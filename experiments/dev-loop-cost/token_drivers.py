"""Measure what drives the token cost of a Claude Code development session.

The owner asked which changes would lower the token use of model development. This
script reads one session transcript (JSON lines) and prints aggregate numbers only:
the context size of each API request, the effect of compactions, which tool calls
add the most tokens to the context and how long those tokens stay there, and the
cost of the same requests if the session had started fresh at each user prompt.

Usage: python3 -I token_drivers.py TRANSCRIPT.jsonl [SUBAGENT_DIR]
"""

from __future__ import annotations

import statistics
import sys
from dataclasses import dataclass, field
from pathlib import Path

# `python3 -I` leaves the script's directory off the import path.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from transcript_reading import Session, read_session, usage_totals

# Price weights relative to one uncached input token (Anthropic list prices:
# cache read 0.1x, 1-hour cache write 2x, output 5x).
WEIGHT_CACHE_READ = 0.1
WEIGHT_CACHE_WRITE = 2.0
WEIGHT_OUTPUT = 5.0

COMPACTION_DROP_TOKENS = 20_000
"""A context that is this much smaller than the one before it shows a compaction, not
an ordinary request: no single request removes this many tokens otherwise."""


@dataclass
class ToolCost:
    """Tokens that the results of one tool category added, and how long they stayed."""
    calls: int = 0
    result_tokens: int = 0
    resident_tokens: int = 0  # result tokens times the later requests that re-read them
    seconds: list[float] = field(default_factory=list)


def weighted(cache_read: int, cache_write: int, output: int, uncached: int) -> float:
    """Return the cost in uncached-input-token equivalents."""
    return cache_read * WEIGHT_CACHE_READ + cache_write * WEIGHT_CACHE_WRITE + output * WEIGHT_OUTPUT + uncached


def next_compaction(compactions: list[int], index: int, end: int) -> int:
    """Return the index of the first request after the next compaction, or the end."""
    return next((c for c in compactions if c > index), end)


def tool_costs(session: Session) -> dict[str, ToolCost]:
    """Return the tokens and resident tokens of each tool category."""
    costs: dict[str, ToolCost] = {}
    end = len(session.requests)
    for category, tokens, index, seconds in session.results:
        cost = costs.setdefault(category, ToolCost())
        cost.calls += 1
        cost.result_tokens += tokens
        cost.resident_tokens += tokens * (next_compaction(session.compactions, index, end) - index)
        cost.seconds.append(seconds)
    return costs


def simulated_cache_read(session: Session, base: int, min_prompt_tokens: int) -> int:
    """Return the context tokens of all requests if each prompt of at least
    min_prompt_tokens had started a new session of base tokens. A compaction inside a
    task keeps its real, smaller context."""
    starts = {index: tokens for index, tokens in session.prompts if tokens >= min_prompt_tokens}
    anchor_real, anchor_sim, total = 0, 0, 0
    for request in session.requests:
        if request.index in starts:
            anchor_real, anchor_sim = request.context, base + starts[request.index]
        elif request.context < anchor_real - COMPACTION_DROP_TOKENS:
            anchor_real, anchor_sim = request.context, min(request.context, anchor_sim)
        simulated = min(request.context, anchor_sim + request.context - anchor_real) if anchor_real else request.context
        total += simulated
    return total


def simulated_compaction(session: Session, threshold: int, summary: int, reread: int) -> int:
    """Return the context tokens of all requests if the session had compacted whenever its
    context reached threshold. Each compaction restarts at summary tokens and costs one
    request at the threshold plus reread tokens, for files that the agent reads again.
    The growth between requests stays as recorded."""
    total, simulated, previous = 0, 0, None
    for request in session.requests:
        growth = request.context - previous if previous is not None and request.context >= previous else None
        simulated = request.context if growth is None and previous is None else (
            min(request.context, summary) if growth is None else simulated + growth)
        if simulated > threshold:
            total += threshold
            simulated = summary + reread + (simulated - threshold)
        total += simulated
        previous = request.context
    return total


def main(arguments: list[str]) -> None:
    """Print the report for one transcript and, optionally, its subagents."""
    session = read_session(Path(arguments[0]))
    requests = session.requests
    contexts = [r.context for r in requests]
    read = sum(r.cache_read for r in requests)
    write = sum(r.cache_write for r in requests)
    output = sum(r.output for r in requests)
    uncached = sum(r.uncached_input for r in requests)
    total_context = sum(contexts)
    print(f"requests {len(requests)}, compactions {len(session.compactions)}, human prompts {len(session.prompts)},"
          f" notification turns {session.notifications}")
    print(f"tokens: cache read {read:,}, cache write {write:,}, output {output:,}, uncached {uncached:,}")
    cost = weighted(read, write, output, uncached)
    print(f"weighted cost (uncached-input equivalents) {cost:,.0f}: cache read {read * WEIGHT_CACHE_READ / cost:.0%},"
          f" cache write {write * WEIGHT_CACHE_WRITE / cost:.0%}, output {output * WEIGHT_OUTPUT / cost:.0%}")
    quantiles = statistics.quantiles(contexts, n=10)
    print(f"context per request: median {statistics.median(contexts):,.0f}, p10 {quantiles[0]:,.0f},"
          f" p90 {quantiles[-1]:,.0f}, max {max(contexts):,}, min {min(contexts):,}")
    starts = [0, *session.compactions, len(requests)]
    segments = [contexts[a:b] for a, b in zip(starts, starts[1:]) if b > a]
    print(f"segments between compactions: median length {statistics.median(len(s) for s in segments):.0f} requests,"
          f" median start {statistics.median(s[0] for s in segments):,.0f}, median end {statistics.median(s[-1] for s in segments):,.0f}")
    print("\ntool category: calls, result tokens, resident tokens (share of all context), median seconds, p90 seconds, total hours")
    for name, c in sorted(tool_costs(session).items(), key=lambda kv: -kv[1].resident_tokens):
        p90 = statistics.quantiles(c.seconds, n=10)[-1] if len(c.seconds) > 1 else c.seconds[0]
        print(f"  {name:16} {c.calls:6} {c.result_tokens:12,} {c.resident_tokens:15,} ({c.resident_tokens / total_context:5.1%})"
              f" {statistics.median(c.seconds):7.1f} {p90:8.1f} {sum(c.seconds) / 3600:7.1f}")
    print("\ntool inputs that the agent wrote: calls, input tokens, resident tokens (share of all context)")
    inputs: dict[str, list[int]] = {}
    for name, tokens, index in session.inputs:
        entry = inputs.setdefault(name, [0, 0, 0])
        entry[0] += 1
        entry[1] += tokens
        entry[2] += tokens * (next_compaction(session.compactions, index, len(requests)) - index)
    for name, (calls, tokens, resident) in sorted(inputs.items(), key=lambda kv: -kv[1][2])[:6]:
        print(f"  {name:16} {calls:6} {tokens:12,} {resident:15,} ({resident / total_context:5.1%})")
    base = int(statistics.quantiles(contexts, n=100)[0])
    print(f"\nsimulated fresh sessions (base context {base:,} tokens = p1 of real contexts):")
    for threshold, label in ((0, "every human prompt"), (50, "prompts of 50+ tokens")):
        simulated = simulated_cache_read(session, base, threshold)
        print(f"  reset at {label}: context tokens {simulated:,} = {simulated / total_context:.0%} of real")
    summary = int(statistics.median(s[0] for s in segments))
    print(f"simulated earlier compaction (summary {summary:,} tokens, 30,000 tokens re-read after each):")
    for threshold in (200_000, 300_000, 500_000):
        simulated = simulated_compaction(session, threshold, summary, 30_000)
        print(f"  compact at {threshold:,}: context tokens {simulated:,} = {simulated / total_context:.0%} of real")
    if len(arguments) > 1:
        sub = [usage_totals(p) for p in sorted(Path(arguments[1]).glob("*.jsonl"))]
        sub_cost = sum(weighted(*t) for t in sub)
        print(f"\nsubagents: {len(sub)} transcripts, weighted cost {sub_cost:,.0f} = {sub_cost / cost:.1%} of the main session")



if __name__ == "__main__":
    main(sys.argv[1:])
