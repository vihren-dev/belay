# Shared entry points. Enter nix develop path:./nix once for a batch of checks.
#
# `timeout --foreground` keeps nix-build in the caller's process group, so a caller that kills
# the group on its deadline (tests/runtime_support.py) stops nix-build too. Nix builds run in
# the Nix daemon, so the children that --foreground leaves alone are not builders. The recipes
# that build test suites use suite_build_limit.

# Seconds for a nix-build of test suites: more than the per-suite limit in
# build-support/tests.nix, so a suite that hangs fails with its own name.
suite_build_limit := "1500"
# Seconds for a nix-build of one mutant suite: more than its limit in build-support/tests.nix.
mutant_build_limit := "3000"
default:
    @just --list

# Resource checks never delete caches or user data.
resources:
    python3 tools/check_resources.py

# Prepare the pinned conformance runtime through the same Nix build that the tests use.
setup: build

# Build the conformance runtime and expose its toolchain, model and programs at the repository root.
build: resources conformance-build
    mkdir -p .lake
    rm -rf .lake/build packages/belay-sqlite-model/.lake/build
    mkdir -p packages/belay-sqlite-model/.lake
    ln -sfn ../build/conformance/.lake/build .lake/build
    ln -sfn ../../../build/conformance/packages/belay-sqlite-model/.lake/build packages/belay-sqlite-model/.lake/build
    ln -sfn build/conformance/lean lean

# Run an explicitly selected scenario without rebuilding its prerequisites.
[positional-arguments]
test-cases *args:
    python3 -m pytest --runtime-root "${SQLITE_VERIFIER_RUNTIME_ROOT:-$PWD}" "$@"

# Build the conformance runtime: the toolchain, the model, the conformance runner and the parser library.
conformance-build:
    mkdir -p build
    timeout --foreground 900 nix-build build-support/default.nix -A conformance --out-link build/conformance --extra-experimental-features 'nix-command flakes'

# Build the checked library reference from an exact source commit, without hosting it.
[positional-arguments]
reference revision: resources
    mkdir -p build
    timeout --foreground 1800 nix-build build-support/default.nix -A apiReference --argstr referenceRevision "$1" --out-link build/api-reference --option sandbox true --option sandbox-fallback false --extra-experimental-features 'nix-command flakes'

# Record live prototype evidence; W3 remains an owner decision after reviewing it.
[positional-arguments]
conformance *args: conformance-build
    timeout 420 python3 -m conformance.pipeline --runtime-root build/conformance --output build/conformance-evidence "$@"

# List selected scenarios without building or executing fixtures.
[positional-arguments]
test-list *args:
    python3 -m pytest --collect-only -q "$@"

# Check pinned tools through the same scenario interface.
smoke:
    timeout --foreground 15 python3 -m pytest tests/test_toolchain_smoke.py --runtime-root "${SQLITE_VERIFIER_RUNTIME_ROOT:-$PWD}"

# Fresh development replay includes every authored/synthetic case and a stable upstream sample.
test: build documentation-inventory test-source
    timeout --foreground {{suite_build_limit}} nix-build build-support/default.nix -A developmentTestReports --out-link build/nix-tests --option sandbox true --option sandbox-fallback false --extra-experimental-features 'nix-command flakes'

# CI runs all full model and historical evidence checks.
test-full: build documentation-inventory test-source
    timeout --foreground {{suite_build_limit}} nix-build build-support/default.nix -A testReports --out-link build/nix-tests-full --option sandbox true --option sandbox-fallback false --extra-experimental-features 'nix-command flakes'

# Check every authored public declaration, constructor and field in the compiled import closure.
documentation-inventory: resources
    mkdir -p build
    timeout --foreground 900 nix-build build-support/default.nix -A publicDocumentation --out-link build/public-documentation --option sandbox true --option sandbox-fallback false --extra-experimental-features 'nix-command flakes'

# Test ownership is shared with Nix; all source-owned checks run on the host.
test-source:
    timeout --foreground 600 python3 -u -m pytest -v tests -m "not requires_nix" --source-checks --runtime-root "${SQLITE_VERIFIER_RUNTIME_ROOT:-$PWD}" --junitxml build/test-results/source.xml

# Review a commit (default: @-) with the other agent tool against docs/review-checklist.md (REVIEWER= overrides).
[positional-arguments]
review *args:
    python3 -m tools.review "$@"

# Record what happened to one review finding: fixed, rejected REASON, or deferred REASON.
[positional-arguments]
review-resolve *args:
    python3 -m tools.review_log "$@"

# Print the current judge lock values (ADR 0011); an owner-approved pull request writes them to integrity/judge.lock.json.
judge-lock:
    nix-instantiate --eval --strict --json integrity/judge.nix -A current | python3 -m json.tool --sort-keys --indent 1

# Count the claimed-corpus cases that each model restriction keeps out of scope.
restriction-costs:
    timeout --foreground 1800 nix-build integrity/judge.nix -A predictions --out-link build/predictions --extra-experimental-features 'nix-command flakes' >&2
    python3 -m conformance.restriction_costs --predictions build/predictions

# Run the locked judge on this commit's subject, as the verdict job does.
verdict:
    timeout --foreground 1800 nix-build integrity/judge.nix -A verdict --out-link build/verdict

# Report per checklist condition how often it fired and what happened to its findings.
[positional-arguments]
review-stats *args:
    python3 -m tools.review_stats "$@"

# Check Nix source identities, test-target commands and environment snapshots.
test-nix:
    timeout --foreground 600 python3 -u -m pytest -v tests -m requires_nix --runtime-root "${SQLITE_VERIFIER_RUNTIME_ROOT:-$PWD}" --junitxml build/test-results/nix.xml

# Run all scheduled suites (tests/nix_scheduled_suites.json), which pull requests skip, also the
# mutant suites that CI runs in their own job.
test-scheduled:
    mkdir -p build
    timeout --foreground {{mutant_build_limit}} nix-build build-support/default.nix -A scheduledTestReports --out-link build/nix-tests-scheduled --option sandbox true --option sandbox-fallback false --extra-experimental-features 'nix-command flakes'

# Run the scheduled suites of the check job: all but the mutant suites (tests/nix_mutant_suites.json).
test-scheduled-checks:
    mkdir -p build
    timeout --foreground {{suite_build_limit}} nix-build build-support/default.nix -A scheduledCheckReports --out-link build/nix-tests-scheduled --option sandbox true --option sandbox-fallback false --extra-experimental-features 'nix-command flakes'

# Run one mutant suite of tests/nix_mutant_suites.json, as its CI job does.
test-mutants suite:
    mkdir -p build/nix-tests-mutants
    timeout --foreground {{mutant_build_limit}} nix-build build-support/default.nix -A "scheduledTests.{{suite}}" --out-link "build/nix-tests-mutants/{{suite}}" --option sandbox true --option sandbox-fallback false --extra-experimental-features 'nix-command flakes'

# Refresh into build/, then review and assign a new corpus version before freezing.
conformance-upstream: conformance-build
    timeout --foreground 900 nix-build build-support/default.nix -A conformanceNative.fixture --out-link build/testfixture --extra-experimental-features 'nix-command flakes'
    timeout --foreground 900 nix-build build-support/default.nix -A conformanceNative.upstream --out-link build/upstream-sqlite --extra-experimental-features 'nix-command flakes'
    timeout 900 python3 -m conformance.upstream_pilot --fixture build/testfixture/bin/testfixture --upstream build/upstream-sqlite --output build/upstream-pilot --pattern 'alter*.test' --pattern 'e_*.test'

# Select native fixture storage explicitly; Linux full replay can opt in to tmpfs.
conformance-corpus temporary_root: conformance-build
    timeout 420 python3 -m conformance.corpus conformance/corpus-v5 --runtime-root build/conformance --native-check --temporary-root {{quote(temporary_root)}} --output build/corpus-progress.json

# The transaction/DML profiling gate is recorded in the W3/W4 status and reports.
conformance-generate: conformance-build
    timeout 120 python3 -m conformance.generate

conformance-mutations: conformance-generate
    timeout 180 python3 -m conformance.mutation_check build/generated/cases.jsonl --output build/generated/mutations.json

conformance-long: conformance-build
    timeout 600 python3 -m conformance.generate --examples 500 --steps 25 --output build/generated-long

# Versioned requirement extraction uses the vendored, release-tagged docsrc archive.
conformance-requirements:
    timeout --foreground 900 nix-build build-support/default.nix -A conformanceDocs --out-link build/conformance-docs --extra-experimental-features 'nix-command flakes'
    python3 -m conformance.requirement_inventory build/conformance-docs/docinfo.db build/requirements-3.51.0.json

# Classify every frozen case without performing fresh native replay.
conformance-progress: conformance-build
    timeout 420 python3 -m conformance.progress --runtime-root build/conformance --output build/corpus-v5-progress.json

# Supply llvm-cov's executable path and a fresh output directory for each measurement.
conformance-coverage llvm_cov output: conformance-generate
    timeout --foreground 900 nix-build build-support/default.nix -A conformanceCoverage --out-link build/model-coverage --extra-experimental-features 'nix-command flakes'
    timeout --foreground 900 nix-build build-support/default.nix -A conformanceNative.coverage --out-link build/native-coverage --extra-experimental-features 'nix-command flakes'
    timeout 300 python3 -m conformance.measure_coverage --llvm-cov {{quote(llvm_cov)}} --output {{quote(output)}}
