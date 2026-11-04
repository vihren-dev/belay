"""Send immutable reportlog observations to ClickHouse with bounded requests and replay IDs."""

from collections.abc import Iterable
import os
from pathlib import Path
import ssl
import sys
from time import monotonic
import urllib.error
import urllib.parse
import urllib.request

from tools.observability_records import diagnostic, encode, events, execution
from tools.observability_spool import lock, spool

BATCH_BYTES = 1024 * 1024
"""A conservative request size; oversized single records remain available for diagnosis."""


class NoRedirect(urllib.request.HTTPRedirectHandler):
    """Never forward database authentication to a redirect destination."""

    def redirect_request(self, req: urllib.request.Request, fp: object, code: int,
                         msg: str, headers: object, newurl: str) -> None:
        """Treat redirects as delivery errors instead of changing the authenticated host."""
        return None


def insert(table: str, rows: Iterable[dict[str, object]], deadline: float) -> None:
    """Send synchronous JSONEachRow batches; confirm status and an empty insert response."""
    endpoint = os.environ["BELAY_CLICKHOUSE_URL"]
    parsed = urllib.parse.urlsplit(endpoint)
    if (parsed.scheme not in {"http", "https"} or not parsed.hostname or parsed.username
            or parsed.password or parsed.query or parsed.fragment):
        raise ValueError("BELAY_CLICKHOUSE_URL must be an HTTP(S) endpoint without credentials or query")
    if parsed.scheme != "https" and parsed.hostname not in {"localhost", "127.0.0.1", "::1"}:
        raise ValueError("non-loopback ClickHouse endpoints require HTTPS")
    query = urllib.parse.urlencode({"query": f"INSERT INTO belay_observability.{table} FORMAT JSONEachRow",
                                  "wait_end_of_query": "1", "async_insert": "0"})
    context = ssl.create_default_context(cafile=os.environ.get("BELAY_CLICKHOUSE_CA"))
    opener = urllib.request.build_opener(NoRedirect(), urllib.request.HTTPSHandler(context=context))

    def send(body: bytes) -> None:
        """Bound each request by both the remaining worker budget and its request timeout."""
        remaining = deadline - monotonic()
        if remaining <= 0:
            raise TimeoutError("upload deadline reached")
        request = urllib.request.Request(endpoint + "?" + query, data=body, method="POST", headers={
            "Content-Type": "application/x-ndjson",
            "X-ClickHouse-User": os.environ.get("BELAY_CLICKHOUSE_USER", "default"),
            "X-ClickHouse-Key": os.environ.get("BELAY_CLICKHOUSE_PASSWORD", ""),
        })
        with opener.open(request, timeout=min(3.0, remaining)) as response:
            if response.status != 200 or response.read(65536).strip():
                raise ValueError("ClickHouse did not confirm an empty successful insert response")

    batch = bytearray()
    for row in rows:
        data = (encode(row) + "\n").encode()
        if len(data) > BATCH_BYTES:
            raise ValueError("row exceeds the 1 MiB upload limit; retained for diagnosis")
        if batch and len(batch) + len(data) > BATCH_BYTES:
            send(bytes(batch))
            batch.clear()
        batch.extend(data)
    if batch:
        send(bytes(batch))


def upload_pending(directory: Path) -> bool:
    """Retry unlocked sessions; leave malformed or unacknowledged observations unchanged."""
    if not os.environ.get("BELAY_CLICKHOUSE_URL"):
        diagnostic(f"BELAY_CLICKHOUSE_URL is unset; reports retained in {directory}")
        return False
    deadline = monotonic() + 12
    succeeded = True
    for manifest in sorted(directory.glob("*/execution.json")):
        if manifest.parent.name.startswith("."):
            continue
        try:
            with lock(manifest.parent) as held:
                if held is None or (manifest.parent / ".uploaded").exists():
                    continue
                row = execution(manifest.parent)
                identity = str(row["execution_id"])
                # Validate the full log first: malformed complete lines must not be silently dropped.
                for _ in events(manifest.parent, identity):
                    pass
                insert("test_executions", [row], deadline)
                insert("test_events", events(manifest.parent, identity, warn=False), deadline)
                (manifest.parent / ".uploaded").touch()
        except (OSError, ValueError, KeyError, urllib.error.URLError) as error:
            # Do not echo a server response or URL: it can contain credentials or captured test data.
            diagnostic(f"{manifest.parent}: delivery failed ({type(error).__name__}); retained for retry")
            succeeded = False
        if monotonic() >= deadline:
            return False
    return succeeded


if __name__ == "__main__":
    sys.exit(0 if upload_pending(Path(sys.argv[1]) if len(sys.argv) > 1 else spool()) else 1)
