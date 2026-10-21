"""Select the SQL parser of a conformance case from its recorded execution profile.

The parser library holds one grammar for each built dialect. A case of corpora v4 and v5
records its profile: release, SQLite source id and compile options. Cases of corpora v1
to v3 record only the source id; the default native library recorded them, with no
grammar options. A case whose profile has no built dialect is not parsed: its verdict
is `MODEL_UNSUPPORTED`, and the parse with another dialect never replaces it.
"""

from pathlib import Path

from belay.sqlite.dialects import ProfileIdentity
from conformance.case_format import Json
from conformance.execution_profile import profile_from_wire, recorded_profile
from conformance.native_library import DEFAULT_ENGINE_VERSION, SOURCE_ID
from conformance.record_versions import PROFILED
from conformance.sql_text import TextParser, Translator, runtime_translator

NO_PARSER_REASON = "no parser for this dialect"
"""The reason of a `MODEL_UNSUPPORTED` case whose recorded profile has no built dialect."""
DEFAULT_NATIVE_PROFILE = ProfileIdentity(DEFAULT_ENGINE_VERSION, SOURCE_ID)
"""The default native library, which records fixtures, generated programs and corpora v1 to v3."""


def default_parser(runtime: Path) -> TextParser:
    """Return the parser of the default native library's dialect."""
    return TextParser.for_profile(runtime_translator(runtime), DEFAULT_NATIVE_PROFILE)


def record_profile(record: dict[str, Json]) -> ProfileIdentity:
    """Return the profile that a native record was recorded with. A subject input has the
    record's profile but no trace, so its clock values cannot be checked here."""
    if record.get("nativeVersion") in PROFILED:
        profile = recorded_profile(record) if "trace" in record else profile_from_wire(record["profile"])
        return ProfileIdentity(profile.engine_version, profile.source_id, profile.compile_options)
    source_id = record.get("sourceId")
    if not isinstance(source_id, str):
        raise ValueError("Native record has no source id")
    return ProfileIdentity(DEFAULT_ENGINE_VERSION, source_id)


def record_parser(translator: Translator, record: dict[str, Json]) -> TextParser:
    """Return the parser of the record's dialect; refuse a record without a built dialect."""
    return TextParser.for_profile(translator, record_profile(record))
