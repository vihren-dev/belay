# A bounded test derivation for observing documented Nix build results and logs.
{ system ? builtins.currentSystem, seed, relevant ? "base", irrelevant ? "base",
  outcome ? "pass" }:
let
  pkgs = import ../../build-support/locked-nixpkgs.nix { inherit system; };
  python = (import ./default.nix { inherit system; }).python;
  subjectInput = pkgs.writeText "observability-relevant-input" relevant;
  selection = { pass = "classify"; fail = "failure"; abrupt = "abrupt_exit"; }.${outcome};
in pkgs.runCommand "observability-${outcome}" {
  nativeBuildInputs = [ python pkgs.coreutils ];
  inherit seed subjectInput;
} ''
  mkdir -p "$out" work
  cp ${./cases.py} work/cases.py
  cp ${./subject.py} work/subject.py
  cp ${./pytest_events.py} work/pytest_events.py
  cd work
  printf '[pytest]\naddopts = -p no:cacheprovider\n' > pytest.ini
  export PYTEST_DISABLE_PLUGIN_AUTOLOAD=1
  export PYTHONPATH="$PWD"
  export PROBE_EVENTS="$TMPDIR/events.jsonl"
  set +e
  timeout 15 python3 -m pytest -c pytest.ini -p pytest_events cases.py \
    -k ${pkgs.lib.escapeShellArg selection} --junitxml "$out/junit.xml"
  status=$?
  set -e
  # A documented builder log carries our own framed records even if the build fails.
  sed 's/^/BELAY_EVENT /' "$PROBE_EVENTS"
  cp "$PROBE_EVENTS" "$out/events.jsonl"
  cp "$subjectInput" "$out/input.txt"
  exit "$status"
''
