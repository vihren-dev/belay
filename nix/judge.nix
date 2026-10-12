# ADR 0011: the locked judge and the verdict. `.github/CODEOWNERS` protects this file and
# nix/judge.lock.json; the verdict job runs `nix-build nix/judge.nix -A verdict`.
#
# Each lock entry is the content-derived store path of one part of the judge: the judge code
# with its claims, each claimed corpus, and the native SQLite oracle with its pinned inputs.
# A content-derived path is computed from the files every time; a fixed-output path with a
# declared hash would reuse an existing store path without reading the files.
{ system ? builtins.currentSystem
, pkgs ? import ../build-support/locked-nixpkgs.nix { inherit system; }
}:
let
  fs = pkgs.lib.fileset;
  root = ../.;
  lock = builtins.fromJSON (builtins.readFile ./judge.lock.json);
  claims = builtins.fromJSON (builtins.readFile ../judge/claims.json);
  part = name: files: "${fs.toSource { inherit root; fileset = fs.unions files; }}";
  parts = {
    judge = part "judge" [ ../judge ];
    oracle = part "oracle" [ ./sqlite.nix ./flake.lock ];
  } // pkgs.lib.mapAttrs' (corpus: entry: {
    name = "corpus ${corpus}";
    value = part corpus [ (root + "/${entry.path}") ];
  }) claims.corpora;
  changed = builtins.filter (name: (lock.${name} or null) != parts.${name}) (builtins.attrNames parts);
  extra = builtins.filter (name: !(parts ? ${name})) (builtins.attrNames lock);
  checked = value:
    if changed == [] && extra == [] then value
    else throw ("the judge changed: ${pkgs.lib.concatStringsSep ", " (changed ++ extra)}"
      + " differs from nix/judge.lock.json. A change to the judge, the claims, a corpus or the"
      + " oracle needs the owner's approval: update nix/judge.lock.json in its own pull request"
      + " (just judge-lock prints the new values).");
  sources = fs.toSource { inherit root; fileset = fs.unions ([ ../judge ] ++ map (entry: root + "/${entry.path}") (builtins.attrValues claims.corpora)); };
  # The subject: the frontend, the model and its predict command, built from the same commit.
  build = import ../build-support/default.nix { inherit system pkgs; };
  subjectSources = fs.toSource { inherit root; fileset = fs.unions [ ../belay (fs.fileFilter (file: file.hasExt "py") ../conformance) ]; };
in {
  # The current values, for `just judge-lock`; reading them does not check the lock.
  current = parts;
  # The lock check alone, without building the subject.
  locked = checked true;
  # The verdict: the locked judge applied to the subject's predictions, in the Nix sandbox.
  verdict = checked (pkgs.runCommand "sqlite-verifier-verdict" { nativeBuildInputs = [ pkgs.python3 ]; } ''
    mkdir -p "$out"
    cd ${sources}
    # Only the subject gets the subject's sources on its import path.
    python3 -m judge --root . --claims judge/claims.json --report "$out/report.json" \
      -- env PYTHONPATH=${subjectSources} python3 -m conformance.predict --runtime ${build.conformance} \
      > "$out/counts.json"
    cat "$out/counts.json"
  '');
}
