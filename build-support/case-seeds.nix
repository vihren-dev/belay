# One Lake cache seed for each verification case (ADR 0010 section 8).
#
# Cases are the folders under examples/ and tests/cases/ that hold a belay.toml; the
# list comes from the folders, not from this file. Each seed's inputs are only what
# its belay.toml names (the case folder, the contract folder and the schema), so a
# change to one case rebuilds only its seed. A seed's output is the Lake cache folder
# that prepare and verify-bundle filled (build-support/case_seed.py).
{ pkgs, runtime, root ? ../. }:
let
  lib = pkgs.lib;
  fs = lib.fileset;
  caseRoots = [ "examples" "tests/cases" ];
  toolOwned = [ "Generated" ".lake" ".belay" ];
  # Relative folders that hold a belay.toml, below one case root.
  findCases = relative:
    let entries = builtins.readDir (root + "/${relative}");
    in lib.optional (entries ? "belay.toml") relative
      ++ lib.concatLists (lib.mapAttrsToList (name: type:
        if type == "directory" && !(builtins.elem name toolOwned)
        then findCases "${relative}/${name}" else [ ]) entries);
  cases = lib.concatMap (relative:
    lib.optionals (builtins.pathExists (root + "/${relative}")) (findCases relative)) caseRoots;
  caseRoot = case: lib.findFirst (relative: lib.hasPrefix "${relative}/" case) "examples" caseRoots;
  # Regular files of a folder, without the tool-owned parts of a local proofs-project build.
  sources = folder: fs.difference (fs.fileFilter (file: file.type == "regular") folder)
    (fs.unions (map (name: fs.maybeMissing (folder + "/${name}")) toolOwned));
  seed = case:
    let
      folder = root + "/${case}";
      project = (builtins.fromTOML (builtins.readFile (folder + "/belay.toml"))).project;
      inputs = fs.toSource {
        inherit root;
        fileset = fs.unions [ (sources folder) (sources (folder + "/${project.contract}"))
                              (folder + "/${project.schema}") ];
      };
    in pkgs.runCommand "case-seed-${builtins.replaceStrings [ "/" ] [ "-" ] case}" { } ''
      export HOME="$TMPDIR"
      cp -R ${inputs} "$TMPDIR/source"
      chmod -R u+w "$TMPDIR/source"
      mkdir -p "$out"
      "$(cat ${runtime}/python-path)" -I ${./case_seed.py} ${runtime} "$TMPDIR/source/${case}" \
        "$TMPDIR/source/${caseRoot case}" "$out"
    '';
in lib.listToAttrs (map (case: lib.nameValuePair case (seed case)) cases)
