# Native pytest events, pinned because this nixpkgs has no reportlog package.
{ python3Packages, fetchPypi }:
python3Packages.buildPythonPackage {
  pname = "pytest-reportlog";
  version = "1.0.0";
  pyproject = true;
  src = fetchPypi {
    pname = "pytest_reportlog";
    version = "1.0.0";
    sha256 = "75aec3a92bb53456c3e028605a636579d26f31c6f1e035ad9f706c203cfcb74e";
  };
  build-system = [ python3Packages.hatchling python3Packages.hatch-vcs ];
  dependencies = [ python3Packages.pytest ];
  doCheck = false;
  pythonImportsCheck = [ "pytest_reportlog.plugin" ];
}
