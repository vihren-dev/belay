"""A two-path subject for verifying this experiment's coverage attribution."""


def classify(value: int) -> str:
    """Give the probe distinct executed lines for positive and nonpositive inputs."""
    if value > 0:
        return "positive"
    return "nonpositive"


def child_only() -> str:
    """Expose a line reached only from a Python subprocess."""
    return "child-only"
