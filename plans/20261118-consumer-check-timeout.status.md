# Consumer-size check under load

Created 2026-11-18. [Task](20261118-consumer-check-timeout.task.md).

`CheckConsumerSize.lean` sets the compiled time limit for its two checks.
The Python test documents the sampling defaults and the fixture's time limit.
`test_consumer_size_claim_is_false_and_replays` passed in the Nix
`tests.surfaceChecks` build.
