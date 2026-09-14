# Reproduction records

After `make sources` and `make check`, run:

```sh
python3 experiments/run.py --output /absolute/new/result-directory
```

The directory must not already exist. The runner preserves authored inputs and
their hashes, repository commit and dirty status, executable hash, Lean/Python
environment, commands, exit codes, reports and observed outcomes. It also compiles
`ProofClient.lean`, which uses observation-key injectivity from the proof library
to show that two conforming observations for the same key have equal occurrence
lists. Its axiom report is preserved in the output.

The current ten cases cover JSON and DSL acceptance, absence versus false, typing,
duplicate keys, repetition/uniqueness, binding failure, malformed JSON and unsupported
wire versions. Expectations are explained per case and traced to the hashed profile
and grammar documents. Malformed and binding failures are classified as rejected
inputs, with their precise phase retained in the report. A missing executable is
`not-run`; timeouts, process failures and uninterpretable reports are execution failures.
An unexpected result remains visible and makes the runner fail.

This is the authored-case portion of evaluation. Public Train/EMF Compare bridge
results and performance experiments remain pending. Recorded durations are single
execution measurements, not a comparative performance claim.
