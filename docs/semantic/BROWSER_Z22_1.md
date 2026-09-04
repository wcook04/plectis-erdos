# Z22_1: Bit-level remainder identities and scoped bad-run implication

[All problems and zones](BROWSER.md)

<a id="node-fc7431951eb20fcc"></a>
## bad_run_pins_remainder_conditional

PROVED: badRun_pins_remainder pins the row-N remainder to a short interval when every row from N+1 through 3N+2 is bad and the terminal ceiling hypothesis holds.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The premise needs at least twelve consecutive bad rows in the relevant range; the audit found a maximum run of three in the measured data. The theorem therefore supplies no observed case.

Open hypotheses: ["hbad: every row from N+1 through 3N+2 fails LargestSkipLateAt", "hceil: ObeysRemainderCeiling (3N+2)"]

- Lean declaration: [badRun_pins_remainder](../../ErdosProblems/Bit/R2.lean#L443)


