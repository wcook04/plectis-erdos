# Erdős #1049: exact rectangular Hermite--Padé threshold no-go

For the explicit rectangular exponent model

```text
decay  = (1 + rho^2)/2 + sigma,
height = (1 + rho)^2/2 + sigma(1 + rho),
saving = 3 sigma^2/pi^2,
```

the compared family proves the exact cleared-gap expansion, its
nonpositivity on `rho >= 0`, `sigma >= 1 + rho`, and the sharp conclusion

```text
hpThreshold rho sigma <= 1/2 - 1/pi^2,
```

with equality if and only if `(rho,sigma)=(0,1)`.  This is a genuine method
boundary for this exponent model, not a universal impossibility theorem and
not a solution of Erdős #1049.

`Challenge.lean` is Mathlib-only.  `Solution.lean` transports the exact
source-current declarations.  The deliberate negative changes the equality
endpoint and must be rejected by Comparator.
