# Exact rational rescue inside the minimum-real component

The quintic `Q(z)=-(379/256)z+3z^2-z^5` exactly refutes the composite rule
“minimize `Re Q(c)` and then use an angularly bracketing pair.”  It does not
refute the critical point itself: `TiedNewtonFaceComponentSelector.md` gives a
strict connector through that point for its actual component ends.  The same
four-ended component also has this completely rational noncritical connector.

Take

```text
h=-3/5+9i/10,       R=3/2,
u=(57+176i)/185,    v=(-1431+1040i)/1769.
```

Both `u` and `v` are exact unit vectors.  Their fifth powers have positive real
parts, so their outward tails lie in negative asymptotic sectors.  Convert the
two arm restrictions `Q((1-t)h+tRu)` and `Q((1-t)h+tRv)` to degree-five
Bernstein form.  Convert each tail by `s=R/T` and multiply by `s^5`; this
preserves sign and again gives a degree-five polynomial.  All 24 controls are
strictly negative.  The largest is `-74316957/566080000<-0.13`, so this is not
a numerical near-contact.

The squared arm lengths are exactly

```text
|Ru-h|^2=2601/1850,       |Rv-h|^2=33309/88450.
```

Each distance is below `3/2`, hence their sum is strictly below `3=2R`.
Therefore the two finite arms and both complete outward tails lie in
`{Re Q<0}`, and the central connector has negative metric defect.

Lean checks the unit directions, all four exact Bernstein identities, the
generic nonpositive-control consumer, reciprocal-tail transport, and the
strict length inequality in `TiedNewtonFaceRationalHubRescue.lean`.  The exact
checker reconstructs the controls independently.

Together with the component-selector theorem, this closes the specific model
in two complementary ways: the trace critical point joins its monodromy-selected
ends, while a noncritical rational hub joins a different pair in the same
four-ended component with large margin.  It does not prove the all-degree joint
selector or Erdős #1041.  It shows that trace should select a component; the
final pair and geometric hub may then be critical or noncritical.
