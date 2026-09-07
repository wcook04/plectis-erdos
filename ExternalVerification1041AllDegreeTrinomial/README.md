# Erdős #1041: all-degree monic trinomials

This package compares the short-note Theorem 1 of the Erdős #1041 writeup
(`res:trinomial-all-degree`): every Schur-stable monic trinomial
`z^n + a z^m + b` has radial spokes from the origin to each zero inside
`{|f| < 1}`, so any two zeros are joined through the origin by a broken
line of length strictly less than two.

The Challenge imports only Mathlib. The Solution is an exact transport of
`ErdosProblems.Erdos1041.AbelControlPolygon.trinomial_erdos1041_conclusion`.
Both Comparator configs enable NanoDa and permit exactly `propext`,
`Quot.sound`, and `Classical.choice`.

This is a Palomar candidate for the writeup lead. It does not solve
unrestricted Erdős #1041. It is not a novelty, peer-review, acceptance, or
live-registry submission claim.
