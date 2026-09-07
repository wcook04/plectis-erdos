# The 4/9 midpoint seam has logarithmic record geometry

## Result boundary

This note opens a proof target; it does not prove the target.  The existing
`4/9` even-cylinder is still conditional on midpoint-seam exclusion, and
Erdős 257 remains open.

At even rank `n`, write the cylinder endpoint interval as

\[
  [A_n-K_n,A_n].
\]

After removing all common leading binary digits, let `L_n` be its suffix
width.  The existing induction needs

\[
  L_n\le n/2-1,
\]

because then the common prefix contains every proper divisor used by the next
two rows.  A seam failure is therefore an expansion of `L_n` from logarithmic
size to linear size.

## Exact genealogy computation

The companion script replays the same exact cylinder through rank ten million
and cross-checks the full endpoint dynamic program through rank 300.  It also
records every common-prefix strip and every record-width correction word.

The two-step suffix top obeys

\[
  A_{n+2}=4A_n+C_n,
\]

where `C_n` is computed from the selected proper-divisor loads at `n+1` and
`n+2`.  If no common bit is stripped, a boundary offset `x` is trapped by

\[
  x_{n+2}=4x_n+C_n,
  \qquad 0\le x_n\le K_n.
\]

Thus record suffix widths are expanding affine words that remain inside a
linear corridor.  This is the actual state that an analytic proof must
control.

The exact run finds:

- maximum suffix width `46`, at rank `2,287,962`;
- maximum consecutive no-strip run `13`, first at rank `293,604`;
- maximum width immediately after a nonzero strip `23`;
- terminal width `21` at rank `10,000,000`;
- correction range `[-219,2]` on the run.

Most importantly, every audited state satisfies

\[
  \boxed{L_n\le 2\,\operatorname{bitlength}(n)+5}. \tag{1}
\]

The constant `5` is attained at rank `293,604`, where `L_n=43`.  Smaller
constants are therefore exactly falsified; `5` is not merely a padded fit.

The two decisive length-13 correction words are preserved in the receipt.  At
rank `293,604` the word is

```text
-42,-4,-10,-21,-7,-14,-14,-9,-26,-9,-21,-26,-11
```

and at the maximum-width rank `2,287,962` it is

```text
-2,-22,2,-34,-15,-15,-28,-9,-6,-25,-10,-19,-28.
```

These are not generic divisor ceilings: they retain the exact odd/even load
ancestry in the receipt.

## One-way proof target

Prove (1), or any `L_n=O(log n)` bound, for the actual cylinder recurrence.
The displayed bound is at most `n/2-1` for every even `n >= 36`; the existing
checked bases then exclude the midpoint seam at every depth.  The
even-cylinder induction would run forever, compactness would give an infinite
Boolean support of exact value `4/9`, and that support would disprove Erdős
257.

The likely analytic object is dyadic anti-concentration of `A_n`, not a larger
finite audit.  As a heuristic only, the coefficient `2` has the correct
extreme-value scale: there are order `n` opportunities, the interval width is
`K_n` of order `n`, and hitting a boundary at resolution `2^L` has scale
`n^2/2^L`.  Turning that heuristic into deterministic arithmetic control is
the missing theorem.

## Stop and re-entry

Do not extend the horizon merely to obtain another green run.  Re-enter with
an analytic correction-word/anti-concentration lemma, or with a proposed
constant below `5` that the exact genealogy can falsify.

## Reproduction

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_seam_genealogy.py --horizon 10000000 --crosscheck 300
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_seam_genealogy.py --horizon 10000000 --crosscheck 300 --check-receipt state/formal_math/erdos257_period_noncollapse/four_ninths_seam_genealogy_receipt.json
```
