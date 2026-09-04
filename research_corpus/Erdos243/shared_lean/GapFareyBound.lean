import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Set

/-!
# Farey-gap denominator bounds for the Erdős #249 window family (N = 1, K)

The wave-17 gap certificate excludes a denominator `q` from representing
`S = ∑ φ(n)/2ⁿ` when

  `(q * V_K) % 2^K + q * (K + 3) < 2^K`

where `V_K` is the committed totient residue
`(∑_{r=1}^{K} φ(1+r)·2^(K-r)) mod 2^K` and `K + 3 = N + K + 2`.

A *failing* `q` is exactly one that pushes a rational `m/q` into the half-open
interval `I_K = [(V'-(K+3))/2^K, V'/2^K)` with `V' = 2^K - V_K`.  Two unimodular
Farey neighbours bracket `I_K`, and the classical mediant lemma forces any
rational inside the gap to have denominator `≥ b + d`.  So every `q ≤ b + d - 1`
satisfies the gap certificate — an elementary per-window proof with no bulk
`decide` and no continued-fraction library.

Rungs in this file (constants generated and cross-verified numerically,
including brute-force confirmation of the pipeline at small `K`):

* `K = 120`: bound `248672326362367909` (~`2.5×10¹⁷`) — replaces
  `totient_gap_check_window_1_120_le_4194304` (the depth-22 brute bound) as the
  feed for the gap wrapper in `CertificateKernel`.
* `K = 240`: bound `79639646646701375323355774875831053` (~`7.96×10³⁴`).

The honest boundary: each rung is a *finite* exclusion.  `sup_K (b + d)(K) = ∞`
would close #249 via `irrational_tsum_totient_div_pow_two_of_gap_certificate_supply`,
but no unboundedness claim is made — that is exactly the untouched analytic core.
-/

namespace GapFareyBound

/-- `qstar` is the exact first displayed denominator at which a gap certificate
fails.  This is the small checker-facing contract emitted by the untrusted
Stern--Brocot producer: all smaller positive denominators pass, while `qstar`
itself fails. -/
def IsFirstGapFailure (V K H qstar : ℕ) : Prop :=
  (∀ q : ℕ, 0 < q → q < qstar → (q * V) % 2 ^ K + q * H < 2 ^ K) ∧
    ¬ ((qstar * V) % 2 ^ K + qstar * H < 2 ^ K)

/-- **Mediant / Farey gap lemma.**  If `a/b < r/s < c/d` (with `b, d > 0`) and the
neighbours are unimodular (`b*c - a*d = 1`), then `b + d ≤ s`.  Elementary:
`s = b·(c·s - r·d) + d·(r·b - a·s)` and both bracketed factors are `≥ 1`. -/
theorem farey_gap {a b c d r s : ℤ}
    (hb : 0 < b) (hd : 0 < d)
    (hdet : b * c - a * d = 1)
    (hleft : a * s < r * b)
    (hright : r * d < c * s) :
    b + d ≤ s := by
  have hX : 1 ≤ c * s - r * d := by linarith
  have hY : 1 ≤ r * b - a * s := by linarith
  have key : b * (c * s - r * d) + d * (r * b - a * s) = s := by
    linear_combination s * hdet
  have h1 : b * 1 ≤ b * (c * s - r * d) := mul_le_mul_of_nonneg_left hX hb.le
  have h2 : d * 1 ≤ d * (r * b - a * s) := mul_le_mul_of_nonneg_left hY hd.le
  linarith [key, h1, h2]

/-! ## Rung `K = 120`: bound `248672326362367909` (~`2.5×10¹⁷`) -/

/-- Unimodularity of the two Farey neighbours: `b*c - a*d = 1`. -/
private lemma det_one :
    (41326538792622579 : ℤ) * 54892391224782222
      - 10940721593428627 * 207345787569745331 = 1 := by norm_num

/-- Left neighbour is strictly below the left endpoint `(V'-123)/2^120`:
`a/b < (V'-123)/2^120`, i.e. `a * 2^120 < (V'-123) * b`. -/
private lemma left_in :
    (10940721593428627 : ℤ) * 2 ^ 120
      < (351897687562210810468098516194744450 - 123) * 41326538792622579 := by
  norm_num

/-- Right endpoint `V'/2^120` is `≤` the right neighbour `c/d`:
`V' * d ≤ c * 2^120`. -/
private lemma right_in :
    (351897687562210810468098516194744450 : ℤ) * 207345787569745331
      ≤ 54892391224782222 * 2 ^ 120 := by
  norm_num

/-- **The bound.**  Every denominator `q` with `0 < q ≤ 248672326362367909`
satisfies the wave-17 gap certificate for the `(N=1, K=120)` window. -/
theorem gap_check_window_1_120_le_248672326362367909
    (q : ℕ) (hq : 0 < q) (hqQ : q ≤ 248672326362367909) :
    (q * 977330308222705062435708544085600126) % 2 ^ 120 + q * 123 < 2 ^ 120 := by
  by_contra hcon
  rw [not_lt] at hcon
  -- division data for A = (q*V) % 2^120, k = (q*V) / 2^120
  set A : ℕ := (q * 977330308222705062435708544085600126) % 2 ^ 120 with hA
  set k : ℕ := (q * 977330308222705062435708544085600126) / 2 ^ 120 with hk
  have hdm : 2 ^ 120 * k + A = q * 977330308222705062435708544085600126 :=
    Nat.div_add_mod _ _
  have hAlt : A < 2 ^ 120 := Nat.mod_lt _ (by positivity)
  -- cast the facts into ℤ
  have hdmZ : (2 : ℤ) ^ 120 * (k : ℤ) + (A : ℤ)
      = (q : ℤ) * 977330308222705062435708544085600126 := by exact_mod_cast hdm
  have hAltZ : (A : ℤ) < 2 ^ 120 := by exact_mod_cast hAlt
  have hconZ : (2 : ℤ) ^ 120 ≤ (A : ℤ) + (q : ℤ) * 123 := by exact_mod_cast hcon
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hP0 : (0 : ℤ) < 2 ^ 120 := by positivity
  -- V + V' = 2^120  ⇒  q*V + q*V' = q*2^120
  have hbridge : (q : ℤ) * 977330308222705062435708544085600126
      + (q : ℤ) * 351897687562210810468098516194744450
      = (q : ℤ) * 2 ^ 120 := by
    rw [← mul_add]; norm_num
  -- interval bounds on r := q - (k+1):  (V'-123)/2^120 ≤ r/q < V'/2^120
  have hIntR : (2 : ℤ) ^ 120 * ((q : ℤ) - ((k : ℤ) + 1))
      < (q : ℤ) * 351897687562210810468098516194744450 := by
    nlinarith [hdmZ, hAltZ, hbridge]
  have hIntL : (q : ℤ) * 351897687562210810468098516194744450 - (q : ℤ) * 123
      ≤ 2 ^ 120 * ((q : ℤ) - ((k : ℤ) + 1)) := by
    nlinarith [hdmZ, hconZ, hbridge]
  have hb0 : (0 : ℤ) < 41326538792622579 := by norm_num
  have hd0 : (0 : ℤ) < 207345787569745331 := by norm_num
  -- Farey precondition (left):  a/b < r/q, cleared through 2^120 > 0
  have hmulL : (2 : ℤ) ^ 120 * (10940721593428627 * (q : ℤ))
      < 2 ^ 120 * (((q : ℤ) - ((k : ℤ) + 1)) * 41326538792622579) := by
    nlinarith [mul_lt_mul_of_pos_right left_in hq0,
      mul_le_mul_of_nonneg_left hIntL hb0.le]
  have hleft : (10940721593428627 : ℤ) * (q : ℤ)
      < ((q : ℤ) - ((k : ℤ) + 1)) * 41326538792622579 :=
    lt_of_mul_lt_mul_left hmulL hP0.le
  -- Farey precondition (right):  r/q < c/d, cleared through 2^120 > 0
  have hmulR : (2 : ℤ) ^ 120 * (((q : ℤ) - ((k : ℤ) + 1)) * 207345787569745331)
      < 2 ^ 120 * (54892391224782222 * (q : ℤ)) := by
    nlinarith [mul_lt_mul_of_pos_right hIntR hd0,
      mul_le_mul_of_nonneg_left right_in hq0.le]
  have hright : ((q : ℤ) - ((k : ℤ) + 1)) * 207345787569745331
      < 54892391224782222 * (q : ℤ) :=
    lt_of_mul_lt_mul_left hmulR hP0.le
  -- mediant lemma forces q ≥ b + d = 248672326362367910
  have hfar := farey_gap hb0 hd0 det_one hleft hright
  have hqQZ : (q : ℤ) ≤ 248672326362367909 := by exact_mod_cast hqQ
  linarith [hfar, hqQZ]

/-- The Farey lower bound at `K = 120` is sharp: the mediant denominator
`248672326362367910` is the exact first displayed denominator for which the
gap certificate fails. -/
theorem gap_check_window_1_120_first_failure :
    IsFirstGapFailure
      977330308222705062435708544085600126
      120 123 248672326362367910 := by
  constructor
  · intro q hq hq_lt
    exact gap_check_window_1_120_le_248672326362367909 q hq (by omega)
  · norm_num [IsFirstGapFailure]

/-! ## Rung `K = 240`: bound `79639646646701375323355774875831053` (~`7.96×10³⁴`;
first failing denominator `79639646646701375323355774875831054 = b + d`) -/

/-- Unimodularity of the `K = 240` Farey neighbours: `b*c - a*d = 1`. -/
private lemma det_one_240 :
    (66013429300517684370587633721421187 : ℤ) * 3607382924184224471122414138260922
      - 17476289389455905704261129876428839 * 13626217346183690952768141154409867 = 1 := by norm_num

/-- Left neighbour is strictly below the left endpoint `(V'-243)/2^240`. -/
private lemma left_in_240 :
    (17476289389455905704261129876428839 : ℤ) * 2 ^ 240
      < (467752257959663993971559469205462307227059981313476726702380679931454872 - 243) * 66013429300517684370587633721421187 := by
  norm_num

/-- Right endpoint `V'/2^240` is `≤` the right neighbour `c/d`. -/
private lemma right_in_240 :
    (467752257959663993971559469205462307227059981313476726702380679931454872 : ℤ) * 13626217346183690952768141154409867
      ≤ 3607382924184224471122414138260922 * 2 ^ 240 := by
  norm_num

/-- **The `K = 240` bound.**  Every denominator `q` with
`0 < q ≤ 79639646646701375323355774875831053` satisfies the gap certificate for the
`(N=1, K=240)` window. -/
theorem gap_check_window_1_240_le_79639646646701375323355774875831053
    (q : ℕ) (hq : 0 < q) (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904) % 2 ^ 240 + q * 243 < 2 ^ 240 := by
  by_contra hcon
  rw [not_lt] at hcon
  set A : ℕ := (q * 1299094806818720335611738031537456208600423915562142231419225521361164904) % 2 ^ 240 with hA
  set k : ℕ := (q * 1299094806818720335611738031537456208600423915562142231419225521361164904) / 2 ^ 240 with hk
  have hdm : 2 ^ 240 * k + A = q * 1299094806818720335611738031537456208600423915562142231419225521361164904 :=
    Nat.div_add_mod _ _
  have hAlt : A < 2 ^ 240 := Nat.mod_lt _ (by positivity)
  have hdmZ : (2 : ℤ) ^ 240 * (k : ℤ) + (A : ℤ)
      = (q : ℤ) * 1299094806818720335611738031537456208600423915562142231419225521361164904 := by exact_mod_cast hdm
  have hAltZ : (A : ℤ) < 2 ^ 240 := by exact_mod_cast hAlt
  have hconZ : (2 : ℤ) ^ 240 ≤ (A : ℤ) + (q : ℤ) * 243 := by exact_mod_cast hcon
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hP0 : (0 : ℤ) < 2 ^ 240 := by positivity
  have hbridge : (q : ℤ) * 1299094806818720335611738031537456208600423915562142231419225521361164904
      + (q : ℤ) * 467752257959663993971559469205462307227059981313476726702380679931454872
      = (q : ℤ) * 2 ^ 240 := by
    rw [← mul_add]; norm_num
  have hIntR : (2 : ℤ) ^ 240 * ((q : ℤ) - ((k : ℤ) + 1))
      < (q : ℤ) * 467752257959663993971559469205462307227059981313476726702380679931454872 := by
    nlinarith [hdmZ, hAltZ, hbridge]
  have hIntL : (q : ℤ) * 467752257959663993971559469205462307227059981313476726702380679931454872 - (q : ℤ) * 243
      ≤ 2 ^ 240 * ((q : ℤ) - ((k : ℤ) + 1)) := by
    nlinarith [hdmZ, hconZ, hbridge]
  have hb0 : (0 : ℤ) < 66013429300517684370587633721421187 := by norm_num
  have hd0 : (0 : ℤ) < 13626217346183690952768141154409867 := by norm_num
  have hmulL : (2 : ℤ) ^ 240 * (17476289389455905704261129876428839 * (q : ℤ))
      < 2 ^ 240 * (((q : ℤ) - ((k : ℤ) + 1)) * 66013429300517684370587633721421187) := by
    nlinarith [mul_lt_mul_of_pos_right left_in_240 hq0,
      mul_le_mul_of_nonneg_left hIntL hb0.le]
  have hleft : (17476289389455905704261129876428839 : ℤ) * (q : ℤ)
      < ((q : ℤ) - ((k : ℤ) + 1)) * 66013429300517684370587633721421187 :=
    lt_of_mul_lt_mul_left hmulL hP0.le
  have hmulR : (2 : ℤ) ^ 240 * (((q : ℤ) - ((k : ℤ) + 1)) * 13626217346183690952768141154409867)
      < 2 ^ 240 * (3607382924184224471122414138260922 * (q : ℤ)) := by
    nlinarith [mul_lt_mul_of_pos_right hIntR hd0,
      mul_le_mul_of_nonneg_left right_in_240 hq0.le]
  have hright : ((q : ℤ) - ((k : ℤ) + 1)) * 13626217346183690952768141154409867
      < 3607382924184224471122414138260922 * (q : ℤ) :=
    lt_of_mul_lt_mul_left hmulR hP0.le
  have hfar := farey_gap hb0 hd0 det_one_240 hleft hright
  have hqQZ : (q : ℤ) ≤ 79639646646701375323355774875831053 := by exact_mod_cast hqQ
  linarith [hfar, hqQZ]

/-- The Farey lower bound at `K = 240` is sharp: the mediant denominator
`79639646646701375323355774875831054` is the exact first displayed denominator
for which the gap certificate fails. -/
theorem gap_check_window_1_240_first_failure :
    IsFirstGapFailure
      1299094806818720335611738031537456208600423915562142231419225521361164904
      240 243 79639646646701375323355774875831054 := by
  constructor
  · intro q hq hq_lt
    exact gap_check_window_1_240_le_79639646646701375323355774875831053 q hq (by omega)
  · norm_num [IsFirstGapFailure]

-- Axiom audit: every result must rest only on the foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms farey_gap
#print axioms gap_check_window_1_120_le_248672326362367909
#print axioms gap_check_window_1_120_first_failure
#print axioms gap_check_window_1_240_le_79639646646701375323355774875831053
#print axioms gap_check_window_1_240_first_failure

end GapFareyBound
