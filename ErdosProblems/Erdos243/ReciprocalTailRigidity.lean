import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Erdős #243: reciprocal-tail rigidity

This module owns the exact centered integer dynamics behind the rational case.
It proves the algebraic defect identity and the well-founded stabilization step:
if the centered errors are eventually nonnegative, the natural tail state is
nonincreasing and the errors eventually vanish.  It also excludes the
scale-normalized constant-negative obstruction `E = -1`, `C₀ = 1`: its
multiplicative denominator state is divisible by `a₀` after the first step,
but at index `a₀ - 1` the centered-state formula makes it congruent to `-1`
modulo `a₀`.

It does not settle the unrestricted problem, whose live obstruction is an
integer centered state that may be negative infinitely often.
-/

namespace ErdosProblems.Erdos243

/-- The Sylvester successor `a² - a + 1`, expressed in a ring. -/
def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

/-- Product-cleared denominator update `Dₙ₊₁ = aₙ Dₙ`. -/
def nextDenState (a D : ℤ) : ℤ :=
  a * D

/-- Product-cleared reciprocal-tail update `Cₙ₊₁ = aₙ Cₙ - Dₙ`. -/
def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D

/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. -/
def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

/-- The next denominator defect from the Sylvester step. -/
def sylvesterDefect (a aNext : ℤ) : ℤ :=
  aNext - sylvesterNext a

/-- The tail update is exactly `Cₙ₊₁ = Cₙ - Eₙ`. -/
theorem nextTailState_eq_sub_centered (a D C : ℤ) :
    nextTailState a D C = C - centeredState a D C := by
  simp [nextTailState, centeredState]
  ring

/-! The entire integer-state system is equivariant under a common scale.  This
removes a large family of duplicate constant-negative-state searches. -/

@[simp] theorem nextDenState_scale (s a D : ℤ) :
    nextDenState a (s * D) = s * nextDenState a D := by
  simp [nextDenState]
  ring

@[simp] theorem nextTailState_scale (s a D C : ℤ) :
    nextTailState a (s * D) (s * C) = s * nextTailState a D C := by
  simp [nextTailState]
  ring

@[simp] theorem centeredState_scale (s a D C : ℤ) :
    centeredState a (s * D) (s * C) = s * centeredState a D C := by
  simp [centeredState]
  ring

/-! ## Excluding the normalized constant-negative orbit

If `Eₙ = -1` and `C₀ = 1`, then `Cₙ = n + 1` and the centered-state
identity becomes

`Dₙ + 1 = (n + 1) (aₙ - 1)`.

On the other hand, `Dₙ₊₁ = aₙ Dₙ` makes every `Dₙ` with `n ≥ 1`
divisible by `a₀`.  Evaluating the displayed identity at `n = a₀ - 1`
would make both `Dₙ` and `Dₙ + 1` divisible by `a₀`, impossible for
`a₀ ≥ 2`.  This consumes the exact multiplicative denominator update above
and closes the normalized branch explored by `FiniteHorizonResidue`.
-/

/-- No infinite natural orbit can simultaneously satisfy the multiplicative
denominator recurrence and the normalized constant-negative shape.

This rules out the `E = -1`, `C₀ = 1` obstruction for every fixed natural
seed.  The general theorem below removes arbitrary common scale and excludes
every constant-negative ratio; variable negative states remain open. -/
theorem no_normalizedConstantNegative_orbit
    (a D : ℕ → ℕ)
    (ha0 : 2 ≤ a 0)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hshape : ∀ n, D n + 1 = (n + 1) * (a n - 1)) :
    False := by
  have ha0_dvd_D_succ : ∀ n, a 0 ∣ D (n + 1) := by
    intro n
    induction n with
    | zero =>
        refine ⟨D 0, ?_⟩
        exact hD 0
    | succ n ih =>
        obtain ⟨k, hk⟩ := ih
        refine ⟨a (n + 1) * k, ?_⟩
        rw [hD (n + 1), hk]
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  let N := a 0 - 1
  have hN : N = (a 0 - 2) + 1 := by
    dsimp [N]
    omega
  have hNsucc : N + 1 = a 0 := by
    dsimp [N]
    omega
  have hdivD : a 0 ∣ D N := by
    rw [hN]
    exact ha0_dvd_D_succ (a 0 - 2)
  have hdivD1 : a 0 ∣ D N + 1 := by
    rw [hshape N, hNsucc]
    exact ⟨a N - 1, rfl⟩
  have hone : a 0 ∣ 1 := (Nat.dvd_add_iff_right hdivD).mpr hdivD1
  have : a 0 = 1 := Nat.dvd_one.mp hone
  omega

/-- No scale-primitive constant-negative natural orbit exists.

Here `m` is the positive magnitude of the constant centered state, `c` is the
initial tail state, and common scaling has been removed by `c.Coprime m`.
The shape equation is exactly what `Eₙ = -m` and `Cₙ = c + n m` impose.

The proof has two arithmetic parts.  First, every `aⱼ` must share a prime
with `m`: otherwise invertibility of `m` modulo `aⱼ` produces a later index
where `aⱼ` divides both `Cₙ` and `Dₙ`, hence divides `m`.  Second, a prime
dividing `m` can occur in at most one `aⱼ`; after its first occurrence the
multiplicative recurrence makes it divide every later `Dₙ`, and the shape
equation forces every later `aₙ` to be `1` modulo that prime.  Pigeonhole on
the finitely many possible prime divisors of `m` gives the contradiction. -/
theorem no_scalePrimitiveConstantNegative_orbit
    (a D : ℕ → ℕ) (m c : ℕ)
    (hm : 0 < m)
    (hcm : c.Coprime m)
    (ha : ∀ n, 2 ≤ a n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hshape : ∀ n, D n + m = (a n - 1) * (c + n * m)) :
    False := by
  have hD_dvd_succ (n : ℕ) : D n ∣ D (n + 1) := by
    refine ⟨a n, ?_⟩
    rw [hD n, Nat.mul_comm]
  have hD_dvd_of_le : ∀ {j k : ℕ}, j ≤ k → D j ∣ D k := by
    intro j k hjk
    induction k, hjk using Nat.le_induction with
    | base => exact dvd_refl _
    | succ k _ ih => exact ih.trans (hD_dvd_succ k)
  have ha_dvd_later : ∀ {j k : ℕ}, j + 1 ≤ k → a j ∣ D k := by
    intro j k hjk
    have haj : a j ∣ D (j + 1) := ⟨D j, hD j⟩
    exact haj.trans (hD_dvd_of_le hjk)
  have hnotCoprime : ∀ j, ¬ (a j).Coprime m := by
    intro j hajm
    letI : NeZero (a j) := ⟨by have := ha j; omega⟩
    let r : ℕ :=
      ((-(c : ZMod (a j))) * (m : ZMod (a j))⁻¹).val
    have hr :
        (r : ZMod (a j)) =
          (-(c : ZMod (a j))) * (m : ZMod (a j))⁻¹ := by
      exact ZMod.natCast_zmod_val _
    have hminv :
        (m : ZMod (a j))⁻¹ * (m : ZMod (a j)) = 1 := by
      simpa [mul_comm] using
        (ZMod.coe_mul_inv_eq_one m hajm.symm)
    have hzero : ((c + r * m : ℕ) : ZMod (a j)) = 0 := by
      push_cast
      rw [hr]
      calc
        (c : ZMod (a j)) +
              (-(c : ZMod (a j)) * (m : ZMod (a j))⁻¹) * m =
            (c : ZMod (a j)) +
              (-(c : ZMod (a j))) *
                ((m : ZMod (a j))⁻¹ * m) := by ring
        _ = 0 := by rw [hminv]; simp
    have hdivBase : a j ∣ c + r * m :=
      (ZMod.natCast_eq_zero_iff (c + r * m) (a j)).mp hzero
    let N := r + (j + 1) * a j
    have hdivC : a j ∣ c + N * m := by
      obtain ⟨q, hq⟩ := hdivBase
      refine ⟨q + (j + 1) * m, ?_⟩
      dsimp [N]
      calc
        c + (r + (j + 1) * a j) * m =
            (c + r * m) + (j + 1) * a j * m := by ring
        _ = a j * q + (j + 1) * a j * m := by rw [hq]
        _ = a j * (q + (j + 1) * m) := by ring
    have hjN : j + 1 ≤ N := by
      have hmul : j + 1 ≤ (j + 1) * a j :=
        Nat.le_mul_of_pos_right (j + 1) (by have := ha j; omega : 0 < a j)
      dsimp [N]
      omega
    have hdivD : a j ∣ D N := ha_dvd_later hjN
    have hdivDm : a j ∣ D N + m := by
      rw [hshape N]
      exact dvd_mul_of_dvd_right hdivC (a N - 1)
    have hdivm : a j ∣ m := (Nat.dvd_add_iff_right hdivD).mpr hdivDm
    have haj1 : a j = 1 :=
      Nat.eq_one_of_dvd_coprimes hajm dvd_rfl hdivm
    have := ha j
    omega
  have hprime_no_repeat :
      ∀ {j k p : ℕ}, j < k → p.Prime → p ∣ m → p ∣ a j → ¬ p ∣ a k := by
    intro j k p hjk hp hpm hpaj hpak
    have hpD : p ∣ D k :=
      hpaj.trans (ha_dvd_later (Nat.succ_le_of_lt hjk))
    have hpDm : p ∣ D k + m := hpD.add hpm
    have hpProd : p ∣ (a k - 1) * (c + k * m) := by
      rw [← hshape k]
      exact hpDm
    have hpC : ¬ p ∣ c + k * m := by
      intro hpc
      have hpkm : p ∣ k * m := dvd_mul_of_dvd_right hpm k
      have hpc' : p ∣ c := (Nat.dvd_add_iff_left hpkm).mpr hpc
      have hp1 : p = 1 :=
        Nat.eq_one_of_dvd_coprimes hcm hpc' hpm
      exact hp.ne_one hp1
    rcases hp.dvd_mul.mp hpProd with hppred | hpC'
    · have hpa_eq : a k - 1 + 1 = a k :=
        Nat.sub_add_cancel (by have := ha k; omega)
      have hp1 : p ∣ 1 := by
        apply (Nat.dvd_add_iff_right hppred).mpr
        simpa [hpa_eq] using hpak
      exact hp.ne_one (Nat.dvd_one.mp hp1)
    · exact hpC hpC'
  let commonPrime (j : ℕ) : ℕ := Nat.minFac (Nat.gcd (a j) m)
  have hcommon_ne_one (j : ℕ) : Nat.gcd (a j) m ≠ 1 := by
    intro h
    exact hnotCoprime j (by simpa [Nat.Coprime] using h)
  have hcommon_prime (j : ℕ) : (commonPrime j).Prime := by
    exact Nat.minFac_prime (hcommon_ne_one j)
  have hcommon_dvd_a (j : ℕ) : commonPrime j ∣ a j := by
    exact (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
  have hcommon_dvd_m (j : ℕ) : commonPrime j ∣ m := by
    exact (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
  have hcommon_le_m (j : ℕ) : commonPrime j ≤ m :=
    Nat.le_of_dvd hm (hcommon_dvd_m j)
  let f : Fin (m + 1) → Fin m := fun j ↦
    ⟨commonPrime j - 1, by
      have hp2 := (hcommon_prime j).two_le
      have hpm := hcommon_le_m j
      omega⟩
  have hf : Function.Injective f := by
    intro j k hjk
    have hval := congrArg Fin.val hjk
    have hpj2 := (hcommon_prime j).two_le
    have hpk2 := (hcommon_prime k).two_le
    have hprimeEq : commonPrime j = commonPrime k := by
      dsimp [f] at hval
      omega
    apply Fin.ext
    have hnotlt : ¬ (j : ℕ) < k := by
      intro hjk'
      apply hprime_no_repeat hjk' (hcommon_prime j)
        (hcommon_dvd_m j) (hcommon_dvd_a j)
      simpa [hprimeEq] using hcommon_dvd_a k
    have hnotgt : ¬ (k : ℕ) < j := by
      intro hkj'
      apply hprime_no_repeat hkj' (hcommon_prime k)
        (hcommon_dvd_m k) (hcommon_dvd_a k)
      simpa [hprimeEq] using hcommon_dvd_a j
    omega
  have := Fin.le_of_injective f hf
  omega

/-- No constant-negative natural orbit exists, at any positive magnitude or
initial tail-state scale.

The common divisor `gcd c m` divides every denominator state by the shape
equation.  Dividing `D`, `c`, and `m` by it produces the scale-primitive orbit
excluded by `no_scalePrimitiveConstantNegative_orbit`. -/
theorem no_constantNegative_orbit
    (a D : ℕ → ℕ) (m c : ℕ)
    (hm : 0 < m)
    (ha : ∀ n, 2 ≤ a n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hshape : ∀ n, D n + m = (a n - 1) * (c + n * m)) :
    False := by
  let g := Nat.gcd c m
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right c hm
  have hgc : g ∣ c := Nat.gcd_dvd_left c m
  have hgm : g ∣ m := Nat.gcd_dvd_right c m
  have hgD : ∀ n, g ∣ D n := by
    intro n
    have hgnm : g ∣ n * m := dvd_mul_of_dvd_right hgm n
    have hgC : g ∣ c + n * m := hgc.add hgnm
    have hgDm : g ∣ D n + m := by
      rw [hshape n]
      exact dvd_mul_of_dvd_right hgC (a n - 1)
    exact (Nat.dvd_add_iff_left hgm).mpr hgDm
  let D' : ℕ → ℕ := fun n ↦ D n / g
  let m' := m / g
  let c' := c / g
  have hm' : 0 < m' :=
    Nat.div_pos (Nat.le_of_dvd hm hgm) hgpos
  have hc'm' : c'.Coprime m' := by
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hD' : ∀ n, D' (n + 1) = a n * D' n := by
    intro n
    dsimp [D']
    rw [hD n]
    exact Nat.mul_div_assoc (a n) (hgD n)
  have hshape' : ∀ n, D' n + m' = (a n - 1) * (c' + n * m') := by
    intro n
    apply Nat.eq_of_mul_eq_mul_left hgpos
    dsimp [D', m', c']
    calc
      g * (D n / g + m / g) = D n + m := by
        rw [Nat.mul_add, Nat.mul_div_cancel' (hgD n),
          Nat.mul_div_cancel' hgm]
      _ = (a n - 1) * (c + n * m) := hshape n
      _ = g * ((a n - 1) * (c / g + n * (m / g))) := by
        have hc_eq : c = g * (c / g) := (Nat.mul_div_cancel' hgc).symm
        have hm_eq : m = g * (m / g) := (Nat.mul_div_cancel' hgm).symm
        have hCscale :
            c + n * m = g * (c / g + n * (m / g)) := by
          calc
            c + n * m = g * (c / g) + n * (g * (m / g)) := by
              calc
                c + n * m = g * (c / g) + n * m :=
                  congrArg (fun x ↦ x + n * m) hc_eq
                _ = g * (c / g) + n * (g * (m / g)) :=
                  congrArg (fun x ↦ g * (c / g) + n * x) hm_eq
            _ = g * (c / g + n * (m / g)) := by ring
        calc
          (a n - 1) * (c + n * m) =
              (a n - 1) * (g * (c / g + n * (m / g))) := by
                exact congrArg (fun x ↦ (a n - 1) * x) hCscale
          _ = g * ((a n - 1) * (c / g + n * (m / g))) := by ring
  exact no_scalePrimitiveConstantNegative_orbit
    a D' m' c' hm' hc'm' ha hD' hshape'

/-- An eventually constant negative centered state is impossible as well:
shift the exact orbit to the first constant-negative index and apply
`no_constantNegative_orbit`. -/
theorem no_eventuallyConstantNegative_orbit
    (a D : ℕ → ℕ) (m c N : ℕ)
    (hm : 0 < m)
    (ha : ∀ n, 2 ≤ a n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hshape : ∀ n,
      D (N + n) + m = (a (N + n) - 1) * (c + n * m)) :
    False := by
  apply no_constantNegative_orbit
    (fun n ↦ a (N + n)) (fun n ↦ D (N + n)) m c hm
  · intro n
    exact ha (N + n)
  · intro n
    simpa only [Nat.add_assoc] using hD (N + n)
  · exact hshape

/-- Exact defect equation from the packet:
`Δₙ Cₙ₊₁ = aₙ² Eₙ - Eₙ₊₁`. -/
theorem sylvesterDefect_mul_nextTailState
    (a aNext D C : ℤ) :
    sylvesterDefect a aNext * nextTailState a D C =
      a ^ 2 * centeredState a D C -
        centeredState aNext (nextDenState a D) (nextTailState a D C) := by
  simp [sylvesterDefect, sylvesterNext, nextTailState, nextDenState,
    centeredState]
  ring

/-- If two consecutive centered errors vanish and the next tail state is
nonzero, the defect identity forces the original denominator sequence to take
the exact Sylvester step. -/
theorem sylvesterNext_eq_of_centered_zero
    (a aNext D C : ℤ)
    (hCnext : nextTailState a D C ≠ 0)
    (hE : centeredState a D C = 0)
    (hEnext :
      centeredState aNext (nextDenState a D) (nextTailState a D C) = 0) :
    aNext = sylvesterNext a := by
  have hdefect := sylvesterDefect_mul_nextTailState a aNext D C
  rw [hE, hEnext] at hdefect
  simp only [mul_zero, sub_zero] at hdefect
  have hzero : sylvesterDefect a aNext = 0 :=
    (mul_eq_zero.mp hdefect).resolve_right hCnext
  rw [sylvesterDefect] at hzero
  exact sub_eq_zero.mp hzero

/-- Along an exact product-cleared tail orbit, eventual vanishing of the
centered state and eventual nonvanishing of the next tail force the exact
Sylvester recurrence from some index onward. -/
theorem sylvesterNext_eventually_of_centered_zero
    (a D C : ℕ → ℤ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC : ∀ n, C (n + 1) = nextTailState (a n) (D n) (C n))
    (hE : ∃ N, ∀ n, N ≤ n → centeredState (a n) (D n) (C n) = 0)
    (hCne : ∃ N, ∀ n, N ≤ n → C (n + 1) ≠ 0) :
    ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n) := by
  obtain ⟨NE, hE⟩ := hE
  obtain ⟨NC, hCne⟩ := hCne
  refine ⟨max NE NC, fun n hn ↦ ?_⟩
  have hnE : NE ≤ n := (Nat.le_max_left NE NC).trans hn
  have hnC : NC ≤ n := (Nat.le_max_right NE NC).trans hn
  apply sylvesterNext_eq_of_centered_zero (a n) (a (n + 1)) (D n) (C n)
  · rw [← hC n]
    exact hCne n hnC
  · exact hE n hnE
  · rw [← hD n, ← hC n]
    exact hE (n + 1) (hnE.trans (Nat.le_succ n))

/-- Every nonincreasing sequence of naturals is eventually constant. -/
theorem antitone_nat_eventually_constant
    (C : ℕ → ℕ) (hstep : ∀ n, C (n + 1) ≤ C n) :
    ∃ N, ∀ n, N ≤ n → C n = C N := by
  classical
  let P : ℕ → Prop := fun m => ∃ n, C n = m
  have hP : ∃ m, P m := ⟨C 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hP
  have hanti : Antitone C := antitone_nat_of_succ_le hstep
  refine ⟨N, fun n hn => ?_⟩
  have hle : C n ≤ C N := hanti hn
  have hmin : C N ≤ C n := by
    rw [hN]
    exact Nat.find_min' hP ⟨n, rfl⟩
  exact Nat.le_antisymm hle hmin

/-- The positive-integer stabilization step used by every one-sided #243
criterion.  If `Cₙ₊₁ + Eₙ = Cₙ`, then the nonnegative errors vanish
eventually. -/
theorem centeredState_eventually_zero
    (C E : ℕ → ℕ) (hrec : ∀ n, C (n + 1) + E n = C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  have hstep : ∀ n, C (n + 1) ≤ C n := fun n => by
    have := hrec n
    omega
  obtain ⟨N, hconst⟩ := antitone_nat_eventually_constant C hstep
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : N ≤ n + 1 := hn.trans (Nat.le_succ n)
  have hsame : C (n + 1) = C n :=
    (hconst (n + 1) hn1).trans (hconst n hn).symm
  have := hrec n
  omega

end ErdosProblems.Erdos243
