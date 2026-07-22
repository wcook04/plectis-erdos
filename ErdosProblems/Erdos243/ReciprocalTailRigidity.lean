import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

/-!
# Erdős #243: reciprocal-tail rigidity

This module owns the exact centered integer dynamics behind the rational case.
It proves the algebraic defect identity and the well-founded stabilization step:
if the centered errors are eventually nonnegative, the natural tail state is
nonincreasing and the errors eventually vanish.  It excludes both constant
negative centered states and, in the natural tail regime, every positive
eventually periodic negative-state magnitude.  It also proves the arithmetic
core of the stronger bounded-aperiodic route: an exact reduced tail tending to
infinity cannot have bounded upward increments.  That proof combines exact
coprimality, whole-modulus avoidance, a shifted CRT barrier, and first crossing.

It does not settle the unrestricted problem, whose live obstruction is an
integer centered state with cofinally unbounded negative excursions.  The full
bounded-negative-part regime is closed below without a periodicity hypothesis.
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

/-! ## Excluding phase-primitive periodic negative magnitudes

The constant-negative argument has a periodic analogue.  Write `eₙ = -Eₙ`
for a positive negative-state magnitude, so that `Cₙ₊₁ = Cₙ + eₙ` and

`Dₙ + eₙ = (aₙ - 1) Cₙ`.

If a divisor `p` occurs in two distinct multiplier states `aⱼ` and `aₖ`, then
the first occurrence puts `p` into `Dₖ`, while the second occurrence forces
`p ∣ Cₖ₊₁`.  From there `p` divides every later `D`, `C`, and `e`.
When `e` is periodic and `C` has a fixed positive drift over one period, any
prime divisor of that drift propagates back to all phases.  A finite-prime
pigeonhole argument therefore excludes a phase-primitive periodic orbit.
-/

/-- Every multiplier `aⱼ` divides every strictly later denominator state. -/
theorem base_dvd_denState_later
    (a D : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = a n * D n)
    {j k : ℕ} (hjk : j < k) :
    a j ∣ D k := by
  have hDdvd : ∀ n, D n ∣ D (n + 1) := by
    intro n
    rw [hD n]
    exact dvd_mul_left (D n) (a n)
  have htrans : ∀ {u v : ℕ}, u ≤ v → D u ∣ D v := by
    intro u v huv
    exact Nat.le_induction (dvd_refl (D u))
      (fun n _ ih ↦ ih.trans (hDdvd n)) v huv
  have haj : a j ∣ D (j + 1) := by
    rw [hD j]
    exact dvd_mul_right (a j) (D j)
  exact haj.trans (htrans (Nat.succ_le_iff.mpr hjk))

/-- If `p` already divides `D` and also divides the current multiplier, then
the constant-shape equation locks `p` into the next tail state. -/
theorem divisorLocksTailSucc
    (p a D C e Cnext : ℕ)
    (ha : 1 ≤ a)
    (hpD : p ∣ D)
    (hpa : p ∣ a)
    (hshape : D + e = (a - 1) * C)
    (hCnext : Cnext = C + e) :
    p ∣ Cnext := by
  have hpRight : p ∣ a * C := dvd_mul_of_dvd_left hpa C
  have hsumEq : D + (C + e) = a * C := by
    calc
      D + (C + e) = (D + e) + C := by omega
      _ = (a - 1) * C + C := by rw [hshape]
      _ = a * C := by
        calc
          (a - 1) * C + C = ((a - 1) + 1) * C := by
            rw [Nat.add_mul, one_mul]
          _ = a * C := by rw [Nat.sub_add_cancel ha]
  have hpSum : p ∣ D + (C + e) := by
    rw [hsumEq]
    exact hpRight
  have hpCe : p ∣ C + e := (Nat.dvd_add_iff_right hpD).mpr hpSum
  rw [hCnext]
  exact hpCe

/-- Once a divisor is present in both `D` and `C`, the product-cleared orbit
keeps it in every later `D`, `C`, and negative-state magnitude `e`. -/
theorem divisorLock_persists
    (p N : ℕ) (a D C e : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hC : ∀ n, C (n + 1) = C n + e n)
    (hshape : ∀ n, D n + e n = (a n - 1) * C n)
    (hpD : p ∣ D N)
    (hpC : p ∣ C N) :
    ∀ n, N ≤ n → p ∣ D n ∧ p ∣ C n ∧ p ∣ e n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      have hpShape : p ∣ D N + e N := by
        rw [hshape N]
        exact dvd_mul_of_dvd_right hpC (a N - 1)
      have hpE : p ∣ e N := (Nat.dvd_add_iff_right hpD).mpr hpShape
      exact ⟨hpD, hpC, hpE⟩
  | succ n hn ih =>
      obtain ⟨hpDn, hpCn, hpEn⟩ := ih
      have hpDnext : p ∣ D (n + 1) := by
        rw [hD n]
        exact dvd_mul_of_dvd_right hpDn (a n)
      have hpCnext : p ∣ C (n + 1) := by
        rw [hC n]
        exact hpCn.add hpEn
      have hpShape : p ∣ D (n + 1) + e (n + 1) := by
        rw [hshape (n + 1)]
        exact dvd_mul_of_dvd_right hpCnext (a (n + 1) - 1)
      have hpEnext : p ∣ e (n + 1) :=
        (Nat.dvd_add_iff_right hpDnext).mpr hpShape
      exact ⟨hpDnext, hpCnext, hpEnext⟩

/-- A period relation iterates over any natural number of periods. -/
theorem periodic_add_mul
    (x : ℕ → ℕ) (h : ℕ)
    (hperiod : ∀ n, x (n + h) = x n) :
    ∀ n t, x (n + t * h) = x n := by
  intro n t
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        x (n + (t + 1) * h) = x ((n + t * h) + h) := by
          simp only [Nat.add_mul, one_mul, Nat.add_assoc]
        _ = x (n + t * h) := hperiod (n + t * h)
        _ = x n := ih

/-- A fixed phase drift also iterates over any number of periods. -/
theorem phaseDrift_add_mul
    (C : ℕ → ℕ) (h M : ℕ)
    (hphase : ∀ n, C (n + h) = C n + M) :
    ∀ n t, C (n + t * h) = C n + t * M := by
  intro n t
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        C (n + (t + 1) * h) = C ((n + t * h) + h) := by
          simp only [Nat.add_mul, one_mul, Nat.add_assoc]
        _ = C (n + t * h) + M := hphase (n + t * h)
        _ = C n + t * M + M := by rw [ih]
        _ = C n + (t + 1) * M := by
          simp only [Nat.add_mul, one_mul, Nat.add_assoc]

/-- If a divisor of the period drift occurs in two multiplier states, then it
is a common divisor of the initial tail state and every periodic magnitude. -/
theorem repeatedDivisor_forces_periodicCommonScale
    (p j k h M : ℕ) (a D C e : ℕ → ℕ)
    (hh : 0 < h)
    (ha : ∀ n, 1 ≤ a n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hC : ∀ n, C (n + 1) = C n + e n)
    (hshape : ∀ n, D n + e n = (a n - 1) * C n)
    (hperiod : ∀ n, e (n + h) = e n)
    (hphase : ∀ n, C (n + h) = C n + M)
    (hjk : j < k)
    (hpM : p ∣ M)
    (hpaj : p ∣ a j)
    (hpak : p ∣ a k) :
    p ∣ C 0 ∧ ∀ n, p ∣ e n := by
  have hpDk : p ∣ D k :=
    hpaj.trans (base_dvd_denState_later a D hD hjk)
  have hpCnext : p ∣ C (k + 1) :=
    divisorLocksTailSucc p (a k) (D k) (C k) (e k) (C (k + 1))
      (ha k) hpDk hpak (hshape k) (hC k)
  have hpDnext : p ∣ D (k + 1) := by
    rw [hD k]
    exact dvd_mul_of_dvd_right hpDk (a k)
  have hpersist := divisorLock_persists p (k + 1) a D C e
    hD hC hshape hpDnext hpCnext
  have hpEall : ∀ n, p ∣ e n := by
    intro n
    let t := k + 1
    have hlate : k + 1 ≤ n + t * h := by
      dsimp [t]
      have hmul : k + 1 ≤ (k + 1) * h :=
        Nat.le_mul_of_pos_right (k + 1) hh
      omega
    have hpLate : p ∣ e (n + t * h) :=
      (hpersist (n + t * h) hlate).2.2
    rw [periodic_add_mul e h hperiod n t] at hpLate
    exact hpLate
  have hlate0 : k + 1 ≤ (k + 1) * h :=
    Nat.le_mul_of_pos_right (k + 1) hh
  have hpCLate : p ∣ C ((k + 1) * h) :=
    (hpersist ((k + 1) * h) hlate0).2.1
  have hCiterate := phaseDrift_add_mul C h M hphase 0 (k + 1)
  simp only [Nat.zero_add] at hCiterate
  rw [hCiterate] at hpCLate
  have hpDrift : p ∣ (k + 1) * M := dvd_mul_of_dvd_right hpM (k + 1)
  have hpC0 : p ∣ C 0 := (Nat.dvd_add_iff_left hpDrift).mpr hpCLate
  exact ⟨hpC0, hpEall⟩

/-- There is no positive, phase-primitive periodic negative-magnitude orbit.

The explicit hypotheses are the exact arithmetic interface needed by the
argument: `e` is positive and periodic with period `h`, `C` gains the positive
drift `M` over one period, and no prime divisor of `M` is a common scale of
`C₀` and all values of `e`.  The pointwise bound `eₙ < aₙ` is the natural
tail regime in which a multiplier cannot divide its phase magnitude. -/
theorem no_phasePrimitivePeriodicNegative_orbit
    (a D C e : ℕ → ℕ) (h M : ℕ)
    (hh : 0 < h)
    (hM : 0 < M)
    (ha : ∀ n, 2 ≤ a n)
    (hepos : ∀ n, 0 < e n)
    (helt : ∀ n, e n < a n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hC : ∀ n, C (n + 1) = C n + e n)
    (hshape : ∀ n, D n + e n = (a n - 1) * C n)
    (hperiod : ∀ n, e (n + h) = e n)
    (hphase : ∀ n, C (n + h) = C n + M)
    (hprimitive : ∀ p, p.Prime → p ∣ M →
      ¬ (p ∣ C 0 ∧ ∀ n, p ∣ e n)) :
    False := by
  have hnotCoprime : ∀ j, ¬ Nat.Coprime (a j) M := by
    intro j hcop
    letI : NeZero (a j) := ⟨by have := ha j; omega⟩
    let r : ℕ :=
      ((-(C j : ZMod (a j))) * (M : ZMod (a j))⁻¹).val
    let t : ℕ := r + (j + 1) * a j
    let k : ℕ := j + t * h
    have hr :
        (r : ZMod (a j)) =
          (-(C j : ZMod (a j))) * (M : ZMod (a j))⁻¹ := by
      exact ZMod.natCast_zmod_val _
    have hMinv :
        (M : ZMod (a j))⁻¹ * (M : ZMod (a j)) = 1 := by
      simpa [mul_comm] using ZMod.coe_mul_inv_eq_one M hcop.symm
    have hzero : ((C j + r * M : ℕ) : ZMod (a j)) = 0 := by
      push_cast
      rw [hr]
      calc
        (C j : ZMod (a j)) +
              (-(C j : ZMod (a j)) * (M : ZMod (a j))⁻¹) * M =
            (C j : ZMod (a j)) +
              (-(C j : ZMod (a j))) *
                ((M : ZMod (a j))⁻¹ * M) := by ring
        _ = 0 := by rw [hMinv]; simp
    have haj_dvd_base : a j ∣ C j + r * M :=
      (ZMod.natCast_eq_zero_iff (C j + r * M) (a j)).mp hzero
    have haj_dvd_Cphase : a j ∣ C j + t * M := by
      obtain ⟨q, hq⟩ := haj_dvd_base
      refine ⟨q + (j + 1) * M, ?_⟩
      dsimp [t]
      calc
        C j + (r + (j + 1) * a j) * M =
            (C j + r * M) + (j + 1) * a j * M := by ring
        _ = a j * q + (j + 1) * a j * M := by rw [hq]
        _ = a j * (q + (j + 1) * M) := by ring
    have htPos : 0 < t := by
      have htLower : j + 1 ≤ t := by
        have hmul : j + 1 ≤ (j + 1) * a j :=
          Nat.le_mul_of_pos_right (j + 1) (by have := ha j; omega)
        dsimp [t]
        omega
      dsimp [t]
      omega
    have hjk : j < k := by
      dsimp [k]
      have : 0 < t * h := Nat.mul_pos htPos hh
      omega
    have hCk : C k = C j + t * M := by
      dsimp [k]
      exact phaseDrift_add_mul C h M hphase j t
    have haj_dvd_Ck : a j ∣ C k := by
      rw [hCk]
      exact haj_dvd_Cphase
    have haj_dvd_Dk : a j ∣ D k :=
      base_dvd_denState_later a D hD hjk
    have haj_dvd_shape : a j ∣ D k + e k := by
      rw [hshape k]
      exact dvd_mul_of_dvd_right haj_dvd_Ck (a k - 1)
    have haj_dvd_ek : a j ∣ e k :=
      (Nat.dvd_add_iff_right haj_dvd_Dk).mpr haj_dvd_shape
    have hek : e k = e j := by
      dsimp [k]
      exact periodic_add_mul e h hperiod j t
    have haj_dvd_ej : a j ∣ e j := by
      rw [← hek]
      exact haj_dvd_ek
    have haj_le_ej : a j ≤ e j := Nat.le_of_dvd (hepos j) haj_dvd_ej
    exact (not_le_of_gt (helt j)) haj_le_ej
  let commonPrime : ℕ → ℕ := fun j ↦ (Nat.gcd (a j) M).minFac
  have hprime : ∀ j, (commonPrime j).Prime := by
    intro j
    dsimp [commonPrime]
    apply Nat.minFac_prime
    intro hgcd
    apply hnotCoprime j
    rw [Nat.coprime_iff_gcd_eq_one]
    exact hgcd
  have hprime_dvd_a : ∀ j, commonPrime j ∣ a j := by
    intro j
    exact (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
  have hprime_dvd_M : ∀ j, commonPrime j ∣ M := by
    intro j
    exact (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
  have hprime_le_M : ∀ j, commonPrime j ≤ M := by
    intro j
    exact Nat.le_of_dvd hM (hprime_dvd_M j)
  let f : Fin (M + 1) → Fin M := fun j ↦
    ⟨commonPrime j - 1, by
      have hp2 := (hprime j).two_le
      have hpM := hprime_le_M j
      omega⟩
  have hfInjective : Function.Injective f := by
    intro j k hjk
    have hval := congrArg Fin.val hjk
    have hpEq : commonPrime j = commonPrime k := by
      dsimp [f] at hval
      have hpj2 := (hprime j).two_le
      have hpk2 := (hprime k).two_le
      omega
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hjklt | hkjlt
    · have hcommon := repeatedDivisor_forces_periodicCommonScale
        (commonPrime j) j k h M a D C e hh
        (fun n ↦ (ha n).trans' (by omega)) hD hC hshape hperiod hphase
        hjklt (hprime_dvd_M j) (hprime_dvd_a j) (by
          rw [hpEq]
          exact hprime_dvd_a k)
      exact (hprimitive (commonPrime j) (hprime j) (hprime_dvd_M j)) hcommon
    · have hcommon := repeatedDivisor_forces_periodicCommonScale
        (commonPrime k) k j h M a D C e hh
        (fun n ↦ (ha n).trans' (by omega)) hD hC hshape hperiod hphase
        hkjlt (hprime_dvd_M k) (hprime_dvd_a k) (by
          rw [← hpEq]
          exact hprime_dvd_a j)
      exact (hprimitive (commonPrime k) (hprime k) (hprime_dvd_M k)) hcommon
  have hcard := Fintype.card_le_of_injective f hfInjective
  simp only [Fintype.card_fin] at hcard
  omega

/-- No positive periodic negative-magnitude orbit exists, at any common scale.

If the phase-primitive condition fails, a prime divisor of the period drift
divides `C₀` and every magnitude.  The shape equation then makes it divide
every denominator state as well.  Dividing the complete orbit by this prime
preserves all hypotheses and strictly decreases the positive period drift, so
strong induction reduces to the phase-primitive theorem above. -/
theorem no_periodicNegative_orbit
    (a D C e : ℕ → ℕ) (h M : ℕ)
    (hh : 0 < h)
    (hM : 0 < M)
    (ha : ∀ n, 2 ≤ a n)
    (hepos : ∀ n, 0 < e n)
    (helt : ∀ n, e n < a n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hC : ∀ n, C (n + 1) = C n + e n)
    (hshape : ∀ n, D n + e n = (a n - 1) * C n)
    (hperiod : ∀ n, e (n + h) = e n)
    (hphase : ∀ n, C (n + h) = C n + M) :
    False := by
  induction M using Nat.strong_induction_on generalizing D C e with
  | h M ih =>
      by_cases hprimitive : ∀ p, p.Prime → p ∣ M →
          ¬ (p ∣ C 0 ∧ ∀ n, p ∣ e n)
      · exact no_phasePrimitivePeriodicNegative_orbit
          a D C e h M hh hM ha hepos helt hD hC hshape hperiod hphase
          hprimitive
      · push Not at hprimitive
        obtain ⟨p, hpPrime, hpM, hpC0, hpE⟩ := hprimitive
        have hpC : ∀ n, p ∣ C n := by
          intro n
          induction n with
          | zero => exact hpC0
          | succ n ihC =>
              rw [hC n]
              exact ihC.add (hpE n)
        have hpD : ∀ n, p ∣ D n := by
          intro n
          have hpShape : p ∣ D n + e n := by
            rw [hshape n]
            exact dvd_mul_of_dvd_right (hpC n) (a n - 1)
          exact (Nat.dvd_add_iff_left (hpE n)).mpr hpShape
        let D' : ℕ → ℕ := fun n ↦ D n / p
        let C' : ℕ → ℕ := fun n ↦ C n / p
        let e' : ℕ → ℕ := fun n ↦ e n / p
        let M' : ℕ := M / p
        have hpPos : 0 < p := hpPrime.pos
        have hM' : 0 < M' := by
          dsimp [M']
          exact Nat.div_pos (Nat.le_of_dvd hM hpM) hpPos
        have hM'lt : M' < M := by
          dsimp [M']
          exact Nat.div_lt_self hM hpPrime.one_lt
        have hepos' : ∀ n, 0 < e' n := by
          intro n
          dsimp [e']
          exact Nat.div_pos (Nat.le_of_dvd (hepos n) (hpE n)) hpPos
        have helt' : ∀ n, e' n < a n := by
          intro n
          exact (Nat.div_le_self (e n) p).trans_lt (helt n)
        have hD' : ∀ n, D' (n + 1) = a n * D' n := by
          intro n
          dsimp [D']
          rw [hD n]
          exact Nat.mul_div_assoc (a n) (hpD n)
        have hC' : ∀ n, C' (n + 1) = C' n + e' n := by
          intro n
          apply Nat.eq_of_mul_eq_mul_left hpPos
          dsimp [C', e']
          calc
            p * (C (n + 1) / p) = C (n + 1) :=
              Nat.mul_div_cancel' (hpC (n + 1))
            _ = C n + e n := hC n
            _ = p * (C n / p + e n / p) := by
              rw [Nat.mul_add, Nat.mul_div_cancel' (hpC n),
                Nat.mul_div_cancel' (hpE n)]
        have hshape' : ∀ n, D' n + e' n = (a n - 1) * C' n := by
          intro n
          apply Nat.eq_of_mul_eq_mul_left hpPos
          dsimp [D', C', e']
          calc
            p * (D n / p + e n / p) = D n + e n := by
              rw [Nat.mul_add, Nat.mul_div_cancel' (hpD n),
                Nat.mul_div_cancel' (hpE n)]
            _ = (a n - 1) * C n := hshape n
            _ = p * ((a n - 1) * (C n / p)) := by
              have hcEq : C n = p * (C n / p) :=
                (Nat.mul_div_cancel' (hpC n)).symm
              calc
                (a n - 1) * C n = (a n - 1) * (p * (C n / p)) := by
                  exact congrArg (fun x ↦ (a n - 1) * x) hcEq
                _ = p * ((a n - 1) * (C n / p)) := by ring
        have hperiod' : ∀ n, e' (n + h) = e' n := by
          intro n
          dsimp [e']
          rw [hperiod n]
        have hphase' : ∀ n, C' (n + h) = C' n + M' := by
          intro n
          apply Nat.eq_of_mul_eq_mul_left hpPos
          dsimp [C', M']
          calc
            p * (C (n + h) / p) = C (n + h) :=
              Nat.mul_div_cancel' (hpC (n + h))
            _ = C n + M := hphase n
            _ = p * (C n / p + M / p) := by
              rw [Nat.mul_add, Nat.mul_div_cancel' (hpC n),
                Nat.mul_div_cancel' hpM]
        exact ih M' hM'lt D' C' e' hM' hepos' helt' hD' hC' hshape'
          hperiod' hphase'

/-- An eventually periodic negative-magnitude tail is impossible in the same
natural regime: shift to the first periodic index and apply
`no_periodicNegative_orbit`. -/
theorem no_eventuallyPeriodicNegative_orbit
    (a D C e : ℕ → ℕ) (N h M : ℕ)
    (hh : 0 < h)
    (hM : 0 < M)
    (ha : ∀ n, 2 ≤ a n)
    (hepos : ∀ n, 0 < e (N + n))
    (helt : ∀ n, e (N + n) < a (N + n))
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hC : ∀ n, C (n + 1) = C n + e n)
    (hshape : ∀ n, D n + e n = (a n - 1) * C n)
    (hperiod : ∀ n, e (N + n + h) = e (N + n))
    (hphase : ∀ n, C (N + n + h) = C (N + n) + M) :
    False := by
  apply no_periodicNegative_orbit
    (fun n ↦ a (N + n)) (fun n ↦ D (N + n))
    (fun n ↦ C (N + n)) (fun n ↦ e (N + n)) h M
    hh hM (fun n ↦ ha (N + n)) hepos helt
  · intro n
    simpa only [Nat.add_assoc] using hD (N + n)
  · intro n
    simpa only [Nat.add_assoc] using hC (N + n)
  · intro n
    exact hshape (N + n)
  · intro n
    simpa only [Nat.add_assoc] using hperiod n
  · intro n
    simpa only [Nat.add_assoc] using hphase n

/-! ## The bounded aperiodic route: a CRT barrier

Periodicity is not needed once the reduced exact tail supplies infinitely many
pairwise-coprime moduli which every later numerator must avoid.  The finite
producer below places a consecutive forbidden block past any prescribed
height. -/

/-- Pairwise-coprime moduli can be assigned to consecutive integers, and the
resulting block can be shifted beyond any prescribed lower bound. -/
theorem exists_shifted_consecutiveMultiples
    {k : ℕ}
    (m : Fin k → ℕ)
    (hm : ∀ i, 1 < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (L : ℕ) :
    ∃ x, L < x ∧ ∀ i : Fin k, m i ∣ x + i.1 := by
  classical
  let residue : Fin k → ℕ := fun i ↦ m i - i.1 % m i
  have hm0 : ∀ i ∈ (Finset.univ : Finset (Fin k)), m i ≠ 0 := by
    intro i _
    have := hm i
    omega
  have hpairSet : Set.Pairwise
      (↑(Finset.univ : Finset (Fin k)) : Set (Fin k))
      (fun i j ↦ Nat.Coprime (m i) (m j)) := by
    intro i _ j _ hij
    exact hpair i j hij
  let y := Nat.chineseRemainderOfFinset residue m Finset.univ hm0 hpairSet
  let P := ∏ i : Fin k, m i
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun i _ ↦ by have := hm i; omega
  let x := (y : ℕ) + (L + 1) * P
  have hLx : L < x := by
    have hmul : L + 1 ≤ (L + 1) * P :=
      Nat.le_mul_of_pos_right (L + 1) hPpos
    dsimp [x]
    omega
  refine ⟨x, hLx, fun i ↦ ?_⟩
  have hy : (y : ℕ) ≡ residue i [MOD m i] :=
    y.property i (Finset.mem_univ i)
  have hremLt : i.1 % m i < m i := Nat.mod_lt _ (by have := hm i; omega)
  have hresidueDvd : m i ∣ residue i + i.1 := by
    refine ⟨i.1 / m i + 1, ?_⟩
    dsimp [residue]
    calc
      m i - i.1 % m i + i.1 =
          m i - i.1 % m i + (i.1 % m i + m i * (i.1 / m i)) := by
            rw [Nat.mod_add_div]
      _ = m i + m i * (i.1 / m i) := by omega
      _ = m i * (i.1 / m i + 1) := by ring
  have hyDvd : m i ∣ (y : ℕ) + i.1 := by
    apply Nat.modEq_zero_iff_dvd.mp
    exact (hy.add_right i.1).trans
      (Nat.modEq_zero_iff_dvd.mpr hresidueDvd)
  have hmP : m i ∣ P := by
    dsimp [P]
    simpa using Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have hmShift : m i ∣ (L + 1) * P :=
    dvd_mul_of_dvd_right hmP (L + 1)
  obtain ⟨q, hq⟩ := hyDvd
  obtain ⟨r, hr⟩ := hmShift
  refine ⟨q + r, ?_⟩
  dsimp [x]
  calc
    (y : ℕ) + (L + 1) * P + i.1 =
        ((y : ℕ) + i.1) + (L + 1) * P := by omega
    _ = m i * q + m i * r := by rw [hq, hr]
    _ = m i * (q + r) := by ring

/-- A sequence tending to infinity cannot have uniformly bounded upward
increments while permanently avoiding infinitely many fresh pairwise-coprime
moduli. -/
theorem no_boundedRise_of_tailAvoidance
    (u m : ℕ → ℕ) (N B : ℕ)
    (hB : 0 < B)
    (hm : ∀ n, N ≤ n → 1 < m n)
    (hpair : ∀ {i j : ℕ}, N ≤ i → N ≤ j → i ≠ j →
      Nat.Coprime (m i) (m j))
    (havoid : ∀ {i t : ℕ}, N ≤ i → i < t →
      Nat.Coprime (m i) (u t))
    (hrise : ∀ n, N ≤ n → u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  let selected : Fin B → ℕ := fun i ↦ m (N + i.1)
  have hselected : ∀ i, 1 < selected i := by
    intro i
    exact hm (N + i.1) (by omega)
  have hselectedPair : ∀ i j, i ≠ j →
      Nat.Coprime (selected i) (selected j) := by
    intro i j hij
    apply hpair (by omega) (by omega)
    intro hindex
    apply hij
    apply Fin.ext
    omega
  let T := N + B
  obtain ⟨x, hxT, hxDiv⟩ :=
    exists_shifted_consecutiveMultiples selected hselected hselectedPair (u T)
  have hforbidden : ∀ t, T ≤ t →
      ¬ (x ≤ u t ∧ u t < x + B) := by
    intro t ht ⟨hxu, huTopBlock⟩
    let rNat := u t - x
    have hrLt : rNat < B := by
      dsimp [rNat]
      omega
    let r : Fin B := ⟨rNat, hrLt⟩
    have hxr : x + r.1 = u t := by
      dsimp [r, rNat]
      omega
    have hmodDvd : m (N + r.1) ∣ u t := by
      rw [← hxr]
      exact hxDiv r
    have hindexLt : N + r.1 < t := by
      dsimp [T] at ht
      have hr := r.2
      omega
    have hcop : Nat.Coprime (m (N + r.1)) (u t) :=
      havoid (by omega) hindexLt
    have hone : m (N + r.1) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hmodDvd
    have hmgt := hm (N + r.1) (by omega)
    omega
  obtain ⟨K, hK⟩ := (Filter.tendsto_atTop_atTop.mp huTop) (x + B)
  let t0 := max K (T + 1)
  have ht0T : T < t0 := by
    dsimp [t0]
    exact lt_of_lt_of_le (Nat.lt_succ_self T) (le_max_right K (T + 1))
  have hu0 : x + B ≤ u t0 := hK t0 (le_max_left K (T + 1))
  let P : ℕ → Prop := fun t ↦ T < t ∧ x + B ≤ u t
  have hP : ∃ t, P t := ⟨t0, ht0T, hu0⟩
  let t := Nat.find hP
  have htP : P t := Nat.find_spec hP
  have htPrev : T ≤ t - 1 := by
    dsimp [P] at htP
    omega
  have htSucc : t - 1 + 1 = t := by
    dsimp [P] at htP
    omega
  have huPrevTop : u (t - 1) < x + B := by
    by_contra hnot
    have hge : x + B ≤ u (t - 1) := by omega
    by_cases heq : t - 1 = T
    · rw [heq] at hge
      omega
    · have hTlt : T < t - 1 := by omega
      have hmin : t ≤ t - 1 := Nat.find_min' hP ⟨hTlt, hge⟩
      omega
  have huPrevBelow : u (t - 1) < x := by
    by_contra hnot
    have hxle : x ≤ u (t - 1) := by omega
    exact hforbidden (t - 1) htPrev ⟨hxle, huPrevTop⟩
  have hRise := hrise (t - 1) (le_trans (by omega) htPrev)
  rw [htSucc] at hRise
  dsimp [P] at htP
  omega

/-- At one reduced exact step, the current multiplier is coprime to the
accumulated denominator state. -/
theorem reducedStep_coprime_currentFactor
    {a u v uNext vNext : ℕ}
    (hredNext : Nat.Coprime uNext vNext)
    (hu : uNext + v = a * u)
    (hv : vNext = a * v) :
    Nat.Coprime a v := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let d := Nat.gcd a v
  have hdA : d ∣ a := Nat.gcd_dvd_left a v
  have hdV : d ∣ v := Nat.gcd_dvd_right a v
  have hdUadd : d ∣ uNext + v := by
    rw [hu]
    exact dvd_mul_of_dvd_left hdA u
  have hdU : d ∣ uNext := (Nat.dvd_add_iff_left hdV).mpr hdUadd
  have hdVnext : d ∣ vNext := by
    rw [hv]
    exact dvd_mul_of_dvd_left hdA v
  have hdOne : d ∣ 1 := by
    have hdGcd : d ∣ Nat.gcd uNext vNext := Nat.dvd_gcd hdU hdVnext
    have hGcdEq : Nat.gcd uNext vNext = 1 := by
      simpa [Nat.Coprime] using hredNext
    rw [hGcdEq] at hdGcd
    exact hdGcd
  exact Nat.dvd_one.mp hdOne

/-- Multipliers at distinct indices of a reduced exact tail are pairwise
coprime. -/
theorem reducedTail_pairwiseCoprime
    (a u v : ℕ → ℕ)
    (hred : ∀ n, Nat.Coprime (u n) (v n))
    (hu : ∀ n, u (n + 1) + v n = a n * u n)
    (hv : ∀ n, v (n + 1) = a n * v n)
    {i j : ℕ} (hij : i < j) :
    Nat.Coprime (a i) (a j) := by
  have hcurrent : ∀ n, Nat.Coprime (a n) (v n) := by
    intro n
    exact reducedStep_coprime_currentFactor (hred (n + 1)) (hu n) (hv n)
  have hdiv : a i ∣ v j := base_dvd_denState_later a v hv hij
  exact ((hcurrent j).of_dvd_right hdiv).symm

/-- Every earlier multiplier is coprime to every later reduced numerator. -/
theorem reducedTail_wholeModulusAvoidance
    (a u v : ℕ → ℕ)
    (hred : ∀ n, Nat.Coprime (u n) (v n))
    (hv : ∀ n, v (n + 1) = a n * v n)
    {i t : ℕ} (hit : i < t) :
    Nat.Coprime (a i) (u t) := by
  have hdiv : a i ∣ v t := base_dvd_denState_later a v hv hit
  exact ((hred t).of_dvd_right hdiv).symm

/-- There is no infinite reduced exact tail whose numerator tends to infinity
but has a uniformly bounded upward increment. -/
theorem no_boundedRise_reducedTail
    (a u v : ℕ → ℕ) (B : ℕ)
    (hB : 0 < B)
    (ha : ∀ n, 1 < a n)
    (hred : ∀ n, Nat.Coprime (u n) (v n))
    (hu : ∀ n, u (n + 1) + v n = a n * u n)
    (hv : ∀ n, v (n + 1) = a n * v n)
    (hrise : ∀ n, u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  apply no_boundedRise_of_tailAvoidance u a 0 B hB
  · intro n _
    exact ha n
  · intro i j _ _ hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact reducedTail_pairwiseCoprime a u v hred hu hv hijlt
    · exact (reducedTail_pairwiseCoprime a u v hred hu hv hjilt).symm
  · intro i t _ hit
    exact reducedTail_wholeModulusAvoidance a u v hred hv hit
  · intro n _
    exact hrise n
  · exact huTop

/-- Eventual form of `no_boundedRise_reducedTail`, obtained by shifting to the
first reduced exact index. -/
theorem no_eventuallyBoundedRise_reducedTail
    (a u v : ℕ → ℕ) (N B : ℕ)
    (hB : 0 < B)
    (ha : ∀ n, N ≤ n → 1 < a n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hu : ∀ n, N ≤ n → u (n + 1) + v n = a n * u n)
    (hv : ∀ n, N ≤ n → v (n + 1) = a n * v n)
    (hrise : ∀ n, N ≤ n → u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  apply no_boundedRise_reducedTail
    (fun n ↦ a (n + N)) (fun n ↦ u (n + N)) (fun n ↦ v (n + N)) B hB
  · intro n
    exact ha (n + N) (by omega)
  · intro n
    exact hred (n + N) (by omega)
  · intro n
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hu (n + N) (by omega)
  · intro n
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hv (n + N) (by omega)
  · intro n
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hrise (n + N) (by omega)
  · exact (Filter.tendsto_add_atTop_iff_nat N).mpr huTop

/-! The remaining bounded-negative wrapper needs the tail gcd to stabilise.
The next lemmas kernel-check that exact arithmetic reduction. -/

/-- The gcd of the product-cleared tail and denominator states divides its
successor. -/
theorem tailGcd_dvd_succ
    (a C D Cnext Dnext : ℕ)
    (hC : Cnext + D = a * C)
    (hD : Dnext = a * D) :
    Nat.gcd C D ∣ Nat.gcd Cnext Dnext := by
  apply Nat.dvd_gcd
  · have hsum : Nat.gcd C D ∣ Cnext + D := by
      rw [hC]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left C D) a
    exact (Nat.dvd_add_iff_left (Nat.gcd_dvd_right C D)).mpr hsum
  · rw [hD]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right C D) a

/-- At a negative-state index, the tail gcd is exactly the gcd with the
positive negative-state magnitude. -/
theorem tailGcd_eq_gcd_negativeMagnitude
    (a C D e : ℕ)
    (hshape : D + e = (a - 1) * C) :
    Nat.gcd C D = Nat.gcd C e := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left C D)
    have hsum : Nat.gcd C D ∣ D + e := by
      rw [hshape]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left C D) (a - 1)
    exact (Nat.dvd_add_iff_right (Nat.gcd_dvd_right C D)).mpr hsum
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left C e)
    have hsum : Nat.gcd C e ∣ D + e := by
      rw [hshape]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left C e) (a - 1)
    exact (Nat.dvd_add_iff_left (Nat.gcd_dvd_right C e)).mpr hsum

/-- A positive divisibility chain with cofinally bounded values is eventually
constant. -/
theorem dvdChain_eventuallyConstant_of_cofinally_bounded
    (G : ℕ → ℕ) (B : ℕ)
    (hpos : ∀ n, 0 < G n)
    (hchain : ∀ n, G n ∣ G (n + 1))
    (hcofinal : ∀ n, ∃ t, n ≤ t ∧ G t ≤ B) :
    ∃ N, ∀ n, N ≤ n → G n = G N := by
  classical
  have hmonoStep : ∀ n, G n ≤ G (n + 1) := by
    intro n
    exact Nat.le_of_dvd (hpos (n + 1)) (hchain n)
  have hmono : Monotone G := monotone_nat_of_le_succ hmonoStep
  have hbound : ∀ n, G n ≤ B := by
    intro n
    obtain ⟨t, hnt, htB⟩ := hcofinal n
    exact (hmono hnt).trans htB
  let P : ℕ → Prop := fun d ↦ ∃ n, B - G n = d
  have hP : ∃ d, P d := ⟨B - G 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hP
  refine ⟨N, fun n hn ↦ ?_⟩
  have hGNle : G N ≤ G n := hmono hn
  have hSubLe : B - G n ≤ B - G N := by omega
  have hMin : B - G N ≤ B - G n := by
    rw [hN]
    exact Nat.find_min' hP ⟨n, rfl⟩
  have hSubEq : B - G n = B - G N := Nat.le_antisymm hSubLe hMin
  have hBn := hbound n
  have hBN := hbound N
  omega

/-- Cofinal bounded negative-state magnitudes force the exact tail gcd to
stabilise. -/
theorem tailGcd_eventuallyConstant_of_cofinally_boundedNegative
    (a C D : ℕ → ℕ) (B : ℕ)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hnegative : ∀ n, ∃ t e, n ≤ t ∧ 0 < e ∧ e ≤ B ∧
      D t + e = (a t - 1) * C t) :
    ∃ N, ∀ n, N ≤ n →
      Nat.gcd (C n) (D n) = Nat.gcd (C N) (D N) := by
  apply dvdChain_eventuallyConstant_of_cofinally_bounded
    (fun n ↦ Nat.gcd (C n) (D n)) B
  · intro n
    exact Nat.gcd_pos_of_pos_left (D n) (hCpos n)
  · intro n
    exact tailGcd_dvd_succ (a n) (C n) (D n) (C (n + 1)) (D (n + 1))
      (hC n) (hD n)
  · intro n
    obtain ⟨t, e, hnt, hepos, heB, hshape⟩ := hnegative n
    refine ⟨t, hnt, ?_⟩
    rw [tailGcd_eq_gcd_negativeMagnitude (a t) (C t) (D t) e hshape]
    exact (Nat.le_of_dvd hepos (Nat.gcd_dvd_right (C t) e)).trans heB

/-- Cofinal bounded negative magnitudes are incompatible with a tail state
tending to infinity.  This composes gcd stabilisation with the exact reduced
CRT obstruction. -/
theorem no_cofinallyBoundedNegative_of_tailTendsto
    (a C D : ℕ → ℕ) (B : ℕ)
    (hB : 0 < B)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hRise : ∀ n, C (n + 1) ≤ C n + B)
    (hnegative : ∀ n, ∃ t e, n ≤ t ∧ 0 < e ∧ e ≤ B ∧
      D t + e = (a t - 1) * C t)
    (hCTop : Filter.Tendsto C Filter.atTop Filter.atTop) :
    False := by
  obtain ⟨N, hG⟩ := tailGcd_eventuallyConstant_of_cofinally_boundedNegative
    a C D B hCpos hC hD hnegative
  let g := Nat.gcd (C N) (D N)
  have hgPos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left (D N) (hCpos N)
  have hgC : ∀ n, N ≤ n → g ∣ C n := by
    intro n hn
    dsimp [g]
    rw [← hG n hn]
    exact Nat.gcd_dvd_left (C n) (D n)
  have hgD : ∀ n, N ≤ n → g ∣ D n := by
    intro n hn
    dsimp [g]
    rw [← hG n hn]
    exact Nat.gcd_dvd_right (C n) (D n)
  let u : ℕ → ℕ := fun n ↦ C n / g
  let v : ℕ → ℕ := fun n ↦ D n / g
  have hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n) := by
    intro n hn
    have hcop := Nat.coprime_div_gcd_div_gcd
      (Nat.gcd_pos_of_pos_left (D n) (hCpos n))
    dsimp [u, v]
    simpa [hG n hn] using hcop
  have hu : ∀ n, N ≤ n → u (n + 1) + v n = a n * u n := by
    intro n hn
    apply Nat.eq_of_mul_eq_mul_left hgPos
    dsimp [u, v]
    calc
      g * (C (n + 1) / g + D n / g) = C (n + 1) + D n := by
        rw [Nat.mul_add, Nat.mul_div_cancel' (hgC (n + 1) (by omega)),
          Nat.mul_div_cancel' (hgD n hn)]
      _ = a n * C n := hC n
      _ = g * (a n * (C n / g)) := by
        have hCn : C n = g * (C n / g) :=
          (Nat.mul_div_cancel' (hgC n hn)).symm
        calc
          a n * C n = a n * (g * (C n / g)) :=
            congrArg (fun x ↦ a n * x) hCn
          _ = g * (a n * (C n / g)) := by ring
  have hv : ∀ n, N ≤ n → v (n + 1) = a n * v n := by
    intro n hn
    dsimp [v]
    rw [hD n]
    exact Nat.mul_div_assoc (a n) (hgD n hn)
  have huRise : ∀ n, N ≤ n → u (n + 1) ≤ u n + B := by
    intro n hn
    have hmul : g * (C (n + 1) / g) ≤ g * (C n / g + B) := by
      rw [Nat.mul_div_cancel' (hgC (n + 1) (by omega)), Nat.mul_add,
        Nat.mul_div_cancel' (hgC n hn)]
      have hBmul : B ≤ g * B := by
        simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right B hgPos
      exact (hRise n).trans (Nat.add_le_add_left hBmul (C n))
    dsimp [u]
    exact Nat.le_of_mul_le_mul_left hmul hgPos
  have huTop : Filter.Tendsto u Filter.atTop Filter.atTop := by
    have hdivMap : Filter.Tendsto (fun x : ℕ ↦ x / g)
        Filter.atTop Filter.atTop :=
      le_of_eq (Filter.map_div_atTop_eq_nat g hgPos)
    exact hdivMap.comp hCTop
  exact no_eventuallyBoundedRise_reducedTail a u v N B hB
    (fun n _ ↦ ha n) hred hu hv huRise huTop

/-- A nonzero integer magnitude which vanishes relative to a natural tail
state forces that tail state to tend to infinity.  The hypothesis is the
division-free arithmetic form of `mₙ / Cₙ → 0`. -/
theorem tailState_tendsto_atTop_of_nonzero_normalizedVanishes
    (C magnitude : ℕ → ℕ)
    (hmagnitude : ∀ n, 0 < magnitude n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * magnitude n < C n) :
    Filter.Tendsto C Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro bound
  obtain ⟨N, hN⟩ := hvanish (bound + 1)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hscale : bound + 1 ≤ (bound + 1) * magnitude n :=
    Nat.le_mul_of_pos_right (bound + 1) (hmagnitude n)
  exact le_trans (by omega) (le_trans hscale (Nat.le_of_lt (hN n hn)))

/-- Division-free normalized vanishing closes the cofinally bounded negative
branch by supplying the tail divergence needed above. -/
theorem no_cofinallyBoundedNegative_of_normalizedVanishes
    (a C D magnitude : ℕ → ℕ) (B : ℕ)
    (hB : 0 < B)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hRise : ∀ n, C (n + 1) ≤ C n + B)
    (hmagnitude : ∀ n, 0 < magnitude n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * magnitude n < C n)
    (hnegative : ∀ n, ∃ t e, n ≤ t ∧ 0 < e ∧ e ≤ B ∧
      D t + e = (a t - 1) * C t) :
    False := by
  exact no_cofinallyBoundedNegative_of_tailTendsto a C D B hB ha hCpos
    hC hD hRise hnegative
    (tailState_tendsto_atTop_of_nonzero_normalizedVanishes
      C magnitude hmagnitude hvanish)

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

/-! ## Bounded negative part: the signed wrapper

The preceding CRT theorem excludes cofinally many bounded negative errors once
their nonzero magnitudes vanish relative to the tail.  The final wrapper has
two additional ingredients.  First, the exact defect identity makes zero
absorbing as soon as the centered representative satisfies `|Eₙ| < Cₙ`.
Second, failure of cofinal negativity leaves an eventually nonnegative natural
tail, so `centeredState_eventually_zero` applies.
-/

/-- The natural product-cleared recurrence realizes the integer tail update
used by `nextTailState`. -/
theorem natTail_eq_nextTailState
    (a C D : ℕ → ℕ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n) (n : ℕ) :
    (C (n + 1) : ℤ) =
      nextTailState (a n : ℤ) (D n : ℤ) (C n : ℤ) := by
  have hCast := congrArg (fun x : ℕ ↦ (x : ℤ)) (hC n)
  simp only [Nat.cast_add, Nat.cast_mul] at hCast
  simp only [nextTailState]
  omega

/-- The natural denominator recurrence realizes `nextDenState` over the
integers. -/
theorem natDen_eq_nextDenState
    (a D : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = a n * D n) (n : ℕ) :
    (D (n + 1) : ℤ) = nextDenState (a n : ℤ) (D n : ℤ) := by
  have hCast := congrArg (fun x : ℕ ↦ (x : ℤ)) (hD n)
  simpa only [Nat.cast_mul, nextDenState] using hCast

/-- Along an exact natural orbit, the signed centered state gives the integer
tail identity `Cₙ₊₁ = Cₙ - Eₙ`. -/
theorem natTail_eq_sub_centeredState
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) :
    (C (n + 1) : ℤ) = (C n : ℤ) - E n := by
  rw [natTail_eq_nextTailState a C D hC n,
    nextTailState_eq_sub_centered, ← hE n]

/-- A zero centered state is absorbing under the strict centered-representative
bound at the next index.  The defect identity makes `Cₙ₊₁` divide `Eₙ₊₁`, and
the only multiple with smaller absolute value is zero. -/
theorem centeredState_zero_absorbing
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hcentered : ∀ n, Int.natAbs (E n) < C n)
    (n : ℕ) (hzero : E n = 0) :
    E (n + 1) = 0 := by
  have hdefect := sylvesterDefect_mul_nextTailState
    (a n : ℤ) (a (n + 1) : ℤ) (D n : ℤ) (C n : ℤ)
  rw [← natTail_eq_nextTailState a C D hC n,
    ← natDen_eq_nextDenState a D hD n, ← hE n, ← hE (n + 1), hzero]
    at hdefect
  simp only [pow_two, mul_zero, zero_sub] at hdefect
  have hdiv : (C (n + 1) : ℤ) ∣ E (n + 1) := by
    refine ⟨-sylvesterDefect (a n : ℤ) (a (n + 1) : ℤ), ?_⟩
    calc
      E (n + 1) =
          -(sylvesterDefect (a n : ℤ) (a (n + 1) : ℤ) *
            (C (n + 1) : ℤ)) := by omega
      _ = (C (n + 1) : ℤ) *
          -sylvesterDefect (a n : ℤ) (a (n + 1) : ℤ) := by ring
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
  simpa using hcentered (n + 1)

/-- If zero is absorbing from an index onward, failure of eventual zero forces
every state on that tail to be nonzero. -/
theorem eventually_nonzero_of_zero_absorbing
    (E : ℕ → ℤ) (N : ℕ)
    (habsorbing : ∀ n, N ≤ n → E n = 0 → E (n + 1) = 0)
    (hnot : ¬ ∃ M, ∀ n, M ≤ n → E n = 0) :
    ∀ n, N ≤ n → E n ≠ 0 := by
  intro n hn hzero
  apply hnot
  refine ⟨n, fun t hnt ↦ ?_⟩
  induction t, hnt using Nat.le_induction with
  | base => exact hzero
  | succ t hnt iht =>
      exact habsorbing t (hn.trans hnt) iht

/-- Global signed form of bounded-negative-part rigidity.  Exact natural
`D/C` dynamics, strict centering, a uniform lower bound on `E`, and
division-free normalized vanishing force the centered state to vanish
eventually. -/
theorem boundedNegativePart_eventually_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (B : ℕ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hcentered : ∀ n, Int.natAbs (E n) < C n)
    (hbound : ∀ n, -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  by_contra hnot
  have habsorbing : ∀ n, E n = 0 → E (n + 1) = 0 := by
    intro n
    exact centeredState_zero_absorbing a C D E hC hD hE hcentered n
  have hnonzero : ∀ n, E n ≠ 0 :=
    fun n ↦ eventually_nonzero_of_zero_absorbing E 0
      (fun m _ ↦ habsorbing m) hnot n (Nat.zero_le n)
  by_cases hnegative : ∀ n, ∃ t, n ≤ t ∧ E t < 0
  · have hBpos : 0 < B := by
      obtain ⟨t, _, htneg⟩ := hnegative 0
      have htbound := hbound t
      omega
    have hRise : ∀ n, C (n + 1) ≤ C n + B := by
      intro n
      have htail := natTail_eq_sub_centeredState a C D E hC hE n
      have hboundn := hbound n
      exact_mod_cast (show (C (n + 1) : ℤ) ≤ (C n : ℤ) + (B : ℤ) by omega)
    have hmagnitude : ∀ n, 0 < Int.natAbs (E n) := by
      intro n
      exact Int.natAbs_pos.mpr (hnonzero n)
    have hnegativeShape : ∀ n, ∃ t e, n ≤ t ∧ 0 < e ∧ e ≤ B ∧
        D t + e = (a t - 1) * C t := by
      intro n
      obtain ⟨t, hnt, htneg⟩ := hnegative n
      let e := Int.natAbs (E t)
      have hepos : 0 < e := Int.natAbs_pos.mpr (hnonzero t)
      have hecast : (e : ℤ) = -E t := by
        dsimp [e]
        exact Int.ofNat_natAbs_of_nonpos (le_of_lt htneg)
      have heB : e ≤ B := by
        have htbound := hbound t
        exact_mod_cast (show (e : ℤ) ≤ (B : ℤ) by omega)
      have haone : 1 ≤ a t := by have := ha t; omega
      have hshapeCast :
          (D t : ℤ) + (e : ℤ) = ((a t - 1 : ℕ) : ℤ) * (C t : ℤ) := by
        rw [Nat.cast_sub haone]
        rw [hE t] at hecast
        simp only [centeredState] at hecast
        norm_num at hecast ⊢
        omega
      refine ⟨t, e, hnt, hepos, heB, ?_⟩
      exact_mod_cast hshapeCast
    exact no_cofinallyBoundedNegative_of_normalizedVanishes
      a C D (fun n ↦ Int.natAbs (E n)) B hBpos ha hCpos hC hD hRise
      hmagnitude hvanish hnegativeShape
  · push Not at hnegative
    obtain ⟨N, hnonnegative⟩ := hnegative
    let Eplus : ℕ → ℕ := fun n ↦ Int.toNat (E (N + n))
    have hrec : ∀ n, C (N + (n + 1)) + Eplus n = C (N + n) := by
      intro n
      have hnnonneg : 0 ≤ E (N + n) := hnonnegative (N + n) (by omega)
      apply Nat.cast_injective (R := ℤ)
      simp only [Nat.cast_add]
      rw [Int.toNat_of_nonneg hnnonneg]
      have htail := natTail_eq_sub_centeredState a C D E hC hE (N + n)
      have htail' :
          (C ((N + n) + 1) : ℤ) + E (N + n) = (C (N + n) : ℤ) := by
        omega
      simpa only [Nat.add_assoc] using htail'
    obtain ⟨K, hK⟩ := centeredState_eventually_zero
      (fun n ↦ C (N + n)) Eplus hrec
    refine hnot ⟨N + K, fun n hn ↦ ?_⟩
    have hNn : N ≤ n := by omega
    let k := n - N
    have hNk : N + k = n := Nat.add_sub_of_le hNn
    have hKk : K ≤ k := by omega
    have htoNat : Int.toNat (E n) = 0 := by
      simpa [Eplus, hNk] using hK k hKk
    have hnnonneg : 0 ≤ E n := hnonnegative n hNn
    have hcast := Int.toNat_of_nonneg hnnonneg
    rw [htoNat] at hcast
    exact hcast.symm

/-- Eventual signed form matching the analytic bounded-negative-part regime:
strict centering and the lower bound may begin at different indices. -/
theorem eventuallyBoundedNegativePart_eventually_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hcentered : ∃ N, ∀ n, N ≤ n → Int.natAbs (E n) < C n)
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  obtain ⟨NC, hcentered⟩ := hcentered
  obtain ⟨NB, B, hbound⟩ := hbound
  let N := max NC NB
  obtain ⟨K, hK⟩ := boundedNegativePart_eventually_zero
    (fun n ↦ a (N + n)) (fun n ↦ C (N + n))
    (fun n ↦ D (N + n)) (fun n ↦ E (N + n)) B
    (fun n ↦ ha (N + n)) (fun n ↦ hCpos (N + n))
    (fun n ↦ by simpa only [Nat.add_assoc] using hC (N + n))
    (fun n ↦ by simpa only [Nat.add_assoc] using hD (N + n))
    (fun n ↦ hE (N + n))
    (fun n ↦ hcentered (N + n) ((Nat.le_max_left NC NB).trans (by omega)))
    (fun n ↦ hbound (N + n) ((Nat.le_max_right NC NB).trans (by omega)))
    (fun scale ↦ by
      obtain ⟨M, hM⟩ := hvanish scale
      exact ⟨M, fun n hn ↦ hM (N + n) (by omega)⟩)
  refine ⟨N + K, fun n hn ↦ ?_⟩
  have hNn : N ≤ n := by omega
  let k := n - N
  have hNk : N + k = n := Nat.add_sub_of_le hNn
  have hKk : K ≤ k := by omega
  simpa [hNk] using hK k hKk

end ErdosProblems.Erdos243
