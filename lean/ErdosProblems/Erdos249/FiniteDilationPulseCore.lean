import Mathlib

/-!
# Arithmetic core for pulses after finitely many dilations

Private finite-dilation arithmetic core, checked with Mathlib / Lean 4.29.1.

This file proves centre isolation, neighbour killing, the simultaneous
CRT/Dirichlet prime-witness construction, and unconditional isolated pulses
for finite dilation mixing at a prime-accessible residue. The public
integer-radix source supplies the signed-series consumer separately. Series
transport and the joint value theorem are not proved here. None of these
statements establishes irrationality of the unreduced totient series.
-/

namespace ErdosProblems.Erdos249.FiniteDilationPulseCore

open scoped BigOperators

/-- Reindexing a finite sum of series at bases b^d gives these coefficients. -/
def mixedCoefficient (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m N : ℕ) : ℤ :=
  ∑ d ∈ D, if d ∣ N then g d (Nat.totient (N / d) % m) else 0

/-- A divisor from the finite family cannot survive at the smallest prime centre
unless it is the smallest dilation itself. -/
theorem divisor_at_minimal_prime_centre
    {d δ p : ℕ} (hp : p.Prime) (hd : 0 < d) (hδ : 0 < δ)
    (hmin : δ ≤ d) (hsmall : d < p) (hdiv : d ∣ δ * p) : d = δ := by
  have hnot : ¬ p ∣ d := by
    intro h
    have := Nat.le_of_dvd hd h
    omega
  have hcop : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr hnot).symm
  have hdiv' : d ∣ p * δ := by simpa only [Nat.mul_comm] using hdiv
  have hdδ : d ∣ δ := hcop.dvd_of_dvd_mul_left hdiv'
  exact Nat.le_antisymm (Nat.le_of_dvd hδ hdδ) hmin

/-- The central coefficient is exactly the selected coefficient. -/
theorem mixedCoefficient_at_prime_centre
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m δ p : ℕ)
    (hδD : δ ∈ D) (hδ : 0 < δ) (hp : p.Prime)
    (hpos : ∀ d ∈ D, 0 < d)
    (hmin : ∀ d ∈ D, δ ≤ d)
    (hsmall : ∀ d ∈ D, d < p) :
    mixedCoefficient D g m (δ * p) = g δ ((p - 1) % m) := by
  classical
  unfold mixedCoefficient
  rw [Finset.sum_eq_single δ]
  · simp only [dvd_mul_right, if_true]
    rw [Nat.mul_div_cancel_left p hδ, Nat.totient_prime hp]
  · intro d hd hne
    have hnot : ¬ d ∣ δ * p := by
      intro hdiv
      exact hne (divisor_at_minimal_prime_centre hp (hpos d hd) hδ
        (hmin d hd) (hsmall d hd) hdiv)
    simp only [hnot, if_false]
  · intro hnot
    exact (hnot hδD).elim

/-- A prime divisor survives division by a coprime dilation. -/
theorem prime_dvd_quotient
    {q d N : ℕ} (hqd : Nat.Coprime q d) (hdN : d ∣ N) (hqN : q ∣ N) :
    q ∣ N / d := by
  have hfactor : d * (N / d) = N := Nat.mul_div_cancel' hdN
  have hprod : q ∣ d * (N / d) := by rw [hfactor]; exact hqN
  exact hqd.dvd_of_dvd_mul_left hprod

/-- A forced prime q with m | q-1 kills the totient residue of the quotient. -/
theorem modulus_dvd_quotient_totient
    {m q d N : ℕ} (hq : q.Prime) (hm : m ∣ q - 1)
    (hqd : Nat.Coprime q d) (hdN : d ∣ N) (hqN : q ∣ N) :
    m ∣ Nat.totient (N / d) := by
  have hdiv := Nat.totient_dvd_of_dvd (prime_dvd_quotient hqd hdN hqN)
  rw [Nat.totient_prime hq] at hdiv
  exact hm.trans hdiv

/-- One auxiliary prime simultaneously kills all active dilation summands. -/
theorem mixedCoefficient_eq_zero_of_auxiliary_prime
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m N q : ℕ)
    (hq : q.Prime) (hm : m ∣ q - 1) (hqN : q ∣ N)
    (hcop : ∀ d ∈ D, Nat.Coprime q d)
    (hzero : ∀ d ∈ D, g d 0 = 0) :
    mixedCoefficient D g m N = 0 := by
  classical
  unfold mixedCoefficient
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hdN : d ∣ N
  · rw [if_pos hdN]
    have hdiv := modulus_dvd_quotient_totient hq hm (hcop d hd) hdN hqN
    rw [Nat.mod_eq_zero_of_dvd hdiv, hzero d hd]
  · rw [if_neg hdN]

/-- A unit multiplier can be divided out of a prescribed nonzero prime
residue.  The resulting residue is itself a unit, as Dirichlet requires. -/
theorem exists_coprime_residue_for_dilated_centre
    {δ j q : ℕ} (hq : 0 < q)
    (hδq : Nat.Coprime δ q) (hjq : Nat.Coprime j q) :
    ∃ a : ℕ, Nat.Coprime a q ∧ δ * a ≡ j [MOD q] := by
  letI : NeZero q := ⟨by omega⟩
  let uδ : (ZMod q)ˣ := ZMod.unitOfCoprime δ hδq
  let uj : (ZMod q)ˣ := ZMod.unitOfCoprime j hjq
  let u : (ZMod q)ˣ := uδ⁻¹ * uj
  refine ⟨(u : ZMod q).val, ZMod.val_coe_unit_coprime u, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff (δ * (u : ZMod q).val) j q).mp
  have hu : uδ * u = uj := by simp [u]
  calc
    ((δ * (u : ZMod q).val : ℕ) : ZMod q) =
        (uδ : ZMod q) * (u : ZMod q) := by
          simp [uδ]
    _ = (uj : ZMod q) := congrArg (fun v : (ZMod q)ˣ => (v : ZMod q)) hu
    _ = (j : ZMod q) := by simp [uj]

private theorem coprime_of_modEq {x y n : ℕ}
    (h : x ≡ y [MOD n]) (hy : Nat.Coprime y n) : Nat.Coprime x n := by
  have h' : x % n = y % n := h
  have h1 : Nat.gcd n x = Nat.gcd n y := by
    rw [Nat.gcd_rec n x, Nat.gcd_rec n y, h']
  have hy' : Nat.gcd n y = 1 := by rw [Nat.gcd_comm]; exact hy
  show Nat.gcd x n = 1
  rw [Nat.gcd_comm, h1]
  exact hy'

private theorem coprime_prime_of_lt {q n : ℕ}
    (hq : q.Prime) (hn0 : 0 < n) (hnq : n < q) : Nat.Coprime q n :=
  (Nat.Prime.coprime_iff_not_dvd hq).mpr fun hd =>
    absurd (Nat.le_of_dvd hn0 hd) (by omega)

/-- A reduced congruence class for the scaled centre, with an explicit
auxiliary prime for each neighbour.  The lower bound keeps every auxiliary
prime coprime to the later finite dilation family. -/
theorem exists_scaled_isolation_modulus
    (m δ H L : ℕ) (hm : 0 < m) (hδ : 0 < δ) :
    ∃ Q b : ℕ, 0 < Q ∧ Nat.Coprime Q m ∧ Nat.Coprime Q δ ∧
      Nat.Coprime b Q ∧
      ∀ n : ℕ, L < n → n ≡ b [MOD Q] →
        ∀ j, 0 < j → j ≤ L →
          (∃ q : ℕ, q.Prime ∧ m ∣ q - 1 ∧ H < q ∧ q ∣ n - j) ∧
          (∃ q : ℕ, q.Prime ∧ m ∣ q - 1 ∧ H < q ∧ q ∣ n + j) := by
  induction L with
  | zero =>
      refine ⟨1, 1, one_pos, Nat.coprime_one_left m,
        Nat.coprime_one_left δ, Nat.coprime_one_left 1, ?_⟩
      intro n _ _ j hj hjL
      exact absurd hjL (by omega)
  | succ L ih =>
      obtain ⟨Q, b, hQ0, hQm, hQδ, hbQ, hmain⟩ := ih
      let B := max (max Q m) (max (max H δ) (L + 1))
      obtain ⟨q₁, hq₁gt, hq₁p, hq₁m⟩ :=
        Nat.forall_exists_prime_gt_and_modEq B (q := m) (a := 1)
          hm.ne' (Nat.coprime_one_left m)
      obtain ⟨q₂, hq₂gt, hq₂p, hq₂m⟩ :=
        Nat.forall_exists_prime_gt_and_modEq (max B q₁) (q := m) (a := 1)
          hm.ne' (Nat.coprime_one_left m)
      have hq₁Q : Q < q₁ := by dsimp [B] at hq₁gt; omega
      have hq₁mgt : m < q₁ := by dsimp [B] at hq₁gt; omega
      have hq₁H : H < q₁ := by dsimp [B] at hq₁gt; omega
      have hq₁δ : δ < q₁ := by dsimp [B] at hq₁gt; omega
      have hq₁L : L + 1 < q₁ := by dsimp [B] at hq₁gt; omega
      have hq₂Q : Q < q₂ := by dsimp [B] at hq₂gt; omega
      have hq₂mgt : m < q₂ := by dsimp [B] at hq₂gt; omega
      have hq₂H : H < q₂ := by dsimp [B] at hq₂gt; omega
      have hq₂δ : δ < q₂ := by dsimp [B] at hq₂gt; omega
      have hq₂L : L + 1 < q₂ := by dsimp [B] at hq₂gt; omega
      have hq₁q₂ : q₁ < q₂ := by omega
      have cq₁Q : Nat.Coprime q₁ Q := coprime_prime_of_lt hq₁p hQ0 hq₁Q
      have cq₁m : Nat.Coprime q₁ m := coprime_prime_of_lt hq₁p hm hq₁mgt
      have cq₁δ : Nat.Coprime q₁ δ := coprime_prime_of_lt hq₁p hδ hq₁δ
      have cq₁L : Nat.Coprime q₁ (L + 1) :=
        coprime_prime_of_lt hq₁p (by omega) hq₁L
      have cq₂Q : Nat.Coprime q₂ Q := coprime_prime_of_lt hq₂p hQ0 hq₂Q
      have cq₂m : Nat.Coprime q₂ m := coprime_prime_of_lt hq₂p hm hq₂mgt
      have cq₂δ : Nat.Coprime q₂ δ := coprime_prime_of_lt hq₂p hδ hq₂δ
      have cq₂q₁ : Nat.Coprime q₂ q₁ :=
        coprime_prime_of_lt hq₂p hq₁p.pos hq₁q₂
      have cq₂sub : Nat.Coprime q₂ (q₂ - (L + 1)) :=
        coprime_prime_of_lt hq₂p (by omega) (by omega)
      obtain ⟨k₁, hk₁Q, hk₁q⟩ := Nat.chineseRemainder cq₁Q.symm b (L + 1)
      have cQq₁q₂ : Nat.Coprime (Q * q₁) q₂ :=
        (cq₂Q.mul_right cq₂q₁).symm
      obtain ⟨b', hb'Qq₁, hb'q₂⟩ :=
        Nat.chineseRemainder cQq₁q₂ k₁ (q₂ - (L + 1))
      have hb'Q : Nat.Coprime b' Q :=
        coprime_of_modEq ((hb'Qq₁.of_dvd ⟨q₁, rfl⟩).trans hk₁Q) hbQ
      have hb'q₁ : Nat.Coprime b' q₁ :=
        coprime_of_modEq
          ((hb'Qq₁.of_dvd ⟨Q, mul_comm Q q₁⟩).trans hk₁q) cq₁L.symm
      have hb'q₂cop : Nat.Coprime b' q₂ :=
        coprime_of_modEq hb'q₂ cq₂sub.symm
      have hq₁div : m ∣ q₁ - 1 :=
        (Nat.modEq_iff_dvd' hq₁p.one_lt.le).mp hq₁m.symm
      have hq₂div : m ∣ q₂ - 1 :=
        (Nat.modEq_iff_dvd' hq₂p.one_lt.le).mp hq₂m.symm
      refine ⟨Q * q₁ * q₂, b',
        Nat.mul_pos (Nat.mul_pos hQ0 hq₁p.pos) hq₂p.pos, ?_, ?_,
        (hb'Q.mul_right hb'q₁).mul_right hb'q₂cop, ?_⟩
      · exact ((hQm.symm.mul_right cq₁m.symm).mul_right cq₂m.symm).symm
      · exact ((hQδ.symm.mul_right cq₁δ.symm).mul_right cq₂δ.symm).symm
      · intro n hn hnb
        have hnQ : n ≡ b [MOD Q] :=
          (((hnb.of_dvd ⟨q₁ * q₂, by ring⟩).trans
            (hb'Qq₁.of_dvd ⟨q₁, rfl⟩)).trans hk₁Q)
        have hnq₁ : n ≡ L + 1 [MOD q₁] :=
          (((hnb.of_dvd ⟨Q * q₂, by ring⟩).trans
            (hb'Qq₁.of_dvd ⟨Q, mul_comm Q q₁⟩)).trans hk₁q)
        have hnq₂ : n ≡ q₂ - (L + 1) [MOD q₂] :=
          ((hnb.of_dvd ⟨Q * q₁, by ring⟩).trans hb'q₂)
        have hd₁ : q₁ ∣ n - (L + 1) :=
          (Nat.modEq_iff_dvd' (by omega)).mp hnq₁.symm
        have hd₂ : q₂ ∣ n + (L + 1) := by
          have h5 : n + (L + 1) ≡
              q₂ - (L + 1) + (L + 1) [MOD q₂] := hnq₂.add_right (L + 1)
          rw [show q₂ - (L + 1) + (L + 1) = q₂ from by omega] at h5
          exact Nat.modEq_zero_iff_dvd.mp
            (h5.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
        intro j hj hjL
        rcases Nat.lt_or_ge j (L + 1) with hcase | hcase
        · exact hmain n (by omega) hnQ j hj (by omega)
        · have hjeq : j = L + 1 := by omega
          subst hjeq
          exact ⟨⟨q₁, hq₁p, hq₁div, hq₁H, hd₁⟩,
            ⟨q₂, hq₂p, hq₂div, hq₂H, hd₂⟩⟩

/-- The simultaneous CRT progression is reduced, so Dirichlet supplies
arbitrarily large prime centres.  The auxiliary primes work for every
dilation in the bounded finite family. -/
theorem exists_prime_witnesses_for_finite_dilations
    (D : Finset ℕ) (m δ r H : ℕ)
    (hm : 0 < m) (hδ : 0 < δ) (hrlt : r < m)
    (hr : Nat.Coprime (r + 1) m)
    (hpos : ∀ d ∈ D, 0 < d)
    (hH : ∀ d ∈ D, d ≤ H) :
    ∀ L : ℕ, ∃ p : ℕ,
      p.Prime ∧ L + 1 < δ * p ∧
      (∀ d ∈ D, d < p) ∧ (p - 1) % m = r ∧
      (∀ j, 0 < j → j ≤ L →
        (∃ q : ℕ, q.Prime ∧ m ∣ q - 1 ∧ q ∣ δ * p - j ∧
          ∀ d ∈ D, Nat.Coprime q d) ∧
        (∃ q : ℕ, q.Prime ∧ m ∣ q - 1 ∧ q ∣ δ * p + j ∧
          ∀ d ∈ D, Nat.Coprime q d)) := by
  intro L
  obtain ⟨Q, b, hQ0, hQm, hQδ, hbQ, hisolate⟩ :=
    exists_scaled_isolation_modulus m δ H L hm hδ
  obtain ⟨a, haQ, hδa⟩ :=
    exists_coprime_residue_for_dilated_centre hQ0 hQδ.symm hbQ
  obtain ⟨c, hcQ, hcm⟩ := Nat.chineseRemainder hQm a (r + 1)
  have hcQcop : Nat.Coprime c Q := coprime_of_modEq hcQ haQ
  have hcmcop : Nat.Coprime c m := coprime_of_modEq hcm hr
  obtain ⟨p, hpgt, hp, hpc⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max H (L + 1))
      (q := Q * m) (a := c) (Nat.mul_ne_zero hQ0.ne' hm.ne')
      (hcQcop.mul_right hcmcop)
  have hpH : H < p := by omega
  have hpL : L + 1 < p := by omega
  have hpQ : p ≡ a [MOD Q] :=
    (hpc.of_dvd ⟨m, rfl⟩).trans hcQ
  have hpm : p ≡ r + 1 [MOD m] :=
    (hpc.of_dvd ⟨Q, mul_comm Q m⟩).trans hcm
  have hresMod : p - 1 ≡ r [MOD m] := by
    refine Nat.ModEq.add_right_cancel' 1 ?_
    rw [show p - 1 + 1 = p from by omega]
    exact hpm
  have hres : (p - 1) % m = r := by
    change (p - 1) % m = r % m at hresMod
    simpa [Nat.mod_eq_of_lt hrlt] using hresMod
  have hδpQ : δ * p ≡ b [MOD Q] := (hpQ.mul_left δ).trans hδa
  have hcenter : L < δ * p := by nlinarith
  refine ⟨p, hp, by nlinarith, ?_, hres, ?_⟩
  · intro d hd
    exact lt_of_le_of_lt (hH d hd) hpH
  · intro j hj hjL
    obtain ⟨⟨q₁, hq₁, hmq₁, hHq₁, hdq₁⟩,
      ⟨q₂, hq₂, hmq₂, hHq₂, hdq₂⟩⟩ :=
        hisolate (δ * p) hcenter hδpQ j hj hjL
    refine ⟨⟨q₁, hq₁, hmq₁, hdq₁, ?_⟩,
      ⟨q₂, hq₂, hmq₂, hdq₂, ?_⟩⟩
    · intro d hd
      exact coprime_prime_of_lt hq₁ (hpos d hd)
        (lt_of_le_of_lt (hH d hd) hHq₁)
    · intro d hd
      exact coprime_prime_of_lt hq₂ (hpos d hd)
        (lt_of_le_of_lt (hH d hd) hHq₂)

/-- Arithmetic witness format for an isolated pulse after finite dilation
mixing.  The prime at the centre need not be the coefficient index: the
index is `δ * p`.  At each offset a single auxiliary prime kills every
active dilation summand. -/
theorem mixedCoefficient_has_pulses_of_prime_witnesses
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m δ r : ℕ)
    (hδD : δ ∈ D) (hδ : 0 < δ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hmin : ∀ d ∈ D, δ ≤ d)
    (hzero : ∀ d ∈ D, g d 0 = 0)
    (hgr : g δ r ≠ 0)
    (hwitness : ∀ L : ℕ, ∃ p : ℕ,
      p.Prime ∧ L + 1 < δ * p ∧
      (∀ d ∈ D, d < p) ∧ (p - 1) % m = r ∧
      (∀ j, 0 < j → j ≤ L →
        (∃ q : ℕ, q.Prime ∧ m ∣ q - 1 ∧ q ∣ δ * p - j ∧
          ∀ d ∈ D, Nat.Coprime q d) ∧
        (∃ q : ℕ, q.Prime ∧ m ∣ q - 1 ∧ q ∣ δ * p + j ∧
          ∀ d ∈ D, Nat.Coprime q d))) :
    ∀ L : ℕ, ∃ N : ℕ, L + 1 < N ∧ mixedCoefficient D g m N ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L →
        mixedCoefficient D g m (N - j) = 0 ∧
        mixedCoefficient D g m (N + j) = 0 := by
  intro L
  obtain ⟨p, hp, hpL, hsmall, hres, hneighbour⟩ := hwitness L
  refine ⟨δ * p, hpL, ?_, ?_⟩
  · rw [mixedCoefficient_at_prime_centre D g m δ p hδD hδ hp hpos hmin hsmall,
      hres]
    exact hgr
  · intro j hj hjL
    obtain ⟨⟨q₁, hq₁, hm₁, hdiv₁, hcop₁⟩,
      ⟨q₂, hq₂, hm₂, hdiv₂, hcop₂⟩⟩ := hneighbour j hj hjL
    exact ⟨mixedCoefficient_eq_zero_of_auxiliary_prime D g m
      (δ * p - j) q₁ hq₁ hm₁ hdiv₁ hcop₁ hzero,
      mixedCoefficient_eq_zero_of_auxiliary_prime D g m
      (δ * p + j) q₂ hq₂ hm₂ hdiv₂ hcop₂ hzero⟩

/-- Unconditional finite-dilation isolation: the only arithmetic input is a
nonzero observable at a prime-accessible residue.  The finite-family bound
`H` is explicit so the auxiliary primes can be chosen beyond every dilation. -/
theorem mixedCoefficient_has_pulses
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m δ r H : ℕ)
    (hm : 0 < m) (hδD : δ ∈ D) (hδ : 0 < δ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hmin : ∀ d ∈ D, δ ≤ d)
    (hH : ∀ d ∈ D, d ≤ H)
    (hrlt : r < m) (hr : Nat.Coprime (r + 1) m)
    (hzero : ∀ d ∈ D, g d 0 = 0)
    (hgr : g δ r ≠ 0) :
    ∀ L : ℕ, ∃ N : ℕ, L + 1 < N ∧ mixedCoefficient D g m N ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L →
        mixedCoefficient D g m (N - j) = 0 ∧
        mixedCoefficient D g m (N + j) = 0 := by
  exact mixedCoefficient_has_pulses_of_prime_witnesses D g m δ r
    hδD hδ hpos hmin hzero hgr
    (exists_prime_witnesses_for_finite_dilations D m δ r H
      hm hδ hrlt hr hpos hH)

/-- A uniform bound for the mixed word, ready for the signed radix series
consumer.  Each active summand reads one of the finitely many residues. -/
theorem mixedCoefficient_bounded
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m : ℕ)
    (hm : 0 < m) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ d ∈ D, ∀ r < m, |(g d r : ℝ)| ≤ C) :
    ∀ N : ℕ, |(mixedCoefficient D g m N : ℝ)| ≤ ∑ _d ∈ D, C := by
  intro N
  have hcast : (mixedCoefficient D g m N : ℝ) =
      ∑ d ∈ D, if d ∣ N then (g d (Nat.totient (N / d) % m) : ℝ) else 0 := by
    simp [mixedCoefficient]
  rw [hcast]
  calc
    |∑ d ∈ D, if d ∣ N then (g d (Nat.totient (N / d) % m) : ℝ) else 0|
        ≤ ∑ d ∈ D,
            |if d ∣ N then (g d (Nat.totient (N / d) % m) : ℝ) else 0| :=
          Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _d ∈ D, C := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hdN : d ∣ N
          · simpa [hdN] using hg d hd _ (Nat.mod_lt _ hm)
          · simpa [hdN] using hC

#print axioms exists_coprime_residue_for_dilated_centre
#print axioms exists_scaled_isolation_modulus
#print axioms exists_prime_witnesses_for_finite_dilations
#print axioms mixedCoefficient_has_pulses_of_prime_witnesses
#print axioms mixedCoefficient_has_pulses
#print axioms mixedCoefficient_bounded

end ErdosProblems.Erdos249.FiniteDilationPulseCore
