import ErdosProblems.Erdos1049.PaperR16.PrimitiveRadial

/-!
# Exact orders, primitive-root counts, and an injective family of test roots

Candidate source; new Lean checks UNRUN. One primitive root of each of
infinitely many pairwise distinct orders suffices for the polynomial argument;
no lower bound for Euler's totient and no prime-distribution theorem is needed.
-/

noncomputable section
open scoped BigOperators Classical
open Filter Topology Polynomial

namespace ErdosProblems.Erdos1049.PaperR16

/-- The general order under composition, not just the specialised Mahler case. -/
theorem isPrimitiveRoot_pow_gcd (ζ : ℂ) (d m : ℕ)
    (hζ : IsPrimitiveRoot ζ d) (hm : m ≠ 0) :
    IsPrimitiveRoot (ζ ^ m) (d / Nat.gcd d m) := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [orderOf_pow' ζ hm, ← hζ.eq_orderOf]

/-- The positive order in the general gcd formula. -/
lemma quotient_order_pos (d m : ℕ) (hd : 0 < d) :
    0 < d / Nat.gcd d m := by
  exact Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_left d m))
    (Nat.gcd_pos_of_pos_left m hd)

/-- The general, fully normalised composed boundary limit. -/
theorem lambert_primitive_power_radial_gcd (d m : ℕ)
    (hd : 0 < d) (hm : 0 < m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) :
    Tendsto (fun r : ℝ => (radialGauge r : ℂ) * lambert (((r : ℂ) * ζ) ^ m))
      radial (𝓝 ((Nat.gcd d m : ℂ) / ((d : ℂ) * (m : ℂ)))) := by
  have hq := quotient_order_pos d m hd
  have hroot := isPrimitiveRoot_pow_gcd ζ d m hζ (Nat.ne_of_gt hm)
  have hlim := lambert_primitive_power_radial m (d / Nat.gcd d m) hm hq ζ hroot
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hqC : ((d / Nat.gcd d m : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  have hgC : (Nat.gcd d m : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.gcd_pos_of_pos_left m hd))
  have hdiv : ((d / Nat.gcd d m : ℕ) : ℂ) * (Nat.gcd d m : ℂ) = (d : ℂ) := by
    exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_left d m))
  have hweight : (m : ℂ)⁻¹ * ((d / Nat.gcd d m : ℕ) : ℂ)⁻¹ =
      (Nat.gcd d m : ℂ) / ((d : ℂ) * (m : ℂ)) := by
    calc
      (m : ℂ)⁻¹ * ((d / Nat.gcd d m : ℕ) : ℂ)⁻¹ =
          (Nat.gcd d m : ℂ) /
            ((((d / Nat.gcd d m : ℕ) : ℂ) * (Nat.gcd d m : ℂ)) * (m : ℂ)) := by
        field_simp [hmC, hqC, hgC] <;> ring
      _ = (Nat.gcd d m : ℂ) / ((d : ℂ) * (m : ℂ)) := by rw [hdiv]
  simpa only [hweight] using hlim

/-- Exact primitive-root count supplied by the pinned complex-root API. -/
theorem primitive_root_count (d : ℕ) :
    (primitiveRoots d ℂ).card = Nat.totient d :=
  Complex.card_primitiveRoots d

/-- Coprimality is necessary; no assumption that `k` is prime is used. -/
theorem isPrimitiveRoot_mahler_power (ell k s i : ℕ)
    (hell : 0 < ell) (hk : 0 < k) (hc : ell.Coprime k)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (ell * k ^ s)) :
    IsPrimitiveRoot (ζ ^ (k ^ i)) (ell * k ^ (s - i)) := by
  have hn : 0 < ell * k ^ s := mul_pos hell (pow_pos hk s)
  by_cases hi : i ≤ s
  · have hp : ell * k ^ s = k ^ i * (ell * k ^ (s - i)) := by
      have he : s = i + (s - i) := by omega
      calc
        ell * k ^ s = ell * k ^ (i + (s - i)) := by rw [← he]
        _ = k ^ i * (ell * k ^ (s - i)) := by rw [pow_add]; ring
    exact IsPrimitiveRoot.pow hn hζ hp
  · have hs : s ≤ i := by omega
    have hbase : IsPrimitiveRoot (ζ ^ (k ^ s)) ell :=
      IsPrimitiveRoot.pow hn hζ (by ring)
    have hp := hbase.pow_of_coprime (k ^ (i - s)) (hc.symm.pow_left (i - s))
    have he : (ζ ^ (k ^ s)) ^ (k ^ (i - s)) = ζ ^ (k ^ i) := by
      calc
        (ζ ^ (k ^ s)) ^ (k ^ (i - s)) = ζ ^ (k ^ s * k ^ (i - s)) :=
          (pow_mul ζ _ _).symm
        _ = ζ ^ (k ^ (s + (i - s))) := by rw [pow_add]
        _ = ζ ^ (k ^ i) := by
          have hn' : s + (i - s) = i := by omega
          rw [hn']
    simpa only [he, Nat.sub_eq_zero_of_le hs, pow_zero, mul_one] using hp

lemma mahler_order_product (ell k s i : ℕ) :
    k ^ i * (ell * k ^ (s - i)) = ell * k ^ max s i := by
  have he : i + (s - i) = max s i := by omega
  calc
    k ^ i * (ell * k ^ (s - i)) = ell * k ^ (i + (s - i)) := by rw [pow_add]; ring
    _ = ell * k ^ max s i := by rw [he]

/-- The exact unscaled boundary coefficient, valid also for composite `k`. -/
theorem lambert_mahler_radial_weight (ell k s i : ℕ)
    (hell : 0 < ell) (hk : 0 < k) (hc : ell.Coprime k)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (ell * k ^ s)) :
    Tendsto (fun r : ℝ => (radialGauge r : ℂ) *
      lambert (((r : ℂ) * ζ) ^ (k ^ i)))
      radial (𝓝 (((ell : ℂ) * (k : ℂ) ^ max s i)⁻¹)) := by
  have hroot := isPrimitiveRoot_mahler_power ell k s i hell hk hc ζ hζ
  have hlim := lambert_primitive_power_radial (k ^ i) (ell * k ^ (s - i))
    (pow_pos hk i) (mul_pos hell (pow_pos hk (s - i))) ζ hroot
  have hw : (((k ^ i : ℕ) : ℂ) * ((ell * k ^ (s - i) : ℕ) : ℂ)) =
      (ell : ℂ) * (k : ℂ) ^ max s i := by
    exact_mod_cast mahler_order_product ell k s i
  simpa only [← mul_inv, hw] using hlim

/-- An elementary source of pairwise distinct root orders, coprime to `k`. -/
def testOrder (k s n : ℕ) : ℕ := (k * n + 1) * k ^ s

def testRoot (k s n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (testOrder k s n : ℂ))

lemma testOrder_pos (k s n : ℕ) (hk : 0 < k) : 0 < testOrder k s n := by
  unfold testOrder
  exact mul_pos (by omega) (pow_pos hk s)

lemma testOrder_coprime (k n : ℕ) : (k * n + 1).Coprime k := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  apply Nat.dvd_antisymm
  · have hleft := Nat.gcd_dvd_left (k * n + 1) k
    have hright : Nat.gcd (k * n + 1) k ∣ k * n :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_right (k * n + 1) k) n
    have hsub := Nat.dvd_sub hleft hright
    simpa using hsub
  · exact one_dvd _

lemma testRoot_primitive (k s n : ℕ) (hk : 0 < k) :
    IsPrimitiveRoot (testRoot k s n) (testOrder k s n) :=
  Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt (testOrder_pos k s n hk))

/-- Roots of different exact orders cannot coincide. -/
theorem testRoot_injective (k s : ℕ) (hk : 0 < k) :
    Function.Injective (testRoot k s) := by
  intro a b hab
  have ha := testRoot_primitive k s a hk
  have hb := testRoot_primitive k s b hk
  rw [← hab] at hb
  have he : testOrder k s a = testOrder k s b := ha.unique hb
  change (k * a + 1) * k ^ s = (k * b + 1) * k ^ s at he
  have he' : k * a + 1 = k * b + 1 :=
    mul_right_cancel₀ (pow_ne_zero s (Nat.ne_of_gt hk)) he
  have he'' : k * a = k * b := by omega
  exact mul_left_cancel₀ (Nat.ne_of_gt hk) he''

/-- Exact finite count of our primitive-root test family. -/
theorem testRoot_finset_card (k s N : ℕ) (hk : 0 < k) :
    ((Finset.range N).image (testRoot k s)).card = N := by
  classical
  rw [Finset.card_image_of_injective _ (testRoot_injective k s hk), Finset.card_range]

/-- `degree+1` distinct primitive-root tests suffice; no growth estimate for totient is hidden. -/
theorem polynomial_eq_zero_of_testRoots (k s : ℕ) (hk : 0 < k) (P : ℂ[X])
    (hroot : ∀ n ≤ P.natDegree, P.eval (testRoot k s n) = 0) : P = 0 := by
  classical
  by_contra hp
  let S : Finset ℂ := (Finset.range (P.natDegree + 1)).image (testRoot k s)
  have hS : S.val ⊆ P.roots := by
    intro z hz
    change z ∈ S at hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    apply (Polynomial.mem_roots hp).2
    exact hroot n (by have h := Finset.mem_range.mp hn; omega)
  have hbound : S.card ≤ P.natDegree := Polynomial.card_le_degree_of_subset_roots hS
  have hcard : S.card = P.natDegree + 1 :=
    testRoot_finset_card k s (P.natDegree + 1) hk
  rw [hcard] at hbound
  omega

end ErdosProblems.Erdos1049.PaperR16
