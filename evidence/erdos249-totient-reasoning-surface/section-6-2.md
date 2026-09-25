# Formal evidence: The Binary Totient Series, Section 6, results 6.39 to 6.71

Part of the [evidence record](../erdos249-totient-reasoning-surface.md) of the paper [erdos249-totient-reasoning-surface.pdf](../../paper/249/erdos249-totient-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="catalogue-mob-b3"></a>

## Proposition 6.39 (Decomposition by the radical), page 33

> *For $`H\ge1`$ and $`r\ge1`$,
> ``` math
> H\beta_H=\frac H{\operatorname{rad}(H)}b_{\operatorname{rad}(H)},
>  \qquad
>  \operatorname{den}(b_r)
>    =\frac{2^r-1}{\gcd(|P_r(2)|,2^r-1)}.
> ```
> The first equality follows from the definition of $`\beta_H`$; the second is ordinary reduction of an integer fraction. Multiplication by $`H/\operatorname{rad}(H)`$ can cause further cancellation. No coprimality assumption is included in either identity.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR20.radical_decomposition`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/RadicalDecomposition.lean#L50)

```lean
theorem radical_decomposition (H r : ℕ) (hH : 0 < H) (hr : 0 < r) :
    (H : ℚ) * numericMobiusShadow H =
      ((H / squarefreeKernel H : ℕ) : ℚ) * baseMobiusShadow (squarefreeKernel H) ∧
    (baseMobiusShadow r).den = mersenne r /
      ((mobiusNumeratorPolynomial r).eval 2).natAbs.gcd (mersenne r)
```

<a id="catalogue-mob-b3-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `radical_decomposition`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L243) (E249_08, line 243), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsAQ.lean#L63) (PaperStatementsAQ.lean, line 63), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-b4"></a>

## Proposition 6.40 (A cyclotomic congruence), page 33

> *Let $`r`$ be squarefree and $`m\mid r`$. In $`\mathbb Z[X]`$,
> ``` math
> P_r(X)\equiv\mu(m)J_2(r/m)\pmod{\Phi_m(X)},
> ```
> where $`J_2(n)=n^2\prod_{p\mid n}(1-p^{-2})`$ is the second Jordan totient. Evaluation at two gives
> ``` math
> \Phi_m(2)\mid P_r(2)-\mu(m)J_2(r/m).
> ```*

The Lean declarations below together state this result.

1. [`Erdos249257.CyclotomicProjectionOfShadow.cyclotomic_dvd_mobiusNumeratorPolynomial_sub`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CyclotomicProjectionOfShadow.lean#L299)

```lean
theorem cyclotomic_dvd_mobiusNumeratorPolynomial_sub
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      RepunitMobiusNumerator.mobiusNumeratorPolynomial r -
        Polynomial.C
          (ArithmeticFunction.moebius m * jordanTotientTwo (r / m))
```

2. [`Erdos249257.CyclotomicProjectionOfShadow.mobiusNumerator_mod_cyclotomicEval`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CyclotomicProjectionOfShadow.lean#L310)

```lean
theorem mobiusNumerator_mod_cyclotomicEval
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    cyclotomicEval m ∣
      RadicalMobiusShadow.mobiusNumerator r -
        ArithmeticFunction.moebius m * jordanTotientTwo (r / m)
```

3. [`Erdos249257.CyclotomicProjectionOfShadow.jordanTotientTwo_eq_prod_primeFactors`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CyclotomicProjectionOfShadow.lean#L67)

```lean
theorem jordanTotientTwo_eq_prod_primeFactors
    {n : ℕ} (hn : Squarefree n) :
    jordanTotientTwo n =
      ∏ p ∈ n.primeFactors, ((p : ℤ) ^ 2 - 1)
```

<a id="catalogue-mob-b4-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `cyclotomic_dvd_mobiusNumeratorPolynomial_sub`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L178) (E249_08, line 178), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsAC.lean#L20) (PaperStatementsAC.lean, line 20), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)
- `mobiusNumerator_mod_cyclotomicEval`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L228) (E249_08, line 228), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsAQ.lean#L46) (PaperStatementsAQ.lean, line 46), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)
- `jordanTotientTwo_eq_prod_primeFactors`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L186) (E249_08, line 186), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsAC.lean#L27) (PaperStatementsAC.lean, line 27), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `cyclotomic_dvd_mobiusNumeratorPolynomial_sub`:

```lean
theorem cyclotomic_dvd_mobiusNumeratorPolynomial_sub
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial r -
        Polynomial.C
          (ArithmeticFunction.moebius m * jordanTotientTwo (r / m)) := by sorry
```

Challenge for `mobiusNumerator_mod_cyclotomicEval`:

```lean
theorem mobiusNumerator_mod_cyclotomicEval
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    cyclotomicEval m ∣
      mobiusNumerator r -
        ArithmeticFunction.moebius m * jordanTotientTwo (r / m) := by sorry
```

<a id="catalogue-mob-b8a"></a>

## Proposition 6.41 (Adjoining a prime: new divisors), page 33

> *Let $`r\ge1`$, let $`p\nmid r`$ be prime, and let $`m\mid r`$. Then
> ``` math
> P_{rp}(X)\equiv-P_r(X^p)\pmod{\Phi_{mp}(X)}.
> ```*

The Lean declaration below states this result.

[`Erdos249257.PrimePowerJumpDynamics.cyclotomic_dvd_primeJump_new_fibre`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/PrimePowerJumpDynamics.lean#L281)

```lean
theorem cyclotomic_dvd_primeJump_new_fibre
    {r p m : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic (m * p) ℤ ∣
      mobiusNumeratorPolynomial (r * p) +
        Polynomial.expand ℤ p (mobiusNumeratorPolynomial r)
```

<a id="catalogue-mob-b8a-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `cyclotomic_dvd_primeJump_new_fibre`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L258) (E249_08, line 258), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsAS.lean#L21) (PaperStatementsAS.lean, line 21), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-b8b"></a>

## Proposition 6.42 (Adjoining a prime: existing divisors), page 34

> *Let $`r`$ be squarefree, let $`p\nmid r`$ be prime, and let $`m\mid r`$. For the existing divisors $`m`$, the corresponding identity is
> ``` math
> P_{rp}(X)\equiv(p^2-1)P_r(X)\pmod{\Phi_m(X)}.
> ```*

The Lean declaration below states this result.

[`Erdos249257.PrimePowerJumpDynamics.cyclotomic_dvd_primeJump_old_fibre`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/PrimePowerJumpDynamics.lean#L310)

```lean
theorem cyclotomic_dvd_primeJump_old_fibre
    {r p m : ℕ} (hr : Squarefree r) (hp : p.Prime)
    (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial (r * p) -
        Polynomial.C ((p : ℤ) ^ 2 - 1) *
          mobiusNumeratorPolynomial r
```

<a id="catalogue-mob-b8b-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `cyclotomic_dvd_primeJump_old_fibre`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L265) (E249_08, line 265), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsAS.lean#L27) (PaperStatementsAS.lean, line 27), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-d7"></a>

## Proposition 6.43 (Lambert-series identities), page 34

> *For an arithmetic function $`f`$ for which the sums converge absolutely, write $`L(f)=\sum_{n\ge1}f(n)/(2^n-1)`$. Expanding each geometric series gives
> ``` math
> L(f)=\sum_{m\ge1}\frac{(f*1)(m)}{2^m}.
> ```
> In particular, if $`\alpha=\varphi*\mu`$, then $`\alpha*1=\varphi`$ and $`L(\alpha)=S`$. The table distinguishes this value from four other Lambert-series values. The identity changes the coefficients and the form of the denominator; it does not transfer an irrationality theorem for one weight to another.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.lambertValue_eq_divisor_sum_series`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertDivisorTransform.lean#L42)

```lean
theorem lambertValue_eq_divisor_sum_series (f : ℕ → ℝ)
    (hf : Summable (fun p : ℕ+ × ℕ+ =>
      f (p.1 : ℕ) * ((1 : ℝ) / 2) ^ ((p.1 : ℕ) * (p.2 : ℕ)))) :
    lambertValue f
      = ∑' m : ℕ+, (∑ e ∈ (m : ℕ).divisors, f e) * ((1 : ℝ) / 2) ^ (m : ℕ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.alpha_divisor_sum_eq_totient`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertDivisorTransform.lean#L101)

```lean
theorem alpha_divisor_sum_eq_totient (n : ℕ) :
    ∑ e ∈ n.divisors, ((primWeight e : ℤ) : ℝ) = (Nat.totient n : ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.lambertValue_alpha_eq_totientSeries`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertDivisorTransform.lean#L109)

```lean
theorem lambertValue_alpha_eq_totientSeries :
    lambertValue (fun d => ((primWeight d : ℤ) : ℝ))
      = ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n
```

<a id="catalogue-cert-d7-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `lambertValue_eq_divisor_sum_series`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L74) (E249_08, line 74), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsAE.lean#L258) (PaperStatementsAE.lean, line 258), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)
- `alpha_divisor_sum_eq_totient`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L285) (E249_08, line 285), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsBA.lean#L25) (PaperStatementsBA.lean, line 25), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)
- `lambertValue_alpha_eq_totientSeries`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L289) (E249_08, line 289), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsBA.lean#L42) (PaperStatementsBA.lean, line 42), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-e3"></a>

## Proposition 6.45 (An affine combination annihilates the specified divisor terms), page 35

> *Let $`H\ge1`$ and $`d\mid H`$, with $`d>0`$. The $`d`$th term in the Möbius expansion of $`R_{mH}`$ is $`\mu(d)K_d(mH)`$, where
> ``` math
> K_d(mH)=\frac{mH}{d(2^d-1)}+\frac{2^d}{(2^d-1)^2}.
> ```
> This is affine in $`m`$. Consequently, for any finite family of real coefficients $`c_i`$ and nonnegative integers $`m_i`$ with $`\sum_i c_i=\sum_i c_i m_i=0`$, one has $`\sum_i c_i K_d(m_iH)=0`$.*
> 
> *For the four multipliers $`(1,3,5,15)`$ and coefficients $`(4,-3,-2,1)`$,
> ``` math
> K_d(15H)-3K_d(3H)-2K_d(5H)+4K_d(H)=0.
> ```
> The zeroth and first moments are zero, while the second is $`15^2-3\cdot3^2-2\cdot5^2+4=152`$. Equivalently, $`XY-3X-2Y+4`$ takes the values $`0,0,152`$ at $`(1,1),(3,5),(9,25)`$. This explains the coefficients: they cancel the affine contribution of each divisor of $`H`$, without cancelling a general quadratic function of the multiplier.*
> 
> *For a finite truncation of depth $`L\ge0`$, write
> ``` math
> U=\sum_{j=1}^{L}
>  \bigl(\varphi(15H+j)-3\varphi(3H+j)
>        -2\varphi(5H+j)+4\varphi(H+j)\bigr)2^{L-j}.
> ```
> The difference between $`2^L(R_{15H}-3R_{3H}-2R_{5H}+4R_H)`$ and $`U`$ has absolute value at most $`19H+5L+5`$. Indeed, the error equals
> ``` math
> (R_{15H+L}+4R_{H+L})-(3R_{3H+L}+2R_{5H+L}),
> ```
> and both parenthesised terms lie between $`0`$ and $`19H+5L+5`$ by $`0\le R_n\le n+1`$ for $`n\ge1`$. Thus
> ``` math
> 19H+5L+5<U\bmod2^L<2^L-(19H+5L+5)
> ```
> is sufficient for this four-tail combination to be nonintegral. The bound is derived from these tail enclosures; no optimality for the actual totient tails is asserted. Obtaining such certificates at the required unbounded family of LCM heights remains unproved, as in Theorems 6.60 and 6.52.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.transportResidueKernel_eq_mobiusTermKernel`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L28)

```lean
theorem transportResidueKernel_eq_mobiusTermKernel {d N : ℕ}
    (hd : 0 < d) (hdN : d ∣ N) :
    transportResidueKernel d N
      = ((ArithmeticFunction.moebius d : ℤ) : ℝ) * mobiusTermKernel d N
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel_affine_in_multiplier`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L47)

```lean
theorem mobiusTermKernel_affine_in_multiplier (d H m : ℕ) :
    mobiusTermKernel d (m * H)
      = (m : ℝ) * ((H : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)))
        + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.joint35ConeWindow_eq`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L99)

```lean
theorem joint35ConeWindow_eq (H L : ℕ) :
    joint35ConeWindow H L
      = ∑ j ∈ Finset.range L,
          ((Nat.totient (15 * H + (j + 1)) : ℤ)
            - 3 * (Nat.totient (3 * H + (j + 1)) : ℤ)
            - 2 * (Nat.totient (5 * H + (j + 1)) : ℤ)
            + 4 * (Nat.totient (H + (j + 1)) : ℤ)) * 2 ^ (L - (j + 1))
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.totientTail_enclosure`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L119)

```lean
theorem totientTail_enclosure (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 1
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel_moment_annihilation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L58)

```lean
theorem mobiusTermKernel_moment_annihilation
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (m : ι → ℕ) (d H : ℕ)
    (hzero : ∑ i, c i = 0) (hfirst : ∑ i, c i * (m i : ℝ) = 0) :
    ∑ i, c i * mobiusTermKernel d (m i * H) = 0
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.joint35_mobiusTermKernel_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L76)

```lean
theorem joint35_mobiusTermKernel_zero (d H : ℕ) :
    mobiusTermKernel d (15 * H) - 3 * mobiusTermKernel d (3 * H)
      - 2 * mobiusTermKernel d (5 * H) + 4 * mobiusTermKernel d H = 0
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.joint35_coefficient_moments`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L87)

```lean
theorem joint35_coefficient_moments :
    ((4 : ℝ) + (-3) + (-2) + 1 = 0)
      ∧ ((4 : ℝ) * 1 + (-3) * 3 + (-2) * 5 + 1 * 15 = 0)
      ∧ ((4 : ℝ) * 1 ^ 2 + (-3) * 3 ^ 2 + (-2) * 5 ^ 2 + 1 * 15 ^ 2 = 152)
      ∧ ((1 : ℝ) * 1 - 3 * 1 - 2 * 1 + 4 = 0)
      ∧ ((3 : ℝ) * 5 - 3 * 3 - 2 * 5 + 4 = 0)
      ∧ ((9 : ℝ) * 25 - 3 * 9 - 2 * 25 + 4 = 152)
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.joint35_truncation_error`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L132)

```lean
theorem joint35_truncation_error (H L : ℕ) (hH : 1 ≤ H) :
    (2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)
      = (totientTail (15 * H + L) + 4 * totientTail (H + L))
        - (3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L))
    ∧ |(2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)|
      ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ)
    ∧ (0 ≤ totientTail (15 * H + L) + 4 * totientTail (H + L)
        ∧ totientTail (15 * H + L) + 4 * totientTail (H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ))
    ∧ (0 ≤ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
        ∧ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ))
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.joint35_nonintegral_of_separated_window`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L183)

```lean
theorem joint35_nonintegral_of_separated_window {H L : ℕ} (hH : 1 ≤ H)
    (hlow : ((19 * H + 5 * L + 5 : ℕ) : ℤ) < joint35ConeWindow H L % 2 ^ L)
    (hhigh : joint35ConeWindow H L % 2 ^ L
      < 2 ^ L - ((19 * H + 5 * L + 5 : ℕ) : ℤ)) :
    (totientTail (15 * H) - 3 * totientTail (3 * H)
      - 2 * totientTail (5 * H) + 4 * totientTail H) ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="catalogue-mob-e3-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `transportResidueKernel_eq_mobiusTermKernel`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L118) (E249_09, line 118), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsBE.lean#L68) (PaperStatementsBE.lean, line 68), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `mobiusTermKernel_affine_in_multiplier`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L81) (E249_08, line 81), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsAE.lean#L267) (PaperStatementsAE.lean, line 267), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)
- `joint35ConeWindow_eq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L62) (E249_09, line 62), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L370) (PaperStatementsAX.lean, line 370), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `totientTail_enclosure`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L97) (E249_09, line 97), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L619) (PaperStatementsAX.lean, line 619), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `mobiusTermKernel_moment_annihilation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L87) (E249_08, line 87), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsAE.lean#L272) (PaperStatementsAE.lean, line 272), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)
- `joint35_mobiusTermKernel_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L69) (E249_08, line 69), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsAE.lean#L254) (PaperStatementsAE.lean, line 254), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)
- `joint35_coefficient_moments`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_08/Challenge.lean#L60) (E249_08, line 60), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_08/PaperStatementsAE.lean#L246) (PaperStatementsAE.lean, line 246), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_08.json) (E249_08)
- `joint35_truncation_error`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L79) (E249_09, line 79), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L385) (PaperStatementsAX.lean, line 385), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `joint35_nonintegral_of_separated_window`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L71) (E249_09, line 71), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L378) (PaperStatementsAX.lean, line 378), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-f1"></a>

## Proposition 6.46 (The error under composite dilation), page 36

> *For $`A\subseteq\mathbb N`$ and $`n\ge1`$, let $`d_A(n)=\#\{d\ge1:d\mid n,\ d\in A\}`$. If $`a\in A`$ and $`a,x\ge1`$, then
> ``` math
> d_A(ax)=d_A(x)+\mathbf 1_{a\nmid x}
>        +\#\{d\mid ax:d\in A,\ d\nmid x,\ d\ne a\}.
> ```
> Indeed, partition the divisors of $`ax`$ into those already dividing $`x`$, the possible new divisor $`a`$, and all other new divisors. If every element of $`A`$ is prime, the last set is empty, since a prime dividing $`ax`$ but not $`x`$ must equal the prime $`a`$. For composite $`a`$ it can be nonempty: at $`A=\mathbb N`$, $`a=6`$, $`x=1`$, the other new divisors are $`2`$ and $`3`$.*
> 
> *This is an unweighted counting identity. The associated Lambert series satisfies
> ``` math
> \sum_{\substack{a\in A\\a\ge1}}\frac1{2^a-1}
>  =\sum_{n\ge1}\frac{d_A(n)}{2^n}.
> ```
> For the totient series the required divisor-convolution weight is instead $`\alpha=\varphi*\mu`$, since $`\alpha*1=\varphi`$, as in Proposition 6.43. Weighting all divisors by $`\varphi`$ would give $`\sum_{d\mid n}\varphi(d)=n`$, not $`\varphi(n)`$; already at $`n=2`$ these values are $`2`$ and $`1`$. A weighted version must retain the weights of the new divisors, so it cannot be obtained by substituting $`A=\mathbb N`$ in this unweighted formula. Also $`\alpha(p)=p-2`$ for primes $`p`$, so $`\alpha`$ is unbounded and is not a periodic weight.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L27)

```lean
theorem composite_dilation_divisor_count (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (ha1 : 1 ≤ a) (hx1 : 1 ≤ x) :
    supportCoeff A (a * x) =
      supportCoeff A x + (if a ∣ x then 0 else 1) +
        compositeDilationDefect A a x
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_eq_zero_of_prime_support`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L36)

```lean
theorem composite_dilation_defect_eq_zero_of_prime_support (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (hAprime : ∀ d ∈ A, d.Prime) :
    compositeDilationDefect A a x = 0
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count_prime_support`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L42)

```lean
theorem composite_dilation_divisor_count_prime_support (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (hx1 : 1 ≤ x) (hAprime : ∀ d ∈ A, d.Prime) :
    supportCoeff A (a * x) = supportCoeff A x + (if a ∣ x then 0 else 1)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_univ_six_one`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L49)

```lean
theorem composite_dilation_defect_univ_six_one :
    ((6 * 1 : ℕ).divisors.filter
        fun d => (d ∈ (Set.univ : Set ℕ) ∧ ¬ d ∣ 1 ∧ d ≠ 6)) = ({2, 3} : Finset ℕ)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_univ_six_one_card`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L72)

```lean
theorem composite_dilation_defect_univ_six_one_card :
    compositeDilationDefect (Set.univ : Set ℕ) 6 1 = 2
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.lambert_support_series`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L83)

```lean
theorem lambert_support_series (A : Set ℕ) :
    (∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a) =
      ∑' m : ℕ, (supportCoeff A (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1)
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.lambert_support_series_restricted`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L92)

```lean
theorem lambert_support_series_restricted (A : Set ℕ) :
    (∑' a : ℕ, Set.indicator {a ∈ A | 1 ≤ a} (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a) =
      ∑' m : ℕ, (supportCoeff A (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1)
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_mul_zeta`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L108)

```lean
theorem totient_convolution_weight_mul_zeta (n : ℕ) :
    ∑ e ∈ n.divisors, MersenneLambertLadder.primWeight e = (Nat.totient n : ℤ)
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.sum_divisors_totient_ne_totient`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L114)

```lean
theorem sum_divisors_totient_ne_totient :
    (∀ n : ℕ, ∑ d ∈ n.divisors, Nat.totient d = n) ∧
      (∑ d ∈ (2 : ℕ).divisors, Nat.totient d) = 2 ∧ Nat.totient 2 = 1
```

10. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_prime`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L120)

```lean
theorem totient_convolution_weight_prime {p : ℕ} (hp : p.Prime) :
    MersenneLambertLadder.primWeight p = (p : ℤ) - 2
```

11. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_unbounded`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L125)

```lean
theorem totient_convolution_weight_unbounded :
    ¬ ∃ B : ℕ, ∀ n : ℕ, MersenneLambertLadder.primWeight n ≤ (B : ℤ)
```

12. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_not_periodic`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L131)

```lean
theorem totient_convolution_weight_not_periodic :
    ¬ ∃ p : ℕ, 0 < p ∧
      ∀ n : ℕ, MersenneLambertLadder.primWeight (n + p) =
        MersenneLambertLadder.primWeight n
```

<a id="catalogue-mob-f1-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `composite_dilation_divisor_count`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L157) (E249_09, line 157), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsBD.lean#L20) (PaperStatementsBD.lean, line 20), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `composite_dilation_defect_eq_zero_of_prime_support`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L128) (E249_09, line 128), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAJ.lean#L168) (PaperStatementsAJ.lean, line 168), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `composite_dilation_divisor_count_prime_support`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L164) (E249_09, line 164), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsBD.lean#L26) (PaperStatementsBD.lean, line 26), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `composite_dilation_defect_univ_six_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L133) (E249_09, line 133), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAJ.lean#L172) (PaperStatementsAJ.lean, line 172), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `composite_dilation_defect_univ_six_one_card`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L138) (E249_09, line 138), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAJ.lean#L176) (PaperStatementsAJ.lean, line 176), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `lambert_support_series`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L169) (E249_09, line 169), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsBD.lean#L30) (PaperStatementsBD.lean, line 30), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `lambert_support_series_restricted`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L174) (E249_09, line 174), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsBD.lean#L34) (PaperStatementsBD.lean, line 34), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `totient_convolution_weight_mul_zeta`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L188) (E249_09, line 188), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsBN.lean#L17) (PaperStatementsBN.lean, line 17), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `sum_divisors_totient_ne_totient`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L142) (E249_09, line 142), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAJ.lean#L500) (PaperStatementsAJ.lean, line 500), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `totient_convolution_weight_prime`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L198) (E249_09, line 198), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsBN.lean#L25) (PaperStatementsBN.lean, line 25), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `totient_convolution_weight_unbounded`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L202) (E249_09, line 202), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsBN.lean#L28) (PaperStatementsBN.lean, line 28), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `totient_convolution_weight_not_periodic`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L192) (E249_09, line 192), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsBN.lean#L20) (PaperStatementsBN.lean, line 20), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `totient_convolution_weight_mul_zeta`:

```lean
theorem totient_convolution_weight_mul_zeta (n : ℕ) :
    ∑ e ∈ n.divisors, primWeight e = (Nat.totient n : ℤ) := by sorry
```

Challenge for `totient_convolution_weight_prime`:

```lean
theorem totient_convolution_weight_prime {p : ℕ} (hp : p.Prime) :
    primWeight p = (p : ℤ) - 2 := by sorry
```

Challenge for `totient_convolution_weight_unbounded`:

```lean
theorem totient_convolution_weight_unbounded :
    ¬ ∃ B : ℕ, ∀ n : ℕ, primWeight n ≤ (B : ℤ) := by sorry
```

Challenge for `totient_convolution_weight_not_periodic`:

```lean
theorem totient_convolution_weight_not_periodic :
    ¬ ∃ p : ℕ, 0 < p ∧
      ∀ n : ℕ, primWeight (n + p) =
        primWeight n := by sorry
```

<a id="catalogue-cert-a10"></a>

## Theorem 6.47 (The quantified certificate condition is equivalent to irrationality), page 37

> *$`\big(\forall h:\mathbb{N},\ 0<h \to \forall N_0:\mathbb{N},\ \exists N\ge N_0,\ \exists L,\ \mathcal{C}(h,N,L)\big) \leftrightarrow S\notin\mathbb Q`$. The quantified-condition side is exactly $`\mathcal{C}(h,N,L)`$ quantified as $`\forall h\ge1\ \forall N_0\ge0\ \exists N\ge N_0\ \exists L`$. The universally quantified assertion remains unproved. The equivalence identifies the finite witnesses that suffice; it does not establish their existence beyond every threshold.*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/LcmConeFlatness.lean#L412)

```lean
theorem irrational_totient_series_iff_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ,
        ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L
```

<a id="catalogue-cert-a10-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_totient_series_iff_certificate_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L100) (E249_01, line 100), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAD.lean#L46) (PaperStatementsAD.lean, line 46), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b2"></a>

## Theorem 6.48 (It suffices to use multiples of a period), page 37

> *$`\big(\forall h_0>0,\ \forall N_0,\ \exists m>0,\ \exists N\ge N_0,\ \exists L,\ \mathcal{C}(m\cdot h_0, N, L)\big) \to S\notin\mathbb Q`$. The shift may be any positive multiple of a prescribed period. This enlarges the choice of finite witness: Theorem 6.47 gives the condition with $`m=1`$. Conversely, rationality would make all such tail differences integral after a fixed starting index. The displayed implication therefore makes this quantified condition equivalent to irrationality; its truth remains unproved.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_period_multiple_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L25)

```lean
theorem irrational_of_period_multiple_certificate_supply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.period_multiple_certificate_at_one`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L33)

```lean
theorem period_multiple_certificate_at_one {h₀ N L : ℕ}
    (hcert : certifiedKill h₀ N L) : certifiedKill (1 * h₀) N L
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_period_multiple_integrality`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L55)

```lean
theorem rational_forces_period_multiple_integrality
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ m N : ℕ, N₀ ≤ N →
      totientTail (N + m * h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.period_multiple_certificate_supply_iff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L41)

```lean
theorem period_multiple_certificate_supply_iff :
    (∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
        ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="catalogue-cert-b2-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_of_period_multiple_certificate_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L211) (E249_09, line 211), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAU.lean#L173) (PaperStatementsAU.lean, line 173), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `period_multiple_certificate_at_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L217) (E249_09, line 217), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAU.lean#L333) (PaperStatementsAU.lean, line 333), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `rational_forces_period_multiple_integrality`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L227) (E249_09, line 227), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAU.lean#L379) (PaperStatementsAU.lean, line 379), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `period_multiple_certificate_supply_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L221) (E249_09, line 221), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAU.lean#L336) (PaperStatementsAU.lean, line 336), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b3"></a>

## Theorem 6.49 (The diagonal condition is equivalent to irrationality), page 37

> *$`\big(\forall t_0:\mathbb{N},\ \exists t\ge t_0,\ \exists L,\ \mathcal{C}({H}(t), {H}(t), L)\big) \leftrightarrow S\notin\mathbb Q`$. For a fixed hypothetical rational value, sufficiently large $`t`$ makes both its dyadic denominator and its odd-part period admissible at $`N=h={H}(t)`$. Conversely, irrationality and pointwise completeness supply a witness for every prescribed $`t`$. This is an equivalent condition with one scale parameter; the verified cases $`t\le82`$ do not establish it at arbitrarily large scales.*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_lcm_diagonal_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/LcmConeFlatness.lean#L426)

```lean
theorem irrational_totient_series_iff_lcm_diagonal_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L,
        certifiedKill (periodLcm t) (periodLcm t) L
```

<a id="catalogue-cert-b3-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_totient_series_iff_lcm_diagonal_certificate_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L260) (E249_01, line 260), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsA.lean#L66) (PaperStatementsA.lean, line 66), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b4"></a>

## Lemma 6.50 (Nondivisors in a short LCM window), page 37

> *Let $`t\ge1`$ and $`1\le j<2t`$ be integers. If $`j\nmid H(t)`$, then $`j=p^a>t`$ for a prime $`p`$ and an integer $`a\ge1`$. Indeed, a prime-power divisor of $`j`$ must exceed $`t`$, and $`j<2t`$ leaves no room for a cofactor larger than $`1`$. This classifies the exceptional offsets in this short window; it does not bound their contribution to a weighted sum of totient differences.*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.eq_prime_pow_of_not_dvd_periodLcm`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/LcmDiagonalReduction.lean#L137)

```lean
theorem eq_prime_pow_of_not_dvd_periodLcm {t j : ℕ} (hj : 0 < j) (hlt : j < 2 * t)
    (hnd : ¬ j ∣ periodLcm t) :
    ∃ p k : ℕ, Nat.Prime p ∧ j = p ^ k ∧ t < j
```

<a id="catalogue-cert-b4-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `eq_prime_pow_of_not_dvd_periodLcm`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L238) (E249_09, line 238), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsA.lean#L74) (PaperStatementsA.lean, line 74), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b5"></a>

## Proposition 6.51 (Totient factorisation on an LCM progression), page 37

> *Let $`t\ge1`$, $`j\ge1`$ and $`q\ge0`$ be integers. Suppose $`j\mid H(t)`$ and every prime divisor of $`j`$ also divides $`H(t)/j`$. Then
> ``` math
> \varphi(qH(t)+j)=\varphi(j)\,
>                  \varphi\bigl(q(H(t)/j)+1\bigr).
> ```
> The two factors in $`qH(t)+j=j\bigl(q(H(t)/j)+1\bigr)`$ are coprime: the second is $`1`$ modulo each prime dividing $`j`$. Totient multiplicativity gives the identity. The extra prime-divisor hypothesis is not automatic from $`j\mid H(t)`$; for example, it fails at $`t=j=2`$, where $`\varphi(H(2)+2)=2`$ but the proposed product would be $`1`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.clean_lcm_ray_factorisation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L67)

```lean
theorem clean_lcm_ray_factorisation (t j q : ℕ) (hdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ (periodLcm t / j)) :
    q * periodLcm t + j = j * (q * (periodLcm t / j) + 1) ∧
    Nat.Coprime j (q * (periodLcm t / j) + 1) ∧
    Nat.totient (q * periodLcm t + j) = Nat.totient j * Nat.totient (q * (periodLcm t / j) + 1)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.unclean_lcm_ray_counterexample`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L76)

```lean
theorem unclean_lcm_ray_counterexample :
    2 ∣ periodLcm 2 ∧ Nat.totient (periodLcm 2 + 2) = 2 ∧
    Nat.totient 2 * Nat.totient (periodLcm 2 / 2 + 1) = 1 ∧
    ¬ (∀ p : ℕ, Nat.Prime p → p ∣ 2 → p ∣ (periodLcm 2 / 2))
```

<a id="catalogue-cert-b5-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `clean_lcm_ray_factorisation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L260) (E249_09, line 260), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L180) (PaperStatementsAT.lean, line 180), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `unclean_lcm_ray_counterexample`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L291) (E249_09, line 291), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L247) (PaperStatementsAT.lean, line 247), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b6"></a>

## Theorem 6.52 (Rationality forces tail integrality on an LCM grid), page 37

> *If $`S\in\mathbb Q`$, there is $`t_1\in\mathbb N`$ such that for all $`t\ge t_1`$, $`q\ge1`$ and $`m\ge0`$,
> ``` math
> R_{(q+m)H(t)}-R_{qH(t)}\in\mathbb Z.
> ```
> Thus all tails at positive multiples of $`H(t)`$ have the same fractional part once $`t\ge t_1`$. A certificate at one fixed scale does not refute rationality: the threshold $`t_1`$ depends on the hypothetical rational value. At a shift $`mH(t)>0`$ and basepoint $`qH(t)`$, such a certificate excludes rational values whose reduced denominator divides $`2^{qH(t)}(2^{mH(t)}-1)`$. Certificates at arbitrarily large scales, as required in Theorem 6.53, exclude every hypothetical rational value.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_flatness`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L8)

```lean
theorem lcm_grid_flatness
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      totientTail ((q + m) * periodLcm t) - totientTail (q * periodLcm t)
        ∈ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_fractional_parts`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L15)

```lean
theorem lcm_grid_fractional_parts
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      Int.fract (totientTail ((q + m) * periodLcm t)) =
        Int.fract (totientTail (q * periodLcm t))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.certificate_denominator_exclusion`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L27)

```lean
theorem certificate_denominator_exclusion (r : ℚ) (h N L : ℕ)
    (hcert : certifiedKill h N L) (hden : r.den ∣ 2 ^ N * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_supply_iff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L40)

```lean
theorem lcm_grid_supply_iff :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
        certifiedKill (m * periodLcm t) (q * periodLcm t) L
```

<a id="catalogue-cert-b6-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `lcm_grid_flatness`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L267) (E249_09, line 267), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L205) (PaperStatementsAT.lean, line 205), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `lcm_grid_fractional_parts`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L274) (E249_09, line 274), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L213) (PaperStatementsAT.lean, line 213), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `certificate_denominator_exclusion`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L255) (E249_09, line 255), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L173) (PaperStatementsAT.lean, line 173), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `lcm_grid_supply_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L285) (E249_09, line 285), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L226) (PaperStatementsAT.lean, line 226), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b7"></a>

## Theorem 6.53 (A sufficient nonintegrality condition on the grid), page 38

> *Suppose that for every $`t_0\in\mathbb{N}`$ there are integers $`t\ge t_0`$, $`q\ge1`$, $`m\ge0`$ and $`L\ge0`$ such that
> ``` math
> \mathcal C(mH_t,qH_t,L).
> ```
> Then $`S\notin\mathbb Q`$. Rationality would make the corresponding tail difference integral at every sufficiently large scale, contradicting Proposition 6.18. A successful certificate necessarily has $`m>0`$, since the discrepancy vanishes at shift zero.*
> 
> *The diagonal choice is $`q=m=1`$; consecutive grid points have $`m=1`$, and for $`p\ge2`$ the pair $`(H_t,pH_t)`$ has $`(q,m)=(1,p-1)`$. The diagonal equivalence in Theorem 6.49 also gives the converse from irrationality to the displayed quantified condition; that condition remains unproved.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_supply_iff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L40)

```lean
theorem lcm_grid_supply_iff :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
        certifiedKill (m * periodLcm t) (q * periodLcm t) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_multiplier_positive`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L50)

```lean
theorem lcm_grid_multiplier_positive (t q m L : ℕ)
    (hc : certifiedKill (m * periodLcm t) (q * periodLcm t) L) : 0 < m
```

<a id="catalogue-cert-b7-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `lcm_grid_supply_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L285) (E249_09, line 285), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L226) (PaperStatementsAT.lean, line 226), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)
- `lcm_grid_multiplier_positive`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L281) (E249_09, line 281), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L221) (PaperStatementsAT.lean, line 221), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b8"></a>

## Corollary 6.54 (Equivalent conditions stated without certificates), page 38

> *The series $`S`$ is irrational if and only if
> ``` math
> R_{2H_t}-R_{H_t}\notin\mathbb Z
>  \qquad\text{for arbitrarily large integers }t.
> ```
> Equivalently, for arbitrarily large $`t`$ there are integers $`q\ge1`$ and $`m\ge1`$ with $`R_{(q+m)H_t}-R_{qH_t}\notin\mathbb Z`$. Apply the pointwise equivalence of Theorem 6.19 to Theorems 6.49 and 6.53, respectively. These are equivalent statements of the irrationality question; the required unbounded sets of scales are not established.*

The Lean declarations below together state this result.

1. [`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_all_tail_diffs_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/LcmConeFlatness.lean#L386)

```lean
theorem irrational_totient_series_iff_all_tail_diffs_nonintegral :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ,
        totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`Erdos249257.TotientTailPeriodKiller.periodLcm_diagonal_kill_iff_tail_diff_notMem_int`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/LcmConeFlatness.lean#L439)

```lean
theorem periodLcm_diagonal_kill_iff_tail_diff_notMem_int (t : ℕ) :
    (∃ L, certifiedKill (periodLcm t) (periodLcm t) L) ↔
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)
```

3. [`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_nonintegrality_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/LcmConeFlatness.lean#L451)

```lean
theorem irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

4. [`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonintegrality_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/LcmConeFlatness.lean#L462)

```lean
theorem irrational_totient_series_of_lcm_cone_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m : ℕ, 0 < q ∧
      totientTail (q * periodLcm t + m * periodLcm t) - totientTail (q * periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="catalogue-cert-b8-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_totient_series_iff_all_tail_diffs_nonintegral`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L67) (E249_10, line 67), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAD.lean#L70) (PaperStatementsAD.lean, line 70), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `periodLcm_diagonal_kill_iff_tail_diff_notMem_int`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L56) (E249_10, line 56), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsA.lean#L95) (PaperStatementsA.lean, line 95), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `irrational_totient_series_of_lcm_diagonal_nonintegrality_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L49) (E249_10, line 49), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsA.lean#L87) (PaperStatementsA.lean, line 87), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `irrational_totient_series_of_lcm_cone_nonintegrality_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L243) (E249_09, line 243), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsA.lean#L87) (PaperStatementsA.lean, line 87), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b9a"></a>

## Proposition 6.55 (Soundness of a second-difference certificate), page 38

> *Let $`h,N,L\in\mathbb N`$. If
> ``` math
> \begin{aligned}
>  2(N+2h+L+2)
>  &<\bigl(D(h,N+h,L)-D(h,N,L)\bigr)\bmod2^L\\
>  &<2^L-2(N+2h+L+2),
> \end{aligned}
> ```
> then $`R_{N+2h}-2R_{N+h}+R_N\notin\mathbb Z`$. The numerator is the second difference of the finite windows. Subtracting the two tail identities leaves an error of absolute value at most $`2(N+2h+L+2)`$, which explains the radius in the hypothesis. At $`(h,N)=(1,8)`$, the first-difference test holds at depth $`8`$, whereas the second-difference test fails at every depth $`L\le8`$ and holds at $`L=9`$. A historical probe over $`t\le20`$ reported that the first-difference test was at least as shallow in $`30`$ of $`40`$ sampled cases. This finite comparison is not a uniform ordering of the depths.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.abs_tail_diff_scaled_sub_window_le`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L65)

```lean
theorem abs_tail_diff_scaled_sub_window_le (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + h) - totientTail N) -
        ((windowDiscrepancy h N L : ℤ) : ℝ)| ≤ (N : ℝ) + h + L + 2
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.second_difference_error_bound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L104)

```lean
theorem second_difference_error_bound (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + 2 * h) - 2 * totientTail (N + h) + totientTail N) -
        ((windowDiscrepancy h (N + h) L - windowDiscrepancy h N L : ℤ) : ℝ)| ≤
      2 * ((N : ℝ) + 2 * h + L + 2)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.second_difference_certificate_sound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L121)

```lean
theorem second_difference_certificate_sound {h N L : ℕ}
    (hlow : 2 * ((N : ℤ) + 2 * h + L + 2) <
      (windowDiscrepancy h (N + h) L - windowDiscrepancy h N L) % 2 ^ L)
    (hhigh : (windowDiscrepancy h (N + h) L - windowDiscrepancy h N L) % 2 ^ L <
      2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)) :
    totientTail (N + 2 * h) - 2 * totientTail (N + h) + totientTail N ∉
      Set.range ((↑) : ℤ → ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.second_difference_cell_one_eight`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L136)

```lean
theorem second_difference_cell_one_eight :
    certifiedKill 1 8 8 ∧
      (∀ L : ℕ, L ≤ 8 → ¬ certifiedRank2Kill 1 8 L) ∧
      certifiedRank2Kill 1 8 9
```

<a id="catalogue-cert-b9a-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `abs_tail_diff_scaled_sub_window_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L122) (E249_10, line 122), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L217) (PaperStatementsAT.lean, line 217), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `second_difference_error_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L231) (E249_10, line 231), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAU.lean#L407) (PaperStatementsAU.lean, line 407), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `second_difference_certificate_sound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L222) (E249_10, line 222), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAU.lean#L399) (PaperStatementsAU.lean, line 399), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `second_difference_cell_one_eight`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L216) (E249_10, line 216), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAU.lean#L394) (PaperStatementsAU.lean, line 394), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b10a"></a>

## Theorem 6.56 (A finite-grid condition gives a nonintegral pair), page 39

> *Let $`Q\subseteq\mathbb N_{>0}`$ be finite and nonempty. Suppose that $`B_q<2^L`$ for every $`q\in Q`$ and that
> ``` math
> \forall q_i\in Q\ \exists q_j\in Q,\qquad
>  B_{q_j}<(A_{q_i}-A_{q_j})\bmod2^L.
> ```
> Then $`R_{q_jH}-R_{q_iH}\notin\mathbb Z`$ for some $`q_i,q_j\in Q`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L12)

```lean
theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L36)

```lean
theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="catalogue-cert-b10a-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paperGridNumerator_eq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L275) (E249_10, line 275), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAX.lean#L238) (PaperStatementsAX.lean, line 238), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `finite_grid_nonintegral_pair`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L260) (E249_10, line 260), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAX.lean#L223) (PaperStatementsAX.lean, line 223), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b10b"></a>

## Theorem 6.57 (A sufficient quantified finite-grid condition), page 39

> *Suppose that for every $`t_0`$ there are $`t\ge t_0`$, a depth $`L`$, and a finite nonempty $`Q\subseteq\mathbb N_{>0}`$ such that, with $`H=H_t`$, all the hypotheses of Theorem 6.56 hold. Then $`S\notin\mathbb Q`$. Indeed, rationality would make all tail differences on every sufficiently large LCM grid integral, whereas the finite-grid theorem supplies a nonintegral pair on such a grid. The example above verifies one grid; it does not establish the quantified hypothesis.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L12)

```lean
theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_supply_irrational`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L49)

```lean
theorem finite_grid_supply_irrational
    (hs : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ, ∃ Q : Finset ℕ,
      Q.Nonempty ∧ (∀ q ∈ Q, 0 < q) ∧
      (∀ q ∈ Q, (q * periodLcm t + L + 2 : ℤ) < 2 ^ L) ∧
      paperGridCertificate (periodLcm t) L Q) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="catalogue-cert-b10b-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paperGridNumerator_eq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L275) (E249_10, line 275), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAX.lean#L238) (PaperStatementsAX.lean, line 238), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `finite_grid_supply_irrational`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L267) (E249_10, line 267), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAX.lean#L229) (PaperStatementsAX.lean, line 229), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b12"></a>

## Proposition 6.58 (A finite carry test implies nonintegrality), page 39

> *For each integer $`z`$ with $`|z|\le N+h+1`$, define
> ``` math
> c_z(0)=z,\qquad
>  c_z(i+1)=2c_z(i)-\bigl(\varphi(N+h+i+1)-\varphi(N+i+1)\bigr).
> ```
> Suppose that for every such $`z`$ there is an $`i\le K`$ with
> ``` math
> |c_z(i)|\ge N+i+h+2.
> ```
> Then $`R_{N+h}-R_N\notin\mathbb Z`$. Indeed, an integral value of the tail difference would be one of the $`2(N+h+1)+1`$ initial candidates. Its recurrence would satisfy $`c_z(i)=R_{N+h+i}-R_{N+i}`$ and hence $`|c_z(i)|<N+i+h+2`$ at every step, contrary to the finite test. The excluded strip is open: equality at its boundary already suffices. This proposition proves soundness for a specified $`h,N,K`$; an irrationality argument still needs the quantified family of tests.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_test_sound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCarryCorrespondence.lean#L8)

```lean
theorem finite_carry_test_sound (h N K : ℕ)
    (htest : ∀ z : ℤ, |z| ≤ (N + h + 1 : ℤ) →
      ∃ i : ℕ, i ≤ K ∧ (N + i + h + 2 : ℤ) ≤ |carryOrbit h N z i|) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_candidate_count`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCarryCorrespondence.lean#L22)

```lean
theorem finite_carry_candidate_count (h N : ℕ) :
    (Finset.Icc (-(N + h + 1 : ℤ)) (N + h + 1)).card = 2 * (N + h + 1) + 1
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_true_orbit`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCarryCorrespondence.lean#L27)

```lean
theorem finite_carry_true_orbit (h N : ℕ) (z : ℤ)
    (hz : (z : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N z i : ℝ) = totientTail (N + i + h) - totientTail (N + i) ∧
    |carryOrbit h N z i| < (N + i + h + 2 : ℤ)
```

<a id="catalogue-cert-b12-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `finite_carry_test_sound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L110) (E249_10, line 110), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L153) (PaperStatementsAT.lean, line 153), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `finite_carry_candidate_count`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L282) (E249_10, line 282), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAJ.lean#L121) (PaperStatementsAJ.lean, line 121), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `finite_carry_true_orbit`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L116) (E249_10, line 116), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L160) (PaperStatementsAT.lean, line 160), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-e1"></a>

## Theorem 6.59 (The block norm condition implies irrationality), page 40

> *Suppose that for every integer $`h\ge1`$ and every threshold $`X_0\in\mathbb{N}`$ there are $`X,L\in\mathbb{N}`$ with
> ``` math
> X\ge\max(X_0,1),\qquad 16(2X+h+L+2)\le2^L,
> ```
> and
> ``` math
> \left\lVert\sum_{X\le N<2X}E(h,N,L)\right\rVert\le\frac{21}{25}X.
> ```
> Then $`S\notin\mathbb Q`$. Indeed, the norm bound implies the real-part bound $`\operatorname{Re}\sum E(h,N,L)\le(9/10)X`$. Under the displayed size condition, this latter bound already gives a finite residue certificate, by $`\cos(\pi/8)>9/10`$ and averaging. The argument uses this specific numerical gap; an unspecified saving below $`X`$ is not the stated hypothesis.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_first_harmonic_norm_gap`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L71)

```lean
theorem irrational_of_first_harmonic_norm_gap
    (hgap : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X L : ℕ,
      max X₀ 1 ≤ X ∧ 16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.first_harmonic_re_bound_of_norm_bound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L40)

```lean
theorem first_harmonic_re_bound_of_norm_bound {h X L : ℕ}
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certificate_of_first_harmonic_real_bound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L54)

```lean
theorem exists_certificate_of_first_harmonic_real_bound {h X L : ℕ} (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hre : (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certificate_of_first_harmonic_norm_bound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L61)

```lean
theorem exists_certificate_of_first_harmonic_norm_bound {h X L : ℕ} (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.nine_tenths_lt_cos_pi_div_eight`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L28)

```lean
theorem nine_tenths_lt_cos_pi_div_eight : (9 / 10 : ℝ) < Real.cos (Real.pi / 8)
```

<a id="catalogue-mob-e1-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_of_first_harmonic_norm_gap`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L177) (E249_10, line 177), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L578) (PaperStatementsAT.lean, line 578), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `first_harmonic_re_bound_of_norm_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L139) (E249_10, line 139), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L476) (PaperStatementsAT.lean, line 476), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `exists_certificate_of_first_harmonic_real_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L133) (E249_10, line 133), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L382) (PaperStatementsAT.lean, line 382), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `exists_certificate_of_first_harmonic_norm_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L127) (E249_10, line 127), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L377) (PaperStatementsAT.lean, line 377), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `nine_tenths_lt_cos_pi_div_eight`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L286) (E249_10, line 286), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAJ.lean#L447) (PaperStatementsAJ.lean, line 447), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-e2"></a>

## Theorem 6.60 (A four-tail residue criterion), page 40

> *For nonnegative integers $`H,p,L`$, define the four-tail combination, its finite numerator and its error bound by
> ``` math
> \begin{aligned}
>  J(H,p)&=R_{2pH}-R_{pH}-pR_{2H}+pR_H,\\
>  W(H,p,L)&=D(pH,pH,L)-pD(H,H,L),\\
>  B(H,p,L)&=3pH+(p+1)(L+2).
> \end{aligned}
> ```
> Then
> ``` math
> |2^LJ(H,p)-W(H,p,L)|\le B(H,p,L).
> ```
> Consequently the finite condition
> ``` math
> B(H,p,L)<W(H,p,L)\bmod2^L<2^L-B(H,p,L)
> ```
> implies $`J(H,p)\notin\mathbb Z`$. If, for every $`t_0\in\mathbb N`$, there are $`t\ge t_0`$, $`p\ge1`$ and $`L\ge0`$ satisfying this condition with $`H=H(t)`$, then $`S\notin\mathbb Q`$. Rationality would instead make both diagonal differences in $`J(H(t),p)`$ integral for every sufficiently large $`t`$.*
> 
> *The error bound groups the remainder as
> ``` math
> (R_{2pH+L}+pR_{H+L})-(R_{pH+L}+pR_{2H+L}).
> ```
> Each parenthesis is nonnegative and at most $`B(H,p,L)`$, by $`0\le R_n\le n+2`$. Their difference therefore has absolute value at most $`B(H,p,L)`$. This proves the bound without asserting optimality for the actual totient tails. Primality of $`p`$ is not required by the criterion; a prime $`p`$ is useful when comparing consecutive LCM heights. The checked instance is $`(H,p,L)=(12,5,15)`$, for which $`W(H,p,L)\bmod2^L=18834`$ and $`B(H,p,L)=282`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.four_tail_combination_eq`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L103)

```lean
theorem four_tail_combination_eq (H p : ℕ) :
    primeJumpTailCommutator H p =
      totientTail (2 * p * H) - totientTail (p * H)
        - p * totientTail (2 * H) + p * totientTail H
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.four_tail_window_eq`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L93)

```lean
theorem four_tail_window_eq (H p L : ℕ) :
    windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L =
      primeJumpWindowCommutator H p L
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.windowDiscrepancy_diagonal_eq`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L81)

```lean
theorem windowDiscrepancy_diagonal_eq (M L : ℕ) :
    windowDiscrepancy M M L =
      (windowNumerator (2 * M) L : ℤ) - (windowNumerator M L : ℤ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.four_tail_error_bound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L113)

```lean
theorem four_tail_error_bound (H p L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (2 * p * H) - totientTail (p * H)
          - p * totientTail (2 * H) + p * totientTail H)
        - ((windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L : ℤ) : ℝ)|
      ≤ ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℝ)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.totientTail_bounds`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L129)

```lean
theorem totientTail_bounds (n : ℕ) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 2
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.four_tail_criterion_sound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L152)

```lean
theorem four_tail_criterion_sound {H p L : ℕ}
    (hlow : ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℤ) <
      (windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L) % 2 ^ L)
    (hhigh : (windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L) % 2 ^ L <
      2 ^ L - ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℤ)) :
    totientTail (2 * p * H) - totientTail (p * H)
        - p * totientTail (2 * H) + p * totientTail H ∉ Set.range ((↑) : ℤ → ℝ)
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_four_tail_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L169)

```lean
theorem irrational_of_four_tail_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ p L : ℕ, 1 ≤ p ∧
      ((3 * p * periodLcm t + (p + 1) * (L + 2) : ℕ) : ℤ) <
        (windowDiscrepancy (p * periodLcm t) (p * periodLcm t) L
          - p * windowDiscrepancy (periodLcm t) (periodLcm t) L) % 2 ^ L ∧
      (windowDiscrepancy (p * periodLcm t) (p * periodLcm t) L
          - p * windowDiscrepancy (periodLcm t) (periodLcm t) L) % 2 ^ L <
        2 ^ L - ((3 * p * periodLcm t + (p + 1) * (L + 2) : ℕ) : ℤ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_four_tail_diagonals_integral`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L135)

```lean
theorem rational_forces_four_tail_diagonals_integral
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ p : ℕ, 0 < p →
      (totientTail (2 * periodLcm t) - totientTail (periodLcm t) ∈
          Set.range ((↑) : ℤ → ℝ)) ∧
        (totientTail (2 * (p * periodLcm t)) - totientTail (p * periodLcm t) ∈
          Set.range ((↑) : ℤ → ℝ))
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.four_tail_checked_instance`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L187)

```lean
theorem four_tail_checked_instance :
    (windowDiscrepancy (5 * 12) (5 * 12) 15
        - ((5 : ℕ) : ℤ) * windowDiscrepancy 12 12 15) % 2 ^ 15 = 18834 ∧
      (3 * 5 * 12 + (5 + 1) * (15 + 2) : ℕ) = 282
```

<a id="catalogue-mob-e2-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `four_tail_combination_eq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L150) (E249_10, line 150), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L501) (PaperStatementsAT.lean, line 501), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `four_tail_window_eq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L172) (E249_10, line 172), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L520) (PaperStatementsAT.lean, line 520), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `windowDiscrepancy_diagonal_eq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L241) (E249_10, line 241), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAU.lean#L561) (PaperStatementsAU.lean, line 561), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `four_tail_error_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L165) (E249_10, line 165), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L514) (PaperStatementsAT.lean, line 514), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `totientTail_bounds`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L237) (E249_10, line 237), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAU.lean#L493) (PaperStatementsAU.lean, line 493), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `four_tail_criterion_sound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L156) (E249_10, line 156), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L506) (PaperStatementsAT.lean, line 506), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `irrational_of_four_tail_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L184) (E249_10, line 184), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L584) (PaperStatementsAT.lean, line 584), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `rational_forces_four_tail_diagonals_integral`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L207) (E249_10, line 207), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAU.lean#L355) (PaperStatementsAU.lean, line 355), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `four_tail_checked_instance`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L144) (E249_10, line 144), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L496) (PaperStatementsAT.lean, line 496), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ni-01"></a>

## Proposition 6.61 (An equivalent diagonal nonintegrality condition), page 41

> *The following statements are equivalent:
> ``` math
> S\notin\mathbb Q
>  \quad\Longleftrightarrow\quad
>  \forall a_0\in\mathbb N\ \exists a\ge a_0,\ \Omega_a\notin\mathbb Z.
> ```
> This is an exact reformulation of irrationality, not a weaker theorem about a finite set of scales. The later sufficient conditions seek a finite inequality that establishes the right-hand side.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.irrational_iff_diagonal_orbit_nonintegrality`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L29)

```lean
theorem irrational_iff_diagonal_orbit_nonintegrality :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
        totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) ∉
          Set.range ((↑) : ℤ → ℝ)
```

<a id="prop-ni-01-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_iff_diagonal_orbit_nonintegrality`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L76) (E249_11, line 76), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAT.lean#L580) (PaperStatementsAT.lean, line 580), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ar-07"></a>

## Proposition 6.62 (A sufficient short-window condition), page 41

> *Suppose that for every $`a_0\in\mathbb N`$ there are $`a\ge a_0`$ and $`L<2\cdot2^a`$ with $`\mathcal C(H_{2^a},H_{2^a},L)`$. Then $`S\notin\mathbb Q`$. Writing out the certificate, the required inequality is
> ``` math
> 2H_{2^a}+L+2
>  <D(H_{2^a},H_{2^a},L)\bmod2^L
>  <2^L-(2H_{2^a}+L+2).
> ```
> It places the residue away from both endpoints of the modulus interval. The examples at $`a=4,6`$ establish the bounded statement in Proposition 6.67, not the condition for every threshold. Pointwise completeness allows a sufficiently large depth but does not supply a depth below $`2\cdot2^a`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_short_window_diagonal_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L56)

```lean
theorem irrational_of_short_window_diagonal_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.diagonal_certificate_unfolded`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L40)

```lean
theorem diagonal_certificate_unfolded (a L : ℕ) :
    certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L ↔
      (((2 * periodLcm (2 ^ a) + L + 2 : ℕ) : ℤ) <
          windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L % 2 ^ L ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L % 2 ^ L <
          2 ^ L - ((2 * periodLcm (2 ^ a) + L + 2 : ℕ) : ℤ))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.pointwise_completeness_supplies_some_depth`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L68)

```lean
theorem pointwise_completeness_supplies_some_depth (h N : ℕ)
    (hnon : totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ L : ℕ, certifiedKill h N L
```

<a id="prop-ar-07-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_of_short_window_diagonal_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L97) (E249_11, line 97), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAU.lean#L180) (PaperStatementsAU.lean, line 180), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)
- `diagonal_certificate_unfolded`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L56) (E249_11, line 56), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAT.lean#L365) (PaperStatementsAT.lean, line 365), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)
- `pointwise_completeness_supplies_some_depth`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L109) (E249_11, line 109), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAU.lean#L329) (PaperStatementsAU.lean, line 329), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sep-03"></a>

## Proposition 6.63 (A sufficient approximation condition), page 42

> *Use the prescribed index $`q_a`$ and the error $`\varepsilon_{a,q_a}`$ defined above. Suppose
> ``` math
> \forall a_0\in\mathbb N\ \exists a\ge\max(2,a_0)\ \forall z\in\mathbb Z,
>  \qquad |\Omega_a-z|\ge\frac1{32}+\varepsilon_{a,q_a}.
> ```
> Then $`S\notin\mathbb Q`$. The estimate $`|\Omega_a-\rho_{a,q_a}|<\varepsilon_{a,q_a}`$ implies $`|\rho_{a,q_a}-z|>1/32`$ for every integer $`z`$, and hence the finite residue separation from which the proof derives irrationality. This is a fixed separation condition along an unbounded family of LCM scales. It is not an irrationality-measure theorem for arbitrary rational approximants, and nonintegrality alone does not give the stated margin. The depth is prescribed, not an additional free witness.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_diagonal_orbit_separation_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L145)

```lean
theorem irrational_of_diagonal_orbit_separation_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a : ℕ, max 2 a₀ ≤ a ∧ ∀ z : ℤ,
      (1 : ℝ) / 32 +
          ((2 * periodLcm (2 ^ a) + 2 * prescribedOddIndex a + 3 : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * prescribedOddIndex a + 1) ≤
        |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) - (z : ℝ)|) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.oddGuarded_depth_eq_prescribed`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L80)

```lean
theorem oddGuarded_depth_eq_prescribed (a : ℕ) :
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * prescribedOddIndex a + 1
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.abs_orbit_sub_rawApprox_lt`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L98)

```lean
theorem abs_orbit_sub_rawApprox_lt (a q : ℕ) :
    |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) -
        ((windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
            diagonalWindowIncrement (2 ^ a) (2 * q + 2) : ℤ) : ℝ) / (2 : ℝ) ^ (2 * q + 1)| <
      ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * q + 1)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.rawApprox_separation_of_orbit_separation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L112)

```lean
theorem rawApprox_separation_of_orbit_separation {a q : ℕ}
    (hsep : ∀ z : ℤ,
      (1 : ℝ) / 32 + ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * q + 1) ≤
        |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) - (z : ℝ)|)
    (z : ℤ) :
    (1 : ℝ) / 32 <
      |((windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
            diagonalWindowIncrement (2 ^ a) (2 * q + 2) : ℤ) : ℝ) / (2 : ℝ) ^ (2 * q + 1) -
        (z : ℝ)|
```

<a id="prop-sep-03-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_of_diagonal_orbit_separation_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L83) (E249_11, line 83), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAT.lean#L601) (PaperStatementsAT.lean, line 601), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)
- `oddGuarded_depth_eq_prescribed`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L261) (E249_11, line 261), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAX.lean#L278) (PaperStatementsAX.lean, line 278), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)
- `abs_orbit_sub_rawApprox_lt`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L254) (E249_11, line 254), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAX.lean#L141) (PaperStatementsAX.lean, line 141), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)
- `rawApprox_separation_of_orbit_separation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L265) (E249_11, line 265), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAX.lean#L374) (PaperStatementsAX.lean, line 374), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-te-04"></a>

## Proposition 6.64 (A sufficient upper-endpoint separation), page 42

> *Let $`a,J,K,m\in\mathbb N`$, $`a\ge8`$, and $`H=H(2^a)`$. Assume
> ``` math
> J+K+(a+6)<2\cdot2^a.
> ```
> Define the finite condition
> ``` math
> \begin{aligned}
>  \mathcal G_a(J,K,m)\quad:\Longleftrightarrow\quad
>  &m\le K,\qquad 2H+J+K+2<2^m,\\
>  &D(H,H+J,K)\bmod2^m\le2^m-(2H+J+K+2).
>  \end{aligned}
> ```
> Then $`\mathcal G_a(J,K,m)`$ implies $`R_{2H+J}-R_{H+J}\notin\mathbb Z`$. In particular, irrationality follows if for every $`a_0`$ there are $`a\ge\max(a_0,8)`$ and $`K,m`$ satisfying $`K+(a+6)<2\cdot2^a`$ and $`\mathcal G_a(0,K,m)`$.*
> 
> *The sign theorem forces an integral tail to give a residue in the upper endpoint interval. This one-sided test excludes that interval; it does not require a lower residue bound. Both the sign-range hypothesis and the strict modulus bound are essential premises of this implication. The required unbounded family is not established.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.upper_endpoint_condition_iff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L29)

```lean
theorem upper_endpoint_condition_iff (a J K m : ℕ) :
    ActualLcmTopEdgeResidueGap a J K m ↔
      (m ≤ K ∧
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.upper_endpoint_gap_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L38)

```lean
theorem upper_endpoint_gap_nonintegral {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a J K m) :
    totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J) ∉
      Set.range ((↑) : ℤ → ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.integral_tail_forces_upper_endpoint_residue`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L50)

```lean
theorem integral_tail_forces_upper_endpoint_residue {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hroom : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ K)
    {d : ℤ}
    (hd : (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J)) :
    (2 : ℤ) ^ K - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ K ∧
      windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ K <
        (2 : ℤ) ^ K
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_upper_endpoint_gap_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L66)

```lean
theorem irrational_of_upper_endpoint_gap_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a K m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
      K + (a + 6) < 2 * 2 ^ a ∧ ActualLcmTopEdgeResidueGap a 0 K m) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="prop-te-04-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `upper_endpoint_condition_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L114) (E249_11, line 114), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAU.lean#L523) (PaperStatementsAU.lean, line 523), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)
- `upper_endpoint_gap_nonintegral`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L122) (E249_11, line 122), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAU.lean#L532) (PaperStatementsAU.lean, line 532), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)
- `integral_tail_forces_upper_endpoint_residue`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L64) (E249_11, line 64), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAT.lean#L567) (PaperStatementsAT.lean, line 567), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)
- `irrational_of_upper_endpoint_gap_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L103) (E249_11, line 103), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAU.lean#L193) (PaperStatementsAU.lean, line 193), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-te-05"></a>

## Proposition 6.65 (Relations among the sufficient conditions), page 42

> *The sufficient conditions do not form a single linear chain. The proved implications are
> ``` math
> \begin{aligned}
>  \text{guarded odd-prefix band}
>  &\ \Longleftrightarrow\ \text{guarded centred-magnitude bound},\\
>  \text{guarded centred-magnitude bound}
>  &\ \Longrightarrow\ \text{flexible centred-magnitude bound},\\
>  \text{flexible centred-magnitude bound}
>  &\ \Longrightarrow\ \text{adjacent-suffix band}
>    \ \Longrightarrow\ \text{upper-endpoint test}.
>  \end{aligned}
> ```
> There is also a separate sufficient argument: terminal dominance and flexible centred magnitude each imply the two-sided exclusion in Proposition 6.66, which implies diagonal nonintegrality. These statements refer to the quantified versions, with the bounds on $`a,q`$ and the depth retained. The detailed conditions and sources appear in Proposition 9.14. No reverse implication between terminal dominance and flexible magnitude is asserted, and none of the required unbounded families is proved here.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.te_chain_relations`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L80)

```lean
theorem te_chain_relations :
    (PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
        PowerTwoActualFinalTopEdgeMagnitudeSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTopEdgeMagnitudeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoAdjacentSuffixMidbandSupply) ∧
      (PowerTwoAdjacentSuffixMidbandSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoFlexibleActualTerminalDominanceSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply →
        PowerTwoActualLcmOrbitNonintegralitySupply)
```

<a id="prop-te-05-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `te_chain_relations`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_11/Challenge.lean#L276) (E249_11, line 276), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_11/PaperStatementsAX.lean#L447) (PaperStatementsAX.lean, line 447), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_11.json) (E249_11)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-te-06"></a>

## Proposition 6.66 (An exact endpoint formula), page 43

> *Let $`a,q\in\mathbb N`$, $`a\ge8`$, and $`H=H(2^a)`$. Assume
> ``` math
> 2q+2+(a+6)<2\cdot2^a,\qquad 2(H+q+2)\le4^q.
> ```
> If $`z\in\mathbb Z`$ and $`z=\Omega_a`$, then
> ``` math
> 2u_{a,q}=\delta_{2^a}(2q+2)-c_{H,H,z}(2q+1).
> ```
> Consequently either of the inequalities
> ``` math
> \begin{aligned}
>  2u_{a,q}&\le\delta_{2^a}(2q+2)-(2H+2q+3),\\
>  \delta_{2^a}(2q+2)&\le2u_{a,q}
>  \end{aligned}
> ```
> is sufficient for $`\Omega_a\notin\mathbb Z`$. Under integrality the recurrence equals a positive tail difference strictly smaller than $`2H+2q+3`$, and the identity rules out both displayed inequalities. The identity is exact; the resulting nonintegrality criterion is only sufficient. Its converse is not asserted.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.endpoint_identity`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L142)

```lean
theorem endpoint_identity {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    {z : ℤ}
    (hz : (z : ℝ) = totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) :
    2 * actualOddHalfCenteredLift a q =
      diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
        carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.integral_carry_strictly_between`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L158)

```lean
theorem integral_carry_strictly_between {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    {z : ℤ}
    (hz : (z : ℝ) = totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) :
    0 < carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) ∧
      carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) <
        ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℤ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.endpoint_criterion_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L187)

```lean
theorem endpoint_criterion_nonintegral {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hesc : 2 * actualOddHalfCenteredLift a q ≤
          diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
            ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℤ) ∨
        diagonalWindowIncrement (2 ^ a) (2 * q + 2) ≤
          2 * actualOddHalfCenteredLift a q) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) ∉
      Set.range ((↑) : ℤ → ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.oddHalfCenteredLift_spec`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L116)

```lean
theorem oddHalfCenteredLift_spec {a : ℕ} (q : ℕ) (ha : 2 ≤ a) :
    Even (windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
        diagonalWindowIncrement (2 ^ a) (2 * q + 2)) ∧
      Int.ModEq ((4 : ℤ) ^ q) (actualOddHalfCenteredLift a q)
        ((windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
          diagonalWindowIncrement (2 ^ a) (2 * q + 2)) / 2) ∧
      -((4 : ℤ) ^ q) < 2 * actualOddHalfCenteredLift a q ∧
      2 * actualOddHalfCenteredLift a q ≤ (4 : ℤ) ^ q
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.centeredLift_range`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L106)

```lean
theorem centeredLift_range {A M : ℤ} (hM : 0 < M) :
    -M < 2 * actualCenteredLift A M ∧ 2 * actualCenteredLift A M ≤ M
```

<a id="prop-te-06-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `endpoint_identity`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L123) (E249_12, line 123), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAX.lean#L300) (PaperStatementsAX.lean, line 300), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)
- `integral_carry_strictly_between`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L82) (E249_12, line 82), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAT.lean#L548) (PaperStatementsAT.lean, line 548), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)
- `endpoint_criterion_nonintegral`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L111) (E249_12, line 111), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAX.lean#L287) (PaperStatementsAX.lean, line 287), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)
- `oddHalfCenteredLift_spec`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L133) (E249_12, line 133), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAX.lean#L388) (PaperStatementsAX.lean, line 388), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)
- `centeredLift_range`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L148) (E249_12, line 148), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAY.lean#L70) (PaperStatementsAY.lean, line 70), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sk-02"></a>

## Proposition 6.67 (A sufficient extension of the examples through exponent 6), page 43

> *The supplied finite result is
> ``` math
> \forall a_0\le6\ \exists a,L\in\mathbb N,\qquad
>  a\ge a_0,\quad L<2\cdot2^a,\quad
>  \mathcal C(H_{2^a},H_{2^a},L).
> ```
> The witnesses at $`(a,L)=(4,23)`$ and $`(6,93)`$ give this bounded family. A witness with $`a\ge7`$ would extend the verified range, but any finite extension would still leave the assertion for arbitrarily large thresholds in Proposition 6.62 unproved.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.short_window_diagonal_through_six`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L161)

```lean
theorem short_window_diagonal_through_six (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.short_window_diagonal_witnesses`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L169)

```lean
theorem short_window_diagonal_witnesses :
    certifiedKill (periodLcm (2 ^ 4)) (periodLcm (2 ^ 4)) 23 ∧ (23 : ℕ) < 2 * 2 ^ 4 ∧
      certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 ∧ (93 : ℕ) < 2 * 2 ^ 6
```

<a id="prop-sk-02-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `short_window_diagonal_through_six`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L174) (E249_12, line 174), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAU.lean#L437) (PaperStatementsAU.lean, line 437), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)
- `short_window_diagonal_witnesses`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L179) (E249_12, line 179), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAU.lean#L443) (PaperStatementsAU.lean, line 443), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-fr-01"></a>

## Proposition 6.68 (A sufficient extremal-order condition), page 43

> *Let $`H\ge1`$ and $`j\ge0`$. If
> ``` math
> \varphi(2H+j)<\min\{\varphi(H+j),\varphi(3H+j)\},
> ```
> then
> ``` math
> \varphi(3H+j)-2\varphi(2H+j)+\varphi(H+j)>0.
> ```
> If instead the middle value is strictly larger than both outer values, the displayed second difference is negative. In each case the claim follows by adding the two strict differences. No lower bound on their sizes is needed.*
> 
> *For $`H=H_{2^a}`$, this reduces nonvanishing of one second difference to an ordering of three totient values. For a prescribed $`j`$, the remaining question is whether either strict ordering occurs for arbitrarily large $`a`$. The elementary implication does not establish those occurrences.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_pos`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L27)

```lean
theorem extremal_order_curvature_pos {H j : ℕ} (hH : 1 ≤ H)
    (hmin : Nat.totient (2 * H + j) < min (Nat.totient (H + j)) (Nat.totient (3 * H + j))) :
    0 < (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_neg`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L36)

```lean
theorem extremal_order_curvature_neg {H j : ℕ} (hH : 1 ≤ H)
    (hleft : Nat.totient (H + j) < Nat.totient (2 * H + j))
    (hright : Nat.totient (3 * H + j) < Nat.totient (2 * H + j)) :
    (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) < 0
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L45)

```lean
theorem extremal_order_curvature_ne_zero {H j : ℕ} (hH : 1 ≤ H)
    (hextremal : MiddleRankTotientExtremal H j) :
    (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) ≠ 0
```

<a id="prop-fr-01-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `extremal_order_curvature_pos`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L211) (E249_12, line 211), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAJ.lean#L309) (PaperStatementsAJ.lean, line 309), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)
- `extremal_order_curvature_neg`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L205) (E249_12, line 205), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAJ.lean#L304) (PaperStatementsAJ.lean, line 304), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)
- `extremal_order_curvature_ne_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L200) (E249_12, line 200), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAJ.lean#L300) (PaperStatementsAJ.lean, line 300), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-cp-06"></a>

## Proposition 6.69 (A directed certificate condition), page 43

> *For fixed $`h,N\in\mathbb{N}`$, a depth $`L\in\mathbb{N}`$ satisfying
> ``` math
> N+L+2\ \le\ D(h,N,L)\bmod2^L
>  \ \le\ 2^L-(N+h+L+2)
> ```
> exists if and only if $`R_{N+h}-R_N\notin\mathbb Z`$. The endpoint inequalities are non-strict.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_iff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L59)

```lean
theorem directed_certificate_iff (h N : ℕ) :
    (∃ L : ℕ,
        ((N : ℤ) + L + 2) ≤ windowDiscrepancy h N L % (2 : ℤ) ^ L ∧
          windowDiscrepancy h N L % (2 : ℤ) ^ L ≤
            (2 : ℤ) ^ L - ((N : ℤ) + h + L + 2)) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_example`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L71)

```lean
theorem directed_certificate_example :
    periodLcm 3 = 6 ∧
      windowDiscrepancy 6 6 6 = 270 ∧
      windowDiscrepancy 6 6 6 % (2 : ℤ) ^ 6 = 14 ∧
      directedCertifiedKill 6 6 6 ∧
      (∀ L : ℕ, L ≤ 6 → ¬ certifiedKill 6 6 L) ∧
      certifiedKill 6 6 7
```

<a id="prop-cp-06-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `directed_certificate_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L74) (E249_12, line 74), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAT.lean#L373) (PaperStatementsAT.lean, line 373), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)
- `directed_certificate_example`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L65) (E249_12, line 65), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAT.lean#L365) (PaperStatementsAT.lean, line 365), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-cp-07"></a>

## Proposition 6.70 (A sufficient condition at the prescribed mod-four pulses), page 44

> *Suppose that for every positive integer $`h`$ and every $`B\in\mathbb N`$ there are a prime $`p>B`$ and $`K\in\mathbb N`$ such that
> ``` math
> \varphi(p+4h)-\varphi(p)\equiv2\pmod4
> ```
> and every integer $`z`$ with $`|z|\le p+4h+1`$ and $`z\equiv2\pmod4`$ has an index $`0\le i\le K`$ satisfying
> ``` math
> |c_{4h,p,z}(i)|\ge p+i+4h+2.
> ```
> Then $`S\notin\mathbb Q`$. Under a hypothetical eventual period $`h`$, the proved congruence argument at a sufficiently large such prime forces $`R_{p+4h}-R_p`$ to be an integer in the tested residue class. The finite test excludes every candidate in that class, a contradiction.*
> 
> *The mod-four congruence is supplied by Proposition 6.91; exclusion at the same prime is not. Restricting to $`2\pmod4`$ retains one residue class out of four, not necessarily exactly one quarter of the candidates in a finite interval. The quantifier over every bound $`B`$ cannot be replaced by one fixed prime for each $`h`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_modFour_pulse_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L105)

```lean
theorem irrational_of_modFour_pulse_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4] ∧
      ∃ K : ℕ, ∀ z : ℤ, |z| ≤ ((p + 4 * h + 1 : ℕ) : ℤ) → z ≡ (2 : ℤ) [ZMOD 4] →
        ∃ i : ℕ, i ≤ K ∧
          ((p + i + 4 * h + 2 : ℕ) : ℤ) ≤ |carryOrbit (4 * h) p z i|) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_pulse_class_integrality`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L88)

```lean
theorem rational_forces_pulse_class_integrality
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ B : ℕ, ∀ p : ℕ, B < p →
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4] →
      ∃ z : ℤ, (z : ℝ) = totientTail (p + 4 * h) - totientTail p ∧
        z ≡ (2 : ℤ) [ZMOD 4]
```

<a id="prop-cp-07-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_of_modFour_pulse_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L157) (E249_12, line 157), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAU.lean#L153) (PaperStatementsAU.lean, line 153), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)
- `rational_forces_pulse_class_integrality`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_12/Challenge.lean#L166) (E249_12, line 166), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_12/PaperStatementsAU.lean#L374) (PaperStatementsAU.lean, line 374), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_12.json) (E249_12)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-a10"></a>

## Proposition 6.71 (The full quantified condition), page 44

> *``` math
> \big(\forall h\ge 1,\ \forall N_0,\ \exists N\ge N_0,\ \exists L,\ \mathcal{C}\ h\ N\ L\big)
> \iff S\notin\mathbb Q.
> ```
> This is exactly the quantifier structure $`\forall h\ge1\ \forall N_0\ \exists N\ge N_0\ \exists L\ \mathcal{C}(h,N,L)`$. The quantified condition is not supplied here. The equivalence specifies exactly what a residue-based proof would need beyond the finite examples.*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/LcmConeFlatness.lean#L412)

```lean
theorem irrational_totient_series_iff_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ,
        ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L
```

<a id="prop-a10-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_totient_series_iff_certificate_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L100) (E249_01, line 100), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAD.lean#L46) (PaperStatementsAD.lean, line 46), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
