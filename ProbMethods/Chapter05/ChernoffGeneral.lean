import ProbMethods.MeasureBridge

/-!
# §5.0 — the Chernoff bound for arbitrary independent bounded variables (Theorem 5.0.5)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 5.0.5: if `X = ∑ Xᵢ` with the `Xᵢ`
independent, mean zero and taking values in `[-1, 1]`, then for `λ ≥ 0`

    P(X ≥ λ √n) ≤ e^{-λ²/2}.

**This was previously recorded here as out of reach**, on the ground that the sample space is a
product of continua and so the counting framework does not reach it — "the first place where the
finite approach genuinely runs out". That reading was half right and half wrong: the finite
framework indeed does not reach it, but **Mathlib does**, and the statement is a short derivation
from two upstream lemmas:

* `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` — a mean-zero variable in
  an interval of length `2` is sub-Gaussian with parameter `1` (Hoeffding's lemma);
* `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` — a sum of independent sub-Gaussian
  variables satisfies `P(∑ ≥ ε) ≤ exp(-ε²/(2 ∑ cᵢ))`.

At `cᵢ = 1` the second gives `exp(-ε²/(2n))`, and `ε = λ√n` turns that into `e^{-λ²/2}` — the
notes' constant exactly, with no slack.

So the entry belongs in the *upstream* column, not the deferred one. The lesson is the same one
Chapter 7 taught with FKG and Chapter 4 with Weierstrass: **check Mathlib before recording a
result as unreachable**, and record the bridge when it is there. Unlike those two, this one was
recorded as blocked for a structural reason that sounded convincing.

This file states the theorem over an arbitrary probability space, which is how the notes state
it; it needs no finite weight and does not use `PMC.wmean`. `ProbMethods/MeasureBridge.lean` is
imported only to keep the measure-theoretic imports in one place.
-/

open MeasureTheory ProbabilityTheory

namespace PMC

section ChernoffGeneral

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι]

/-- **Theorem 5.0.5.** For independent mean-zero variables in `[-1,1]`,
`P(∑ Xᵢ ≥ ε) ≤ exp(-ε²/(2n))`. -/
theorem measure_sum_ge_le_of_mem_Icc {X : ι → Ω → ℝ} (hindep : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i, X i ω} ≤ Real.exp (-ε ^ 2 / (2 * Fintype.card ι)) := by
  have hsubG : ∀ i ∈ (Finset.univ : Finset ι), HasSubgaussianMGF (X i) 1 μ := by
    intro i _
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hmeas i) (hbdd i) (hmean i)
    have hc : ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal) = 1 := by
      refine NNReal.coe_injective ?_
      push_cast
      rw [Real.norm_eq_abs]
      norm_num
    rwa [hc] at h
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep hsubG hε
  rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h

/-- **Theorem 5.0.5, as the notes write it**: `P(∑ Xᵢ ≥ λ√n) ≤ e^{-λ²/2}`. -/
theorem measure_sum_ge_sqrt_le_of_mem_Icc {X : ι → Ω → ℝ} (hindep : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    {lam : ℝ} (hlam : 0 ≤ lam) (hn : 0 < Fintype.card ι) :
    μ.real {ω | lam * Real.sqrt (Fintype.card ι) ≤ ∑ i, X i ω}
      ≤ Real.exp (-(lam ^ 2) / 2) := by
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (Fintype.card ι) := Real.sqrt_nonneg _
  have hε : (0 : ℝ) ≤ lam * Real.sqrt (Fintype.card ι) := mul_nonneg hlam hsqrt
  have h := measure_sum_ge_le_of_mem_Icc hindep hmeas hbdd hmean hε
  refine le_trans h (le_of_eq ?_)
  have hsq : (lam * Real.sqrt (Fintype.card ι)) ^ 2 = lam ^ 2 * Fintype.card ι := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hnR)]
  rw [hsq]
  field_simp

end ChernoffGeneral

end PMC
