import ProbMethods.Weighted
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# §9.1 — Hoeffding's lemma, in finite form

§9.1's bounded differences inequality (Theorem 9.1.1) is the one result of Chapter 9 that
lives naturally in this project's finite framework: the sample space is a product of finite
sets, the martingale is the sequence of partial averages over the remaining coordinates, and
nothing needs `MeasureTheory`.

Its analytic input is **Hoeffding's lemma**: a mean-zero random variable confined to an
interval of length `b - a` has moment generating function at most `exp(λ²(b-a)²/8)`. That is
what this file states.

Mathlib has Hoeffding's lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`),
but only for measures, and its proof runs through tilted measures and the cumulant generating
function. Using it here would mean building a bridge from a finite weight to a `Measure`,
which is a project of its own; proving the finite statement directly is the alternative, and
either route is acceptable.

The constant matters: `λ²(b-a)²/8` is what makes the bounded differences inequality come out
with the notes' `exp(-2λ²/∑cᵢ²)`. A cruder MGF bound would give a factor of four worse in the
exponent and so would *not* prove Theorem 9.1.1 as stated.
-/

open Finset

namespace PMC

section Hoeffding

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Hoeffding's lemma.** If `Z` is confined to `[a, b]` and has mean zero under the weight
`w`, then its moment generating function satisfies

    E[exp (λ Z)] ≤ exp (λ² (b-a)² / 8).

The classical proof: convexity of `exp` on `[a, b]` gives, pointwise,
`exp (λ z) ≤ ((b - z)/(b - a)) exp (λ a) + ((z - a)/(b - a)) exp (λ b)`; averaging and using
`E[Z] = 0` leaves `(b exp(λa) - a exp(λb))/(b - a)`, which is `exp (L(h))` for
`h = λ(b - a)`, `p = -a/(b - a)` and `L(h) = -p h + log (1 - p + p exp h)`; and
`L(h) ≤ h²/8` because `L(0) = L'(0) = 0` and `L'' ≤ 1/4`.

The `L'' ≤ 1/4` step is the one piece of real calculus, `p(1-p) ≤ 1/4` in disguise. -/
theorem wmean_exp_le_of_mem_Icc {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (Z : Ω → ℝ) {a b : ℝ} (hab : ∀ ω, Z ω ∈ Set.Icc a b) (hmean : wmean w Z = 0) (lam : ℝ) :
    wmean w (fun ω => Real.exp (lam * Z ω)) ≤ Real.exp (lam ^ 2 * (b - a) ^ 2 / 8) := by
  sorry

end Hoeffding

end PMC
