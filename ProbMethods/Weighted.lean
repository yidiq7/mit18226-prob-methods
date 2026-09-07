import ProbMethods.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Weighted counting over a finite space

Shared infrastructure for the results whose distribution is not uniform. Chapters 1 and 2
are all uniform counting; from §3.1 onwards the parameter is a real number, and the device
that carries those arguments is a finite *weighted* sum rather than measure theory.

The point is that over a finite space an expectation is a finite sum, so nothing here needs
`MeasureTheory` or `PMF`. Weights are an arbitrary nonnegative `w : Ω → ℝ`; the results
that need `∑ w = 1` take it as a hypothesis rather than baking it in, since the Bernoulli
weights of §3.1 and the `G(n, p)` weights of Chapter 4 both arrive as products and are
easier to normalise at the point of use.

## Main definitions

* `PMC.wmean` — the weighted mean of a real random variable.
* `PMC.wvar` — its weighted variance, about its own weighted mean.

## Main results

* `PMC.wchebyshev` — Chebyshev's inequality. Mathlib's Chebyshev is stated for
  `MeasureTheory`/`ProbabilityTheory` and does not apply to a bare finite weighted sum, so
  this is proved here. Chapters 4 (§4.5, §4.6), 5 and 9 all want it.
-/

open Finset

namespace PMC

section Weighted

variable {Ω : Type*} [Fintype Ω]

/-- The weighted mean of `X` against weights `w`. -/
def wmean (w : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, w ω * X ω

/-- The weighted variance of `X`, taken about its own weighted mean. -/
def wvar (w : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, w ω * (X ω - wmean w X) ^ 2

lemma wvar_nonneg {w : Ω → ℝ} (X : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : 0 ≤ wvar w X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (sq_nonneg _)

/-- **Chebyshev's inequality**, over a finite weighted space.

The total weight of the points where `X` deviates from its weighted mean by at least `a` is
at most `wvar w X / a ^ 2`. Stated multiplicatively so no division or positivity side
condition on the variance is needed. -/
theorem wchebyshev (w : Ω → ℝ) (X : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) {a : ℝ} (ha : 0 < a) :
    (∑ ω ∈ univ.filter fun ω => a ≤ |X ω - wmean w X|, w ω) * a ^ 2 ≤ wvar w X := by
  have hstep : ∀ ω ∈ univ.filter fun ω => a ≤ |X ω - wmean w X|,
      w ω * a ^ 2 ≤ w ω * (X ω - wmean w X) ^ 2 := by
    intro ω hω
    rw [mem_filter] at hω
    refine mul_le_mul_of_nonneg_left ?_ (hw ω)
    calc a ^ 2 ≤ |X ω - wmean w X| ^ 2 := pow_le_pow_left₀ ha.le hω.2 2
      _ = (X ω - wmean w X) ^ 2 := sq_abs _
  calc (∑ ω ∈ univ.filter fun ω => a ≤ |X ω - wmean w X|, w ω) * a ^ 2
      = ∑ ω ∈ univ.filter fun ω => a ≤ |X ω - wmean w X|, w ω * a ^ 2 := Finset.sum_mul _ _ _
    _ ≤ ∑ ω ∈ univ.filter fun ω => a ≤ |X ω - wmean w X|,
          w ω * (X ω - wmean w X) ^ 2 := Finset.sum_le_sum hstep
    _ ≤ ∑ ω, w ω * (X ω - wmean w X) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun ω _ _ => ?_
        exact mul_nonneg (hw ω) (sq_nonneg _)
    _ = wvar w X := rfl

/-- The complementary form: the weight of the points *within* `a` of the mean is at least
`total - wvar / a ^ 2`. This is the direction §4.6 uses. -/
theorem wchebyshev' (w : Ω → ℝ) (X : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) {a : ℝ} (ha : 0 < a) :
    (∑ ω, w ω) * a ^ 2 - wvar w X
      ≤ (∑ ω ∈ univ.filter fun ω => |X ω - wmean w X| < a, w ω) * a ^ 2 := by
  have h := wchebyshev w X hw ha
  have hfar : (univ.filter fun ω => ¬ |X ω - wmean w X| < a)
      = univ.filter fun ω => a ≤ |X ω - wmean w X| := by
    ext ω; simp [not_lt]
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset Ω)
    (fun ω => |X ω - wmean w X| < a) w
  rw [hfar] at hsplit
  have hT : (∑ ω, w ω) * a ^ 2
      = (∑ ω ∈ univ.filter fun ω => |X ω - wmean w X| < a, w ω) * a ^ 2
        + (∑ ω ∈ univ.filter fun ω => a ≤ |X ω - wmean w X|, w ω) * a ^ 2 := by
    rw [← add_mul, hsplit]
  linarith

end Weighted

end PMC
