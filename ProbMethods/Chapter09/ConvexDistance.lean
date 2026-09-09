import ProbMethods.Chapter09.Talagrand
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# §9.5 — Lemma 9.5.12, convex distance dominates Euclidean distance

Zhao, *Probabilistic Methods in Combinatorics*, Lemma 9.5.12: for `A ⊆ [0,1]ⁿ` and
`x ∈ [0,1]ⁿ`,

    dist(x, conv A) ≤ d_T(x, A),

where `d_T` is Talagrand's convex distance (`PMC.convexDist`) and `dist` is Euclidean. This is
the step that converts Theorem 9.5.11 — the convex-distance concentration inequality, task
#49 — into the *geometric* statements of §9.5: Corollary 9.5.13 for convex sets, and 9.5.6 and
9.5.8 for convex Lipschitz functions. Without it, 9.5.11 has no consumers.

## The route

The inequality is linear-programming duality, and both halves of it are in Mathlib.

* **The pointwise bound.** For any `α : Fin n → ℝ` and any `y ∈ [0,1]ⁿ`,

      |(x - y) · α| ≤ ∑ᵢ |αᵢ| |xᵢ - yᵢ| ≤ ∑_{i : xᵢ ≠ yᵢ} |αᵢ|,

  the second step because `|xᵢ - yᵢ| ≤ 1` on the cube and the terms with `xᵢ = yᵢ` vanish. The
  right-hand side is `PMC.wHamDist |α| x y`, so taking the infimum over `y ∈ A` gives
  `|(x - y)·α| ≥` nothing yet — the infimum has to be taken on the *left*, which is why the
  next step is needed.
* **The nearest point.** `conv A` is compact (`Set.Finite.isCompact_convexHull` for finite `A`),
  hence complete, so `exists_norm_eq_iInf_of_complete_convex` supplies a nearest point `z`, and
  `norm_eq_iInf_iff_real_inner_le_zero` characterises it by `⟪x - z, y - z⟫ ≤ 0` for every
  `y ∈ conv A`. That gives `(x - y) · (x - z) ≥ ‖x - z‖²`, so at
  `α = |x - z| / ‖x - z‖` — componentwise absolute value, which has the same norm and is
  nonnegative, as `PMC.unitWeights` requires — every `y ∈ A` has
  `wHamDist α x y ≥ (x - y)·α ≥ ‖x - z‖`. Taking the infimum over `y ∈ A` and then the
  supremum over `α` gives `‖x - z‖ ≤ d_T(x, A)`.

Both Mathlib lemmas live in an inner product space, so the proof will want to transport along
`EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ)`; the statement below avoids that by writing the
Euclidean distance as `√(∑ (xᵢ - zᵢ)²)` and asking for the nearest point explicitly, which is
also the form Corollary 9.5.13 consumes. For finite `A` the infimum is attained, so the
existential form is equivalent to the `Metric.infDist` one.
-/

open Finset

namespace PMC

section ConvexDistance

variable {n : ℕ}

/-- **Lemma 9.5.12.** Some point of the convex hull of `A` is within Talagrand's convex
distance `d_T(x, A)` of `x` in Euclidean distance. -/
theorem exists_mem_convexHull_dist_le (hn : 0 < n) (A : Finset (Fin n → ℝ)) (hA : A.Nonempty)
    (hA01 : ∀ y ∈ A, ∀ i, y i ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin n → ℝ) (hx01 : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ z ∈ convexHull ℝ (↑A : Set (Fin n → ℝ)),
      Real.sqrt (∑ i, (x i - z i) ^ 2) ≤ convexDist A x := by
  sorry

end ConvexDistance

end PMC
