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

/-- **First-order optimality of a nearest point**, in coordinates: if `z` minimises the squared
Euclidean distance to `x` over a convex set containing `y`, then `(x - z) · (y - z) ≤ 0`. Moving
from `z` towards `y` by `t = a / (a + b)`, with `a` the inner product and `b = ‖y - z‖²`, would
otherwise get strictly closer to `x`. -/
private lemma sum_mul_sub_nonpos_of_nearest {s : Set (Fin n → ℝ)} (hs : Convex ℝ s)
    {x y z : Fin n → ℝ} (hz : z ∈ s) (hy : y ∈ s)
    (hmin : ∀ w ∈ s, ∑ i, (x i - z i) ^ 2 ≤ ∑ i, (x i - w i) ^ 2) :
    ∑ i, (x i - z i) * (y i - z i) ≤ 0 := by
  by_contra! ha
  set a := ∑ i, (x i - z i) * (y i - z i) with ha_def
  set b := ∑ i, (y i - z i) ^ 2 with hb_def
  have hb : 0 ≤ b := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hab : 0 < a + b := by linarith
  set t := a / (a + b)
  have ht0 : 0 < t := div_pos ha hab
  have ht1 : t ≤ 1 := div_le_one_of_le₀ (by linarith) hab.le
  have hta : t * (a + b) = a := div_mul_cancel₀ a hab.ne'
  have hw := hmin _ (hs.add_smul_sub_mem hz hy ⟨ht0.le, ht1⟩)
  have hexpand : ∑ i, (x i - (z + t • (y - z)) i) ^ 2
      = ∑ i, (x i - z i) ^ 2 - 2 * t * a + t ^ 2 * b := by
    rw [ha_def, hb_def, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hexpand] at hw
  have h1 : 0 ≤ t * (t * b - 2 * a) := by
    have : t * (t * b - 2 * a) = t ^ 2 * b - 2 * t * a := by ring
    linarith
  have h2 : 0 ≤ t * b - 2 * a := (mul_nonneg_iff_of_pos_left ht0).mp h1
  have h3 : t * a + t * b = a := (mul_add t a b).symm.trans hta
  linarith [mul_pos ht0 ha]

/-- **The pointwise bound.** If `x` and `y` differ by at most `1` in each coordinate, then
`(x - y) · v` is at most the Hamming distance from `x` to `y` weighted by `|v|`. -/
private lemma sum_mul_le_wHamDist_abs {x y v : Fin n → ℝ} (hxy : ∀ i, |x i - y i| ≤ 1) :
    ∑ i, (x i - y i) * v i ≤ wHamDist (fun i => |v i|) x y := by
  rw [wHamDist, Finset.sum_filter]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : x i = y i
  · simp [h]
  · rw [if_pos h]
    calc (x i - y i) * v i ≤ |(x i - y i) * v i| := le_abs_self _
      _ = |x i - y i| * |v i| := abs_mul _ _
      _ ≤ 1 * |v i| := mul_le_mul_of_nonneg_right (hxy i) (abs_nonneg _)
      _ = |v i| := one_mul _

/-- The distance to a nonempty set of real points under a unit weight vector is at most `n`,
each weight being at most `1`. This bounds the supremum defining `PMC.convexDist` over `ℝ`, where
`PMC.bddAbove_convexDist_image` does not apply because it assumes `[Fintype β]`. -/
private lemma wDistToSet_real_le_card {α : Fin n → ℝ} (hα : α ∈ unitWeights n)
    {A : Finset (Fin n → ℝ)} (hA : A.Nonempty) (x : Fin n → ℝ) : wDistToSet α A x ≤ n := by
  obtain ⟨y, hy⟩ := hA
  rw [wDistToSet, dif_pos ⟨y, hy⟩]
  refine (Finset.inf'_le _ hy).trans ?_
  have hle : ∀ i, α i ≤ 1 := fun i => (sq_le_one_iff₀ (hα.1 i)).mp <| by
    rw [← hα.2]
    exact Finset.single_le_sum (f := fun j => α j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
  rw [wHamDist]
  calc ∑ i ∈ (univ : Finset (Fin n)).filter fun i => x i ≠ y i, α i
      ≤ ∑ i, α i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => hα.1 i
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hle i
    _ = n := by simp

/-- **Lemma 9.5.12.** Some point of the convex hull of `A` is within Talagrand's convex
distance `d_T(x, A)` of `x` in Euclidean distance. -/
theorem exists_mem_convexHull_dist_le (hn : 0 < n) (A : Finset (Fin n → ℝ)) (hA : A.Nonempty)
    (hA01 : ∀ y ∈ A, ∀ i, y i ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin n → ℝ) (hx01 : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ z ∈ convexHull ℝ (↑A : Set (Fin n → ℝ)),
      Real.sqrt (∑ i, (x i - z i) ^ 2) ≤ convexDist A x := by
  have hcont : ContinuousOn (fun w : Fin n → ℝ => ∑ i, (x i - w i) ^ 2)
      (convexHull ℝ (↑A : Set (Fin n → ℝ))) := by fun_prop
  obtain ⟨z, hz, hmin⟩ := (A.finite_toSet.isCompact_convexHull ℝ).exists_isMinOn
    (Finset.coe_nonempty.mpr hA).convexHull hcont
  refine ⟨z, hz, ?_⟩
  have hbdd : BddAbove ((fun α => wDistToSet α A x) '' unitWeights n) := by
    refine ⟨n, ?_⟩
    rintro _ ⟨α, hα, rfl⟩
    exact wDistToSet_real_le_card hα hA x
  set S := ∑ i, (x i - z i) ^ 2 with hS
  rcases (Real.sqrt_nonneg S).eq_or_lt with hD | hD
  · rw [← hD]
    obtain ⟨α, hα⟩ := unitWeights_nonempty hn
    have hα0 : 0 ≤ wDistToSet α A x := by
      rw [wDistToSet, dif_pos hA]
      exact Finset.le_inf' hA _ fun y _ => Finset.sum_nonneg fun i _ => hα.1 i
    exact hα0.trans (le_csSup hbdd ⟨α, hα, rfl⟩)
  have hS0 : 0 < S := Real.sqrt_pos.mp hD
  set D := Real.sqrt S
  have hDD : D * D = S := Real.mul_self_sqrt hS0.le
  have hα : (fun i => |x i - z i| / D) ∈ unitWeights n := by
    refine ⟨fun i => div_nonneg (abs_nonneg _) hD.le, ?_⟩
    simp only [div_pow, sq_abs]
    rw [← Finset.sum_div, ← hS, sq D, hDD]
    exact div_self hS0.ne'
  have hle : ∀ y ∈ A, D ≤ wHamDist (fun i => |x i - z i| / D) x y := by
    intro y hy
    have hfo : ∑ i, (x i - z i) * (y i - z i) ≤ 0 :=
      sum_mul_sub_nonpos_of_nearest (convex_convexHull ℝ _) hz
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr hy)) (isMinOn_iff.mp hmin)
    have hcube : ∀ i, |x i - y i| ≤ 1 := fun i => abs_le.mpr
      ⟨by linarith [(hx01 i).1, (hA01 y hy i).2], by linarith [(hx01 i).2, (hA01 y hy i).1]⟩
    have hbound := sum_mul_le_wHamDist_abs (v := fun i => x i - z i) hcube
    have hsplit : ∑ i, (x i - y i) * (x i - z i)
        = S - ∑ i, (x i - z i) * (y i - z i) := by
      rw [hS, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hdiv : wHamDist (fun i => |x i - z i| / D) x y
        = wHamDist (fun i => |x i - z i|) x y / D := by
      simp only [wHamDist, Finset.sum_div]
    rw [hdiv, le_div_iff₀ hD, hDD]
    linarith
  have hDα : D ≤ wDistToSet (fun i => |x i - z i| / D) A x := by
    rw [wDistToSet, dif_pos hA]
    exact Finset.le_inf' hA _ hle
  exact hDα.trans (le_csSup hbdd ⟨_, hα, rfl⟩)

end ConvexDistance

end PMC
