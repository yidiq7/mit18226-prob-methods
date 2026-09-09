import ProbMethods.Chapter09.BoundedDifferences
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# §9.5 — Talagrand's inequality: the convex distance

Theorem 9.5.11: for `A ⊆ Ω₁ × ⋯ × Ωₙ` with a product probability measure,

    P(x ∈ A) · P(d_T(x, A) ≥ t) ≤ e^{-t²/4},

where `d_T` is Talagrand's **convex distance**. Its combinatorial applications are the reason
the inequality matters: unlike the bounded differences inequality, whose bound degrades as
`e^{-t²/n}`, this one has no `n` in the exponent.

This file sets up the distance and its basic properties, and states the inequality. **The
definitions are where the design choices are**, so they are recorded here rather than left to
whoever proves the analytic core:

* the sample space is the uniform product `Fin n → β`, as in §9.1 — not the fully general
  product of distinct factors with an arbitrary product measure. The notes' applications
  reach that generality by padding coordinates, the same device `Chapter09/
  ChromaticConcentration.lean` uses for graphs;
* `PMC.wHamDist` is the weighted Hamming distance and `PMC.wDistToSet` its distance to a set,
  defined to be `0` on the empty set so that it is total;
* `PMC.convexDist` is the supremum of `PMC.wDistToSet α` over the unit sphere of nonnegative
  weights, as a `sSup` — the set is nonempty and bounded above by `√n`
  (`PMC.wDistToSet_le_sqrt`), so the supremum is a genuine real number.

The inequality itself (`PMC.card_mul_card_filter_convexDist_le`) is published as a task. Its
proof is an induction on the number of coordinates using Hölder's inequality, together with
the elementary but delicate fact that `inf_{0≤λ≤1} e^{(1-λ)²/4} r^{-λ} ≤ 2 - r` for
`r ∈ (0,1]`; the notes do not prove it either.
-/

open Finset

namespace PMC

section Talagrand

variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β] {n : ℕ}

/-- The weighted Hamming distance: the total weight of the coordinates where `x` and `y`
differ. -/
def wHamDist (α : Fin n → ℝ) (x y : Fin n → β) : ℝ :=
  ∑ i ∈ (univ : Finset (Fin n)).filter fun i => x i ≠ y i, α i

lemma wHamDist_self (α : Fin n → ℝ) (x : Fin n → β) : wHamDist α x x = 0 := by
  rw [wHamDist, Finset.filter_false_of_mem, Finset.sum_empty]
  intro i _
  simp

lemma wHamDist_nonneg {α : Fin n → ℝ} (hα : ∀ i, 0 ≤ α i) (x y : Fin n → β) :
    0 ≤ wHamDist α x y :=
  Finset.sum_nonneg fun i _ => hα i

/-- The weighted distance from `x` to a set, taken to be `0` on the empty set. -/
noncomputable def wDistToSet (α : Fin n → ℝ) (A : Finset (Fin n → β)) (x : Fin n → β) : ℝ :=
  if h : A.Nonempty then A.inf' h (fun y => wHamDist α x y) else 0

lemma wDistToSet_nonneg {α : Fin n → ℝ} (hα : ∀ i, 0 ≤ α i) (A : Finset (Fin n → β))
    (x : Fin n → β) : 0 ≤ wDistToSet α A x := by
  rw [wDistToSet]
  by_cases h : A.Nonempty
  · rw [dif_pos h]
    obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_inf' h (fun y => wHamDist α x y)
    rw [hy]
    exact wHamDist_nonneg hα x y
  · rw [dif_neg h]

lemma wDistToSet_eq_zero_of_mem {α : Fin n → ℝ} (hα : ∀ i, 0 ≤ α i)
    {A : Finset (Fin n → β)} {x : Fin n → β} (hx : x ∈ A) : wDistToSet α A x = 0 := by
  have h : A.Nonempty := ⟨x, hx⟩
  rw [wDistToSet, dif_pos h]
  refine le_antisymm ?_ ?_
  · have := Finset.inf'_le (fun y => wHamDist α x y) hx
    rwa [wHamDist_self] at this
  · obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_inf' h (fun y => wHamDist α x y)
    rw [hy]
    exact wHamDist_nonneg hα x y

/-- **The weighted distance is at most `√n`** for a unit weight vector, by Cauchy–Schwarz on
the coordinates where the two points differ. This is what makes the supremum defining the
convex distance a real number. -/
lemma wDistToSet_le_sqrt {α : Fin n → ℝ} (hα : ∀ i, 0 ≤ α i) (hnorm : ∑ i, α i ^ 2 = 1)
    (A : Finset (Fin n → β)) (x : Fin n → β) : wDistToSet α A x ≤ Real.sqrt n := by
  classical
  have hbound : ∀ y : Fin n → β, wHamDist α x y ≤ Real.sqrt n := by
    intro y
    set D : Finset (Fin n) := (univ : Finset (Fin n)).filter fun i => x i ≠ y i with hD
    have hcs : (∑ i ∈ D, α i) ^ 2 ≤ #D * ∑ i ∈ D, α i ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hle : ∑ i ∈ D, α i ^ 2 ≤ 1 := by
      rw [← hnorm]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => sq_nonneg _)
    have hcard : (#D : ℝ) ≤ n := by
      have := Finset.card_le_card (Finset.filter_subset (fun i => x i ≠ y i)
        (univ : Finset (Fin n)))
      rw [card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    have hsq : (∑ i ∈ D, α i) ^ 2 ≤ (n : ℝ) := by
      calc (∑ i ∈ D, α i) ^ 2 ≤ #D * ∑ i ∈ D, α i ^ 2 := hcs
        _ ≤ (n : ℝ) * 1 := by
            refine mul_le_mul hcard hle (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
            positivity
        _ = (n : ℝ) := by ring
    have hnn : 0 ≤ ∑ i ∈ D, α i := Finset.sum_nonneg fun i _ => hα i
    rw [wHamDist, ← hD]
    calc ∑ i ∈ D, α i = Real.sqrt ((∑ i ∈ D, α i) ^ 2) := by
          rw [Real.sqrt_sq hnn]
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hsq
  rw [wDistToSet]
  by_cases h : A.Nonempty
  · rw [dif_pos h]
    obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_inf' h (fun y => wHamDist α x y)
    rw [hy]
    exact hbound y
  · rw [dif_neg h]
    positivity

/-- The nonnegative unit weight vectors. -/
def unitWeights (n : ℕ) : Set (Fin n → ℝ) :=
  {α | (∀ i, 0 ≤ α i) ∧ (∑ i, α i ^ 2) = 1}

/-- **Talagrand's convex distance**: the largest weighted Hamming distance from `x` to `A`
over all nonnegative unit weight vectors. -/
noncomputable def convexDist (A : Finset (Fin n → β)) (x : Fin n → β) : ℝ :=
  sSup ((fun α => wDistToSet α A x) '' unitWeights n)

lemma unitWeights_nonempty (hn : 0 < n) : (unitWeights n).Nonempty := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨fun i => if i = (0 : Fin n) then 1 else 0, fun i => by positivity, ?_⟩
  have hterm : ∀ i : Fin n, (if i = (0 : Fin n) then (1 : ℝ) else 0) ^ 2
      = if i = (0 : Fin n) then (1 : ℝ) else 0 := by
    intro i
    by_cases h : i = 0 <;> simp [h]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp

lemma bddAbove_convexDist_image (A : Finset (Fin n → β)) (x : Fin n → β) :
    BddAbove ((fun α => wDistToSet α A x) '' unitWeights n) := by
  refine ⟨Real.sqrt n, ?_⟩
  rintro r ⟨α', hα', rfl⟩
  exact wDistToSet_le_sqrt hα'.1 hα'.2 A x

lemma convexDist_nonneg (hn : 0 < n) (A : Finset (Fin n → β)) (x : Fin n → β) :
    0 ≤ convexDist A x := by
  obtain ⟨α, hα⟩ := unitWeights_nonempty hn
  have hmem : wDistToSet α A x ∈ (fun α => wDistToSet α A x) '' unitWeights n := ⟨α, hα, rfl⟩
  exact le_trans (wDistToSet_nonneg hα.1 A x)
    (le_csSup (bddAbove_convexDist_image A x) hmem)

/-- The convex distance vanishes on `A`. -/
lemma convexDist_eq_zero_of_mem (hn : 0 < n) {A : Finset (Fin n → β)} {x : Fin n → β}
    (hx : x ∈ A) : convexDist A x = 0 := by
  refine le_antisymm ?_ (convexDist_nonneg hn A x)
  obtain ⟨α₀, hα₀⟩ := unitWeights_nonempty hn
  refine csSup_le ⟨_, ⟨α₀, hα₀, rfl⟩⟩ ?_
  rintro r ⟨α, hα, rfl⟩
  exact le_of_eq (wDistToSet_eq_zero_of_mem hα.1 hx)

/-- **Theorem 9.5.11 (Talagrand's inequality, general form).** In counting form:

    #A · #{x : d_T(x, A) ≥ t} ≤ |β|^{2n} · e^{-t²/4},

which is `P(x ∈ A) P(d_T(x,A) ≥ t) ≤ e^{-t²/4}` after dividing by `|β|^{2n}`. -/
theorem card_mul_card_filter_convexDist_le (hn : 0 < n) (A : Finset (Fin n → β)) {t : ℝ}
    (ht : 0 ≤ t) :
    (#A : ℝ) * #((univ : Finset (Fin n → β)).filter fun x => t ≤ convexDist A x)
      ≤ ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t ^ 2) / 4) := by
  sorry

end Talagrand

end PMC
