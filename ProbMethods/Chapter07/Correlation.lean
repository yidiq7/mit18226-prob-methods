import ProbMethods.Weighted

/-!
# §7.2 — Correlation of monotone properties

Zhao, *Probabilistic Methods in Combinatorics*, §7.2.

The form of Harris–FKG that applications use: two *upward-closed* properties of a random
subset are positively correlated. With `α := Sym2 V` this is "monotone graph properties
correlate in `G(n, p)`".

The inequality itself is upstream (Mathlib's `fkg`, reached here through
`PMC.pweight_fkg`); what this file adds is the passage from monotone functions to monotone
*events*, and one concrete graph property.
-/

open Finset

namespace PMC

section Monotone

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Monotone events are positively correlated** under a product measure (Zhao, §7.2).

For upward-closed `A` and `B`, the weight of `A ∧ B` is at least the product of the
weights. Immediate from `PMC.pweight_fkg` applied to the indicator functions, which are
monotone exactly because the properties are upward-closed. -/
theorem pweight_correlate (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (A B : Finset α → Prop) [DecidablePred A] [DecidablePred B]
    (hA : ∀ S T : Finset α, S ⊆ T → A S → A T)
    (hB : ∀ S T : Finset α, S ⊆ T → B S → B T) :
    (∑ S ∈ (univ : Finset (Finset α)).filter A, pweight p S)
        * ∑ S ∈ (univ : Finset (Finset α)).filter B, pweight p S
      ≤ ∑ S ∈ (univ : Finset (Finset α)).filter (fun S => A S ∧ B S), pweight p S := by
  classical
  set f : Finset α → ℝ := fun S => if A S then 1 else 0 with hf
  set g : Finset α → ℝ := fun S => if B S then 1 else 0 with hg
  have hf0 : (0 : Finset α → ℝ) ≤ f := by
    intro S; rw [hf]; by_cases h : A S <;> simp [h]
  have hg0 : (0 : Finset α → ℝ) ≤ g := by
    intro S; rw [hg]; by_cases h : B S <;> simp [h]
  have hfm : Monotone f := by
    intro S T hST
    rw [hf]
    by_cases h : A S
    · simp [h, hA S T hST h]
    · by_cases h' : A T <;> simp [h, h']
  have hgm : Monotone g := by
    intro S T hST
    rw [hg]
    by_cases h : B S
    · simp [h, hB S T hST h]
    · by_cases h' : B T <;> simp [h, h']
  have hmA : wmean (pweight p) f
      = ∑ S ∈ (univ : Finset (Finset α)).filter A, pweight p S := by
    rw [wmean, Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hf]
    by_cases h : A S <;> simp [h]
  have hmB : wmean (pweight p) g
      = ∑ S ∈ (univ : Finset (Finset α)).filter B, pweight p S := by
    rw [wmean, Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hg]
    by_cases h : B S <;> simp [h]
  have hmAB : wmean (pweight p) (fun S => f S * g S)
      = ∑ S ∈ (univ : Finset (Finset α)).filter (fun S => A S ∧ B S), pweight p S := by
    rw [wmean, Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hf, hg]
    by_cases h : A S <;> by_cases h' : B S <;> simp [h, h']
  have h := pweight_fkg p hp0 hp1 hf0 hg0 hfm hgm
  rw [hmA, hmB, hmAB] at h
  exact h

end Monotone

/-- Containing a triangle is an upward-closed property of the edge set. -/
theorem hasTriangle_mono {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (hEF : E ⊆ F) (h : HasTriangle E) : HasTriangle F := by
  obtain ⟨t, ht, htE⟩ := h
  exact ⟨t, ht, htE.trans hEF⟩

/-- **Containing a triangle correlates with any monotone property** in `G(n, p)`
(Zhao, §7.2).

A concrete instance of `PMC.pweight_correlate`: the two events "the random graph contains a
triangle" and any upward-closed `B` are positively correlated. -/
theorem pweight_hasTriangle_correlate {V : Type*} [Fintype V] [DecidableEq V]
    (p : Sym2 V → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (B : Finset (Sym2 V) → Prop) [DecidablePred B]
    (hB : ∀ E F : Finset (Sym2 V), E ⊆ F → B E → B F) :
    (∑ E ∈ (univ : Finset (Finset (Sym2 V))).filter HasTriangle, pweight p E)
        * ∑ E ∈ (univ : Finset (Finset (Sym2 V))).filter B, pweight p E
      ≤ ∑ E ∈ (univ : Finset (Finset (Sym2 V))).filter
          (fun E => HasTriangle E ∧ B E), pweight p E :=
  pweight_correlate p hp0 hp1 HasTriangle B hasTriangle_mono hB

end PMC
