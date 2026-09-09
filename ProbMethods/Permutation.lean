import ProbMethods.Weighted
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Combinatorics.Enumerative.Bell

/-!
# The uniform random permutation

§6.5's applications of the lopsided local lemma live on a sample space of *permutations*
rather than a product, so `PMC.unifProd` does not reach them: the coordinates `σ i` are far
from independent — they are distinct.

This file sets up the uniform weight `PMC.unifPerm` on `Equiv.Perm α` and the counting facts
the lopsided local lemma needs from it. Everything rests on one device: **composing with a
transposition**. `σ ↦ Equiv.swap t t' * σ` is a bijection between the permutations sending
`i` to `t` and those sending `i` to `t'`, which gives both the exact probability
`P(σ i = t) = 1 / |α|` and, in a form that survives extra constraints, the negative
correlation `P(σ i = i ∧ D) ≤ P(σ i = i) P(D)` for the derangement-type events `D`.

The negative correlation is the point: fixed-point events are *not* independent, so the
ordinary local lemma does not apply to them, and this is the smallest instance of Theorem
6.5.5's random injection model.
-/

open Finset

namespace PMC

section Permutation

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The uniform weight on permutations of `α`. -/
noncomputable def unifPerm (α : Type*) [Fintype α] [DecidableEq α] : Equiv.Perm α → ℝ :=
  fun _ => 1 / Fintype.card (Equiv.Perm α)

lemma unifPerm_apply (σ : Equiv.Perm α) :
    unifPerm α σ = 1 / Fintype.card (Equiv.Perm α) := rfl

lemma unifPerm_nonneg (σ : Equiv.Perm α) : 0 ≤ unifPerm α σ := by
  rw [unifPerm_apply]; positivity

lemma card_perm_pos : 0 < Fintype.card (Equiv.Perm α) := Fintype.card_pos

lemma sum_unifPerm : ∑ σ : Equiv.Perm α, unifPerm α σ = 1 := by
  have hpos : (0 : ℝ) < Fintype.card (Equiv.Perm α) := by
    exact_mod_cast card_perm_pos (α := α)
  rw [Finset.sum_congr rfl fun σ _ => unifPerm_apply σ, Finset.sum_const, card_univ,
    nsmul_eq_mul, mul_one_div, div_self (ne_of_gt hpos)]

lemma wprob_unifPerm (A : Finset (Equiv.Perm α)) :
    wprob (unifPerm α) A = #A / Fintype.card (Equiv.Perm α) := by
  rw [wprob, Finset.sum_congr rfl fun σ _ => unifPerm_apply σ, Finset.sum_const,
    nsmul_eq_mul, mul_one_div]

/-! ### Composing with a transposition -/

/-- The permutations sending `i` to `t` are as many as those sending `i` to `t'`: compose
with the transposition of `t` and `t'`. -/
theorem card_filter_apply_eq (i t t' : α) :
    #((univ : Finset (Equiv.Perm α)).filter fun σ => σ i = t)
      = #((univ : Finset (Equiv.Perm α)).filter fun σ => σ i = t') := by
  apply Finset.card_bij (fun σ _ => Equiv.swap t t' * σ)
  · intro σ hσ
    rw [mem_filter] at hσ ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [Equiv.Perm.mul_apply, hσ.2, Equiv.swap_apply_left]
  · intro σ _ τ _ h
    exact mul_left_cancel h
  · intro τ hτ
    rw [mem_filter] at hτ
    refine ⟨Equiv.swap t t' * τ, ?_, ?_⟩
    · rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [Equiv.Perm.mul_apply, hτ.2, Equiv.swap_apply_right]
    · rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

/-- A permutation sends `i` to a given point with probability `1 / |α|`. -/
theorem wprob_unifPerm_apply_eq [Nonempty α] (i t : α) :
    wprob (unifPerm α) ((univ : Finset (Equiv.Perm α)).filter fun σ => σ i = t)
      = 1 / Fintype.card α := by
  have hcard : Fintype.card α * #((univ : Finset (Equiv.Perm α)).filter fun σ => σ i = t)
      = Fintype.card (Equiv.Perm α) := by
    have hfib : #(univ : Finset (Equiv.Perm α))
        = ∑ s : α, #((univ : Finset (Equiv.Perm α)).filter fun σ => σ i = s) :=
      Finset.card_eq_sum_card_fiberwise (fun σ _ => mem_univ (σ i))
    rw [card_univ] at hfib
    rw [hfib, Finset.sum_congr rfl fun s _ => card_filter_apply_eq i s t,
      Finset.sum_const, card_univ, smul_eq_mul]
  have hPpos : (0 : ℝ) < Fintype.card (Equiv.Perm α) := by
    exact_mod_cast card_perm_pos (α := α)
  have h : (Fintype.card α : ℝ) * #((univ : Finset (Equiv.Perm α)).filter fun σ => σ i = t)
      = Fintype.card (Equiv.Perm α) := by exact_mod_cast hcard
  have hAne : (#((univ : Finset (Equiv.Perm α)).filter fun σ => σ i = t) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact absurd h.symm (ne_of_gt hPpos)
  rw [wprob_unifPerm, ← h, mul_comm, ← div_div, div_self hAne]

/-! ### Negative correlation for fixed-point events -/

/-- The permutations with no fixed point inside `S`. -/
def derangeOn (S : Finset α) : Finset (Equiv.Perm α) :=
  (univ : Finset (Equiv.Perm α)).filter fun σ => ∀ j ∈ S, σ j ≠ j

lemma mem_derangeOn {S : Finset α} {σ : Equiv.Perm α} :
    σ ∈ derangeOn S ↔ ∀ j ∈ S, σ j ≠ j := by
  rw [derangeOn, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- **The counting core of negative correlation.** Among the permutations with no fixed point
in `S`, those fixing `i` are no more numerous than those sending `i` to any given `t` —
*provided* `i ∉ S`, so that `i`'s own constraint is not one of the ones being preserved.

Composing with `Equiv.swap i t` is the injection. It is well defined because the only way it
could create a fixed point at some `j ∈ S` is `σ j = Equiv.swap i t j`, which forces `j = t`
and `σ t = i`; but `σ i = i` already, so injectivity of `σ` rules that out. This is Theorem
6.5.5's argument for single-edge matchings, with `Equiv.swap i t` in the role of the
permutation `σ` of `Y` that sends `F₀` to `T`. -/
theorem card_filter_fix_le {i : α} {S : Finset α} (hi : i ∉ S) (t : α) :
    #((derangeOn S).filter fun σ => σ i = i) ≤ #((derangeOn S).filter fun σ => σ i = t) := by
  apply Finset.card_le_card_of_injOn (fun σ => Equiv.swap i t * σ)
  · intro σ hσ
    rw [mem_coe, mem_filter, mem_derangeOn] at hσ
    rw [mem_coe, mem_filter, mem_derangeOn]
    refine ⟨fun j hj => ?_, ?_⟩
    · -- no new fixed point inside `S`
      intro hfix
      rw [Equiv.Perm.mul_apply] at hfix
      have hσj : σ j = Equiv.swap i t j := by
        have := congrArg (Equiv.swap i t) hfix
        rwa [Equiv.swap_apply_self] at this
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      by_cases hjt : j = t
      · subst hjt
        rw [Equiv.swap_apply_right] at hσj
        exact hji (σ.injective (hσj.trans hσ.2.symm))
      · rw [Equiv.swap_apply_of_ne_of_ne hji hjt] at hσj
        exact hσ.1 j hj hσj
    · rw [Equiv.Perm.mul_apply, hσ.2, Equiv.swap_apply_left]
  · intro σ _ τ _ h
    exact mul_left_cancel h

/-- Summing `PMC.card_filter_fix_le` over the possible images of `i`. -/
theorem card_mul_card_filter_fix_le {i : α} {S : Finset α} (hi : i ∉ S) :
    Fintype.card α * #((derangeOn S).filter fun σ => σ i = i) ≤ #(derangeOn S) := by
  have hfib : #(derangeOn S) = ∑ t : α, #((derangeOn S).filter fun σ => σ i = t) :=
    Finset.card_eq_sum_card_fiberwise (fun σ _ => mem_univ (σ i))
  calc Fintype.card α * #((derangeOn S).filter fun σ => σ i = i)
      = ∑ _t : α, #((derangeOn S).filter fun σ => σ i = i) := by
        rw [Finset.sum_const, card_univ, smul_eq_mul]
    _ ≤ ∑ t : α, #((derangeOn S).filter fun σ => σ i = t) :=
        Finset.sum_le_sum fun t _ => card_filter_fix_le hi t
    _ = #(derangeOn S) := hfib.symm

/-- **Fixed-point events are negatively correlated with derangement events.** The event
`σ i = i` and the event "no fixed point inside `S`" satisfy the lopsided local lemma's
hypothesis whenever `i ∉ S`.

They are *not* independent, which is exactly why §6.5 needs the lopsided form: conditioning
on there being no fixed point elsewhere makes `σ i = i` less likely, not equally likely. -/
theorem wprob_fix_inter_derangeOn_le [Nonempty α] (i : α) {S : Finset α} (hi : i ∉ S) :
    wprob (unifPerm α) (((univ : Finset (Equiv.Perm α)).filter fun σ => σ i = i)
        ∩ derangeOn S)
      ≤ wprob (unifPerm α) ((univ : Finset (Equiv.Perm α)).filter fun σ => σ i = i)
        * wprob (unifPerm α) (derangeOn S) := by
  have hApos : (0 : ℝ) < Fintype.card α := by
    have := Fintype.card_pos (α := α); exact_mod_cast this
  have hPpos : (0 : ℝ) < Fintype.card (Equiv.Perm α) := by
    exact_mod_cast card_perm_pos (α := α)
  have hinter : ((univ : Finset (Equiv.Perm α)).filter fun σ => σ i = i) ∩ derangeOn S
      = (derangeOn S).filter fun σ => σ i = i := by
    ext σ
    simp only [mem_inter, mem_filter, mem_univ, true_and]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hcount : (Fintype.card α : ℝ) * #((derangeOn S).filter fun σ => σ i = i)
      ≤ #(derangeOn S) := by exact_mod_cast card_mul_card_filter_fix_le hi
  rw [hinter, wprob_unifPerm_apply_eq i i, wprob_unifPerm, wprob_unifPerm,
    div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (#((derangeOn S).filter fun σ => σ i = i) : ℝ) * (Fintype.card α * Fintype.card (Equiv.Perm α))
      = ((Fintype.card α : ℝ) * #((derangeOn S).filter fun σ => σ i = i))
          * Fintype.card (Equiv.Perm α) := by ring
    _ ≤ (#(derangeOn S) : ℝ) * Fintype.card (Equiv.Perm α) := by
        exact mul_le_mul_of_nonneg_right hcount (le_of_lt hPpos)

end Permutation

end PMC
