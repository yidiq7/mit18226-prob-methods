import ProbMethods.Weighted

/-!
# §4.3 — monotone properties and the satisfying probability

§4.3's *threshold* results are asymptotic and stay deferred, but **Theorem 4.3.5 is not**: for
a non-trivial monotone property `F`, the map `p ↦ P(Ω_p ∈ F)` is strictly increasing on
`[0,1]`. That is a finite statement about a polynomial in `p`, and it is the fact every later
threshold argument silently uses.

In this project's encoding, `P(Ω_p ∈ F) = ∑_{S ∈ F} bweight p S` — the `G(n,p)` weight of
`Weighted.lean` summed over the family. *Monotone* means upward-closed, and *non-trivial*
means `F` is neither empty nor everything; note that upward-closure makes those equivalent to
`∅ ∉ F` and `univ ∈ F`.

Route for a prover. The clean argument changes one coordinate at a time. With independent
coordinate probabilities, the weight of `F` is **linear** in each `p_j`:

    P = p_j · P(F | j ∈ S) + (1 - p_j) · P(F | j ∉ S),

and upward-closure gives `P(F | j ∈ S) ≥ P(F | j ∉ S)` by the injection `S ↦ S ∪ {j}`, so `P`
is nondecreasing in every coordinate. Strictness needs one *pivotal* coordinate, which
non-triviality supplies: a minimal member of `F` is nonempty, and deleting one of its
elements leaves a non-member.
-/

open Finset

namespace PMC

section Threshold

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A family of subsets is **monotone** if it is upward-closed. -/
def IsMonotoneFamily (F : Finset (Finset α)) : Prop :=
  ∀ S ∈ F, ∀ T : Finset α, S ⊆ T → T ∈ F

/-- Upward-closure turns non-triviality into the two endpoint facts. -/
lemma notMem_empty_of_monotone {F : Finset (Finset α)} (hF : IsMonotoneFamily F)
    (hnotall : F ≠ (univ : Finset (Finset α))) : (∅ : Finset α) ∉ F := by
  intro hmem
  refine hnotall (Finset.eq_univ_of_forall fun S => ?_)
  exact hF ∅ hmem S (Finset.empty_subset S)

lemma mem_univ_of_monotone {F : Finset (Finset α)} (hF : IsMonotoneFamily F)
    (hne : F.Nonempty) : (univ : Finset α) ∈ F := by
  obtain ⟨S, hS⟩ := hne
  exact hF S hS univ (Finset.subset_univ S)

/-- **Theorem 4.3.5 (monotonicity of the satisfying probability).** For a non-trivial monotone
family `F`, the weight `p ↦ ∑_{S ∈ F} bweight p S` is strictly increasing on `[0,1]`. -/
theorem strictMonoOn_sum_bweight (F : Finset (Finset α)) (hF : IsMonotoneFamily F)
    (hne : F.Nonempty) (hnotall : F ≠ (univ : Finset (Finset α))) :
    StrictMonoOn (fun p : ℝ => ∑ S ∈ F, bweight p S) (Set.Icc (0 : ℝ) 1) := by
  sorry

end Threshold

end PMC
