import ProbMethods.Chapter06.LocalLemma

/-!
# §6.2 — Colouring hypergraphs by the local lemma

Zhao, *Probabilistic Methods in Combinatorics*, §6.2.

The local-lemma strengthening of §1.3's `PMC.twoColorable_of_card_lt_two_pow`: instead of
bounding the *total* number of edges, it is enough that no edge meets too many others.

Colourings are subsets `S ⊆ V` (the vertices coloured one way), so the sample space is
`Finset V` with the uniform weight. The event "edge `i` is monochromatic" is determined by
the coordinates in `edge i`, which is what discharges the local lemma's independence
hypothesis via `PMC.card_inter_mul_of_determinedBy`.
-/

open Finset

namespace PMC

section Coloring

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- The event that edge `i` is monochromatic: the colouring `S` either contains all of it
or misses all of it. -/
def monoEvent (edge : ι → Finset V) (i : ι) : Finset (Finset V) :=
  (univ : Finset (Finset V)).filter fun S => edge i ⊆ S ∨ edge i ∩ S = ∅

/-- Being monochromatic on `edge i` depends only on the colours of `edge i`'s vertices. -/
theorem determinedBy_monoEvent (edge : ι → Finset V) (i : ι) :
    DeterminedBy (edge i) (monoEvent edge i) := by
  intro S T hST
  have hsub : edge i ⊆ S ↔ edge i ⊆ T := by
    constructor
    · intro h x hx
      have : x ∈ S ∩ edge i := mem_inter.mpr ⟨h hx, hx⟩
      rw [hST] at this
      exact (mem_inter.mp this).1
    · intro h x hx
      have : x ∈ T ∩ edge i := mem_inter.mpr ⟨h hx, hx⟩
      rw [← hST] at this
      exact (mem_inter.mp this).1
  have hdis : edge i ∩ S = ∅ ↔ edge i ∩ T = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
    constructor
    · intro h ⟨x, hx⟩
      rw [mem_inter] at hx
      have : x ∈ T ∩ edge i := mem_inter.mpr ⟨hx.2, hx.1⟩
      rw [← hST, mem_inter] at this
      exact h ⟨x, mem_inter.mpr ⟨hx.1, this.1⟩⟩
    · intro h ⟨x, hx⟩
      rw [mem_inter] at hx
      have : x ∈ S ∩ edge i := mem_inter.mpr ⟨hx.2, hx.1⟩
      rw [hST, mem_inter] at this
      exact h ⟨x, mem_inter.mpr ⟨hx.1, this.1⟩⟩
  simp only [monoEvent, mem_filter, mem_univ, true_and]
  rw [hsub, hdis]

/-- A `k`-edge is monochromatic under exactly `2 * 2 ^ (n - k)` of the `2 ^ n` colourings:
all of it one colour, or all of it the other. -/
theorem card_monoEvent (edge : ι → Finset V) (i : ι) {k : ℕ} (hk : 1 ≤ k)
    (hcard : #(edge i) = k) :
    #(monoEvent edge i) = 2 * 2 ^ (Fintype.card V - k) := by
  classical
  have hdet := determinedBy_monoEvent edge i
  rw [hdet.card_eq]
  have hsdiff : #((univ : Finset V) \ edge i) = Fintype.card V - k := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hcard]
  -- the traces on `edge i` that are monochromatic are exactly `∅` and `edge i`
  have htrace : (edge i).powerset.filter (fun U => U ∈ monoEvent edge i)
      = {∅, edge i} := by
    ext U
    simp only [mem_filter, mem_powerset, monoEvent, mem_univ, true_and, mem_insert,
      mem_singleton]
    constructor
    · rintro ⟨hUsub, hU | hU⟩
      · exact Or.inr (Finset.Subset.antisymm hUsub hU)
      · refine Or.inl (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_)
        have : x ∈ edge i ∩ U := mem_inter.mpr ⟨hUsub hx, hx⟩
        rw [hU] at this
        exact notMem_empty x this
    · rintro (rfl | rfl)
      · exact ⟨empty_subset _, Or.inr (by simp)⟩
      · exact ⟨Subset.rfl, Or.inl Subset.rfl⟩
  have hne : (∅ : Finset V) ≠ edge i := by
    intro h
    rw [← h] at hcard
    simp at hcard
    omega
  rw [htrace, card_insert_of_notMem (by simpa using hne), card_singleton, hsdiff]
  ring

end Coloring

end PMC
