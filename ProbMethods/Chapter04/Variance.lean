import ProbMethods.Chapter04.SecondMoment

/-!
# §4.1 — The variance of the triangle count

Zhao, *Probabilistic Methods in Combinatorics*, §4.1.

The overlap analysis that turns `PMC.sum_bweight_triangleFree_le` into an explicit
threshold. Two triples span `3`, `5` or `6` edges between them according as they share
`3`, `2` or at most `1` vertex (`PMC.card_spannedEdges_union`), and only the first two
cases contribute to the variance — the `6`-edge pairs cancel exactly against `E[X]²`.
-/

open Finset

namespace PMC

/-- For a fixed triple `t`, at most `3 * n` triples meet it in two or more vertices: such a
`t'` is `insert v u` for a `2`-subset `u ⊆ t` and some vertex `v`. -/
private lemma card_partners_le {V : Type*} [Fintype V] [DecidableEq V] (t : Finset V) :
    #((powersetCard 3 (univ : Finset V)).filter fun t' => 2 ≤ #(t ∩ t'))
      ≤ #(powersetCard 2 t) * Fintype.card V := by
  classical
  have hsub : ((powersetCard 3 (univ : Finset V)).filter fun t' => 2 ≤ #(t ∩ t'))
      ⊆ ((powersetCard 2 t) ×ˢ (univ : Finset V)).image (fun q => insert q.2 q.1) := by
    intro t' ht'
    rw [mem_filter, mem_powersetCard] at ht'
    obtain ⟨⟨-, ht'card⟩, hmeet⟩ := ht'
    obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq hmeet
    have huT : u ⊆ t := hu.trans inter_subset_left
    have huT' : u ⊆ t' := hu.trans inter_subset_right
    have hlt : #u < #t' := by omega
    obtain ⟨v, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine mem_image.mpr ⟨(u, v), ?_, ?_⟩
    · rw [mem_product, mem_powersetCard]
      exact ⟨⟨huT, hucard⟩, mem_univ v⟩
    · have hins : insert v u ⊆ t' := insert_subset hv.1 huT'
      have hcard : #(insert v u) = 3 := by
        rw [card_insert_of_notMem hv.2, hucard]
      have heq : insert v u = t' :=
        Finset.eq_of_subset_of_card_le hins (by rw [hcard, ht'card])
      exact heq
  calc #((powersetCard 3 (univ : Finset V)).filter fun t' => 2 ≤ #(t ∩ t'))
      ≤ #(((powersetCard 2 t) ×ˢ (univ : Finset V)).image (fun q => insert q.2 q.1)) :=
        card_le_card hsub
    _ ≤ #((powersetCard 2 t) ×ˢ (univ : Finset V)) := card_image_le
    _ = #(powersetCard 2 t) * Fintype.card V := by rw [card_product, card_univ]

end PMC
