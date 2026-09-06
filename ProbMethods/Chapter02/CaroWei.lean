import ProbMethods.Basic

/-!
# §2.3 — Caro–Wei and Turán's theorem

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 2.3.2, Corollary 2.3.5 and
Theorem 2.3.6.

Mathlib already has Turán's theorem in its structural form
(`SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`): the extremal `K_{r+1}`-free
graphs are exactly the Turán graphs. What is formalized here is the *edge-count* bound of
Theorem 2.3.6, which the notes derive from Caro–Wei.
-/

open Finset

namespace PMC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Caro–Wei for an induced subgraph: writing `d_t u` for the number of neighbours of `u`
that lie in `t`, the set `t` contains an independent set of size at least
`∑ u ∈ t, 1 / (d_t u + 1)`.

This is the derandomization of Zhao, Remark 2.3.4, run as a strong induction on `t`: delete
a vertex `v` of minimum degree in `t` together with its neighbours, and add `v` to the
independent set the induction hypothesis supplies for what is left. -/
private lemma exists_isIndepSet_caro_wei_on (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) :
    ∃ s ⊆ t, G.IsIndepSet (s : Set V) ∧
      ∑ u ∈ t, (1 : ℝ) / (#(t ∩ G.neighborFinset u) + 1) ≤ #s := by
  induction t using Finset.strongInductionOn with
  | _ t ih =>
  rcases t.eq_empty_or_nonempty with rfl | ht
  · exact ⟨∅, Subset.rfl, by simp, by simp⟩
  obtain ⟨v, hvt, hvmin⟩ := t.exists_min_image (fun u => #(t ∩ G.neighborFinset u)) ht
  have hvt' : v ∉ t \ insert v (G.neighborFinset v) := fun h =>
    (mem_sdiff.1 h).2 (mem_insert_self _ _)
  obtain ⟨s, hst, hind, hsum⟩ :=
    ih _ ((ssubset_iff_of_subset sdiff_subset).2 ⟨v, hvt, hvt'⟩)
  have hvs : v ∉ s := fun h => hvt' (hst h)
  refine ⟨insert v s, insert_subset hvt (hst.trans sdiff_subset), ?_, ?_⟩
  · -- Nothing surviving the deletion is adjacent to `v`, so `v` extends `s`.
    rw [coe_insert]
    refine Set.Pairwise.insert hind fun b hb _ => ?_
    have hb' := (mem_sdiff.1 (hst hb)).2
    rw [mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hb'
    exact ⟨hb'.2, fun h => hb'.2 h.symm⟩
  · have hpos : (0 : ℝ) < #(t ∩ G.neighborFinset v) + 1 := Nat.cast_add_one_pos _
    -- `v` and its neighbours carry total weight at most `(d_t v + 1) / (d_t v + 1) = 1`,
    -- because no vertex of `t` has smaller degree than `v`.
    have hB : ∑ u ∈ t ∩ insert v (G.neighborFinset v),
        (1 : ℝ) / (#(t ∩ G.neighborFinset u) + 1) ≤ 1 := by
      refine (sum_le_card_nsmul _ _ ((1 : ℝ) / (#(t ∩ G.neighborFinset v) + 1))
        fun u hu => one_div_le_one_div_of_le hpos ?_).trans ?_
      · exact_mod_cast Nat.add_le_add_right (hvmin u (mem_inter.1 hu).1) 1
      · have hsub : t ∩ insert v (G.neighborFinset v)
            ⊆ insert v (t ∩ G.neighborFinset v) := by
          intro u hu
          obtain ⟨hut, huN⟩ := mem_inter.1 hu
          rcases mem_insert.1 huN with rfl | huv
          · exact mem_insert_self _ _
          · exact mem_insert_of_mem (mem_inter.2 ⟨hut, huv⟩)
        rw [nsmul_eq_mul, mul_one_div, div_le_one hpos]
        exact_mod_cast (card_le_card hsub).trans (card_insert_le _ _)
    -- Deleting vertices only lowers degrees, so `hsum` already covers the survivors.
    have hA : ∑ u ∈ t \ insert v (G.neighborFinset v),
        (1 : ℝ) / (#(t ∩ G.neighborFinset u) + 1) ≤ #s := by
      refine (sum_le_sum fun u _ =>
        one_div_le_one_div_of_le (Nat.cast_add_one_pos _) ?_).trans hsum
      exact_mod_cast Nat.add_le_add_right
        (card_le_card (inter_subset_inter sdiff_subset Subset.rfl)) 1
    have hincl : t ∩ insert v (G.neighborFinset v) ⊆ t := inter_subset_left
    have hsplit :=
      sum_sdiff (f := fun u => (1 : ℝ) / (#(t ∩ G.neighborFinset u) + 1)) hincl
    rw [sdiff_inter_self_left] at hsplit
    rw [← hsplit, card_insert_of_notMem hvs]
    exact_mod_cast add_le_add hA hB

/-- **Caro–Wei inequality** (Zhao, Theorem 2.3.2; Caro 1979, Wei 1981).

Every graph `G` has an independent set of size at least `∑ v, 1 / (d v + 1)`.

The book's proof takes a uniformly random ordering of the vertices and keeps those that
precede all of their neighbours. The kept set is independent, and vertex `v` is kept with
probability `1 / (d v + 1)`, so the expected size of the kept set is `∑ v, 1 / (d v + 1)`. -/
theorem exists_isIndepSet_caro_wei (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧
      ∑ v : V, (1 : ℝ) / (G.degree v + 1) ≤ #s := by
  obtain ⟨s, -, hind, hsum⟩ := exists_isIndepSet_caro_wei_on G univ
  simp only [univ_inter, SimpleGraph.card_neighborFinset_eq_degree] at hsum
  exact ⟨s, hind, hsum⟩

/-- **Caro–Wei, clique form** (Zhao, Corollary 2.3.5).

Every `n`-vertex graph `G` has a clique of size at least `∑ v, 1 / (n - d v)`.

Apply `PMC.exists_isIndepSet_caro_wei` to the complement, whose degrees are `n - 1 - d v`. -/
theorem exists_isClique_caro_wei (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ s : Finset V, G.IsClique (s : Set V) ∧
      ∑ v : V, (1 : ℝ) / ((Fintype.card V : ℝ) - G.degree v) ≤ #s := by
  -- An independent set of `Gᶜ` is a clique of `G`, and `Gᶜ` has degrees `n - 1 - d v`.
  obtain ⟨s, hs, hsum⟩ := exists_isIndepSet_caro_wei Gᶜ
  refine ⟨s, by simpa using hs, le_trans (le_of_eq ?_) hsum⟩
  refine Finset.sum_congr rfl fun v _ => ?_
  have hlt : G.degree v < Fintype.card V := SimpleGraph.degree_lt_card_verts v
  -- `degree_compl` subtracts in `ℕ`, which truncates, so settle the identity there and
  -- cross to `ℝ` once.
  have hnat : Gᶜ.degree v + 1 = Fintype.card V - G.degree v := by
    rw [SimpleGraph.degree_compl]
    omega
  have hcast : ((Fintype.card V - G.degree v : ℕ) : ℝ) = (Fintype.card V : ℝ) - G.degree v :=
    Nat.cast_sub hlt.le
  have hone : ((Gᶜ.degree v + 1 : ℕ) : ℝ) = (Gᶜ.degree v : ℝ) + 1 := by simp
  rw [← hcast, ← hone, hnat]

/-- **Turán's theorem, edge-count form** (Zhao, Theorem 2.3.6; Turán 1941).

An `n`-vertex `K_{r+1}`-free graph has at most `(1 - 1 / r) * n ^ 2 / 2` edges.

The book's proof combines `PMC.exists_isClique_caro_wei` with convexity: `K_{r+1}`-freeness
bounds the clique guaranteed there by `r`, and `∑ v, 1 / (n - d v) ≥ n / (n - 2 * m / n)`
by the AM–HM inequality, where `m` is the number of edges. -/
theorem card_edgeFinset_le_of_cliqueFree {r : ℕ} (hr : 0 < r) (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : G.CliqueFree (r + 1)) :
    (#G.edgeFinset : ℝ) ≤ (1 - 1 / r) * (Fintype.card V : ℝ) ^ 2 / 2 := by
  sorry

end PMC
