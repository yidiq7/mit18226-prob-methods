import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset

/-!
# §11.0 — how many triangle-free graphs are there?

Question 11.0.1 asks for the number of triangle-free graphs on `n` vertices, and Theorem
11.0.2 (Erdős–Kleitman–Rothschild) answers `2^{n²/4 + o(n²)}`.

**The lower bound is elementary and is what is proved here**: every subgraph of a complete
bipartite graph is triangle-free, so a bipartition into parts of size `a` and `n - a` already
gives `2^{a(n-a)}` triangle-free graphs, and the balanced split gives `2^{⌊n²/4⌋}`.

The upper bound is the hard half — it is the whole point of the container method, needing
Theorem 11.1.1 (containers for triangle-free graphs) and behind it the hypergraph container
theorem. It is also the only part of Theorem 11.0.2 that is asymptotic: the `o(n²)` sits
entirely in the upper bound, while the lower bound holds exactly, for every `n`, with no
error term. That is why this half can be stated faithfully without any restatement decision.
-/

open Finset

namespace PMC

section TriangleFree

open Classical in
/-- The triangle-free graphs on `n` labelled vertices. -/
noncomputable def triangleFreeGraphs (n : ℕ) : Finset (SimpleGraph (Fin n)) :=
  (univ : Finset (SimpleGraph (Fin n))).filter fun G => G.CliqueFree 3

/-- The graph whose edges are the pairs listed in `s`. -/
def graphOfPairs {n : ℕ} (s : Finset (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => (u, v) ∈ s

lemma graphOfPairs_adj {n : ℕ} (s : Finset (Fin n × Fin n)) (u v : Fin n) :
    (graphOfPairs s).Adj u v ↔ u ≠ v ∧ ((u, v) ∈ s ∨ (v, u) ∈ s) := by
  rw [graphOfPairs, SimpleGraph.fromRel_adj]

/-- **A graph whose edges all cross a bipartition is triangle-free.** Two of any three
vertices lie on the same side, and same-side vertices are never adjacent. -/
lemma cliqueFree_three_of_pairs {n : ℕ} (A : Finset (Fin n)) {s : Finset (Fin n × Fin n)}
    (hs : s ⊆ A ×ˢ (univ \ A)) : (graphOfPairs s).CliqueFree 3 := by
  classical
  -- an edge always joins `A` to its complement
  have hcross : ∀ u v : Fin n, (graphOfPairs s).Adj u v → (u ∈ A ↔ v ∉ A) := by
    intro u v huv
    rw [graphOfPairs_adj] at huv
    rcases huv.2 with h | h
    · have := hs h
      rw [Finset.mem_product, Finset.mem_sdiff] at this
      exact ⟨fun _ => this.2.2, fun _ => this.1⟩
    · have := hs h
      rw [Finset.mem_product, Finset.mem_sdiff] at this
      exact ⟨fun hu => absurd hu this.2.2, fun hnv => absurd this.1 hnv⟩
  -- three mutually adjacent vertices would put two on the same side
  rw [SimpleGraph.CliqueFree]
  intro t ht
  rw [SimpleGraph.isNClique_iff] at ht
  obtain ⟨hclique, hcard⟩ := ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have hA : ∀ x y : Fin n, x ∈ ({a, b, c} : Finset (Fin n)) →
      y ∈ ({a, b, c} : Finset (Fin n)) → x ≠ y → (x ∈ A ↔ y ∉ A) := by
    intro x y hx hy hxy
    exact hcross x y (hclique hx hy hxy)
  by_cases ha : a ∈ A
  · -- then `b` and `c` are both outside `A`, so they cannot be adjacent
    have hb : b ∉ A := (hA a b (by simp) (by simp) hab).mp ha
    have hc : c ∉ A := (hA a c (by simp) (by simp) hac).mp ha
    exact hb ((hA b c (by simp) (by simp) hbc).mpr hc)
  · -- then `b` and `c` are both inside `A`
    have hb : b ∈ A := by
      by_contra hcon
      exact ha ((hA a b (by simp) (by simp) hab).mpr hcon)
    have hc : c ∈ A := by
      by_contra hcon
      exact ha ((hA a c (by simp) (by simp) hac).mpr hcon)
    exact (hA b c (by simp) (by simp) hbc).mp hb hc

/-- Distinct sets of crossing pairs give distinct graphs.

The point needing care: `graphOfPairs` symmetrises, so `Adj u v` could come from `(u,v)` or
from `(v,u)`. Only one of the two can lie in `A ×ˢ Aᶜ`, which is what makes the pair set
recoverable from the graph. -/
lemma graphOfPairs_injOn {n : ℕ} (A : Finset (Fin n)) :
    Set.InjOn (graphOfPairs (n := n)) ((A ×ˢ (univ \ A)).powerset : Finset _) := by
  classical
  have key : ∀ t t' : Finset (Fin n × Fin n), t ⊆ A ×ˢ (univ \ A) → t' ⊆ A ×ˢ (univ \ A) →
      graphOfPairs t = graphOfPairs t' → ∀ u v : Fin n, (u, v) ∈ t → (u, v) ∈ t' := by
    intro t t' ht ht' heq u v hmem
    have hp := ht hmem
    rw [Finset.mem_product, Finset.mem_sdiff] at hp
    have hne : u ≠ v := fun h => hp.2.2 (h ▸ hp.1)
    have hadj : (graphOfPairs t).Adj u v := by
      rw [graphOfPairs_adj]
      exact ⟨hne, Or.inl hmem⟩
    rw [heq, graphOfPairs_adj] at hadj
    rcases hadj.2 with h | h
    · exact h
    · -- `(v,u) ∈ t'` would put `v ∈ A` and `u ∉ A`, contradicting `(u,v) ∈ t`
      have hq := ht' h
      rw [Finset.mem_product, Finset.mem_sdiff] at hq
      exact absurd hp.1 hq.2.2
  intro s hs s' hs' heq
  rw [mem_coe, Finset.mem_powerset] at hs
  rw [mem_coe, Finset.mem_powerset] at hs'
  ext p
  obtain ⟨u, v⟩ := p
  exact ⟨fun h => key s s' hs hs' heq u v h, fun h => key s' s hs' hs heq.symm u v h⟩

/-- **The lower bound in Theorem 11.0.2, for an arbitrary bipartition.** A split of the
vertices into `A` and its complement gives `2^{#A · (n - #A)}` triangle-free graphs. -/
theorem card_triangleFreeGraphs_ge_of_bipartition {n : ℕ} (A : Finset (Fin n)) :
    2 ^ (#A * #((univ : Finset (Fin n)) \ A)) ≤ #(triangleFreeGraphs n) := by
  classical
  have hcard : #((A ×ˢ ((univ : Finset (Fin n)) \ A)).powerset)
      = 2 ^ (#A * #((univ : Finset (Fin n)) \ A)) := by
    rw [Finset.card_powerset, Finset.card_product]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (graphOfPairs (n := n)) ?_ (graphOfPairs_injOn A)
  intro s hs
  rw [mem_coe, Finset.mem_powerset] at hs
  rw [mem_coe, triangleFreeGraphs, mem_filter]
  exact ⟨mem_univ _, cliqueFree_three_of_pairs A hs⟩

/-- **The lower bound in Theorem 11.0.2**: there are at least `2^{⌊n²/4⌋}` triangle-free
graphs on `n` labelled vertices, since `⌊n/2⌋ · ⌈n/2⌉ = ⌊n²/4⌋`. Exact for every `n`, with no
error term — the `o(n²)` of Theorem 11.0.2 lives entirely in the upper bound. -/
theorem card_triangleFreeGraphs_ge (n : ℕ) :
    2 ^ (n / 2 * ((n + 1) / 2)) ≤ #(triangleFreeGraphs n) := by
  classical
  obtain ⟨A, hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := n / 2)
      (by rw [card_univ, Fintype.card_fin]; omega)
  have hcompl : #((univ : Finset (Fin n)) \ A) = (n + 1) / 2 := by
    rw [Finset.card_sdiff_of_subset hAsub, card_univ, Fintype.card_fin, hAcard]
    omega
  have := card_triangleFreeGraphs_ge_of_bipartition A
  rw [hAcard, hcompl] at this
  exact this

end TriangleFree

end PMC
