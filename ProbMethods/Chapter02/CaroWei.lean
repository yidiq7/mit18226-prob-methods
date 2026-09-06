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

/-- **Caro–Wei inequality** (Zhao, Theorem 2.3.2; Caro 1979, Wei 1981).

Every graph `G` has an independent set of size at least `∑ v, 1 / (d v + 1)`.

The book's proof takes a uniformly random ordering of the vertices and keeps those that
precede all of their neighbours. The kept set is independent, and vertex `v` is kept with
probability `1 / (d v + 1)`, so the expected size of the kept set is `∑ v, 1 / (d v + 1)`. -/
theorem exists_isIndepSet_caro_wei (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧
      ∑ v : V, (1 : ℝ) / (G.degree v + 1) ≤ #s := by
  sorry

/-- **Caro–Wei, clique form** (Zhao, Corollary 2.3.5).

Every `n`-vertex graph `G` has a clique of size at least `∑ v, 1 / (n - d v)`.

Apply `PMC.exists_isIndepSet_caro_wei` to the complement, whose degrees are `n - 1 - d v`. -/
theorem exists_isClique_caro_wei (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ s : Finset V, G.IsClique (s : Set V) ∧
      ∑ v : V, (1 : ℝ) / ((Fintype.card V : ℝ) - G.degree v) ≤ #s := by
  sorry

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
