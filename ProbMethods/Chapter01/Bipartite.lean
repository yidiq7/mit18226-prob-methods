import ProbMethods.Basic

/-!
# §1.0 — Large bipartite subgraphs

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 1.0.1.
-/

open Finset

-- CI smoke test 2: no semantic change.
namespace PMC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Large bipartite subgraph** (Zhao, Theorem 1.0.1).

Every graph with `m` edges has a bipartite subgraph with at least `m / 2` edges.

Stated as a max-cut bound: some two-colouring `c` of the vertices cuts at least half the
edges, i.e. `#G.edgeFinset ≤ 2 * #(cutEdges G c)`. The bichromatic edges of `c` are exactly
the edges of a bipartite subgraph of `G`.

The book's proof colours each vertex black or white independently and uniformly, and notes
that each edge is cut with probability `1 / 2`, so the expected number of cut edges is
`m / 2`; some colouring meets the expectation. -/
theorem exists_cut_two_mul_card_edgeFinset_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ c : V → Bool, #G.edgeFinset ≤ 2 * #(cutEdges G c) := by
  sorry

end PMC
