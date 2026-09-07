import ProbMethods.Basic

/-!
# §2.4 — Sampling

Zhao, *Probabilistic Methods in Combinatorics*, Proposition 2.4.4.

Question 2.4.1 — the exact hypergraph Turán density for the tetrahedron — is a notorious
open problem and is not a node. Only the sampling upper bound is formalized.
-/

open Finset

namespace PMC

/-- **Tetrahedron-free 3-graphs are sparse** (Zhao, Proposition 2.4.4).

A tetrahedron-free 3-graph on `n ≥ 5` vertices has at most `(7/10) * C(n, 3)` edges,
stated as `10 * #H ≤ 7 * n.choose 3` to stay in `ℕ` without division.

**The notes state this for `n ≥ 4`, which is off by one.** On four vertices the extremal
tetrahedron-free 3-graph has `3` of the `4` triples — omit any single triple and no
tetrahedron remains — while `(7/10) * C(4,3) = 2.8`. The `n ≥ 5` hypothesis is also what
the argument actually needs, since it samples five vertices at a time.

The proof samples `5` of the `n` vertices: averaging the edge density over all `5`-subsets
reduces the claim to the base case, that a tetrahedron-free 3-graph on `5` vertices has at
most `7` of its `10` triples. That base case is exactly tight. -/
theorem card_le_of_not_hasTetrahedron {n : ℕ} (hn : 5 ≤ n) (H : Finset (Finset (Fin n)))
    (hH : IsThreeGraph H) (hfree : ¬ HasTetrahedron H) :
    10 * #H ≤ 7 * n.choose 3 := by
  sorry

end PMC
