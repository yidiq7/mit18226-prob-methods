import ProbMethods.Basic

/-!
# §1.3 — 2-colourable hypergraphs

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 1.3.1.
-/

open Finset

namespace PMC

variable {V : Type*}

/-- **Erdős' lower bound for property B** (Zhao, Theorem 1.3.1; Erdős 1964).

Every `k`-uniform hypergraph with fewer than `2 ^ (k - 1)` edges is 2-colourable; that is,
`m k ≥ 2 ^ (k - 1)`, where `m k` is the least number of edges of a `k`-uniform hypergraph
that is not 2-colourable.

The book's proof takes a uniformly random 2-colouring of the vertices: each edge is
monochromatic with probability `2 ^ (1 - k)`, so the expected number of monochromatic
edges is `#E * 2 ^ (1 - k) < 1`, and some colouring has none. -/
theorem twoColorable_of_card_lt_two_pow {k : ℕ} {E : Finset (Finset V)}
    (hk : ∀ e ∈ E, #e = k) (hE : #E < 2 ^ (k - 1)) : TwoColorable E := by
  sorry

end PMC
