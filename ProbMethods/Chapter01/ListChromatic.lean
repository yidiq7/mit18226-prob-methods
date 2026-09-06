import ProbMethods.Basic

/-!
# §1.4 — List chromatic number of `K_{n,n}`

Zhao, *Probabilistic Methods in Combinatorics*, Theorems 1.4.2 and 1.4.3.
-/

open Finset

namespace PMC

/-- **`K_{n,n}` is `k`-choosable when `n < 2 ^ (k - 1)`** (Zhao, Theorem 1.4.2).

Equivalently `ch(K_{n,n}) ≤ ⌊log₂ (2n)⌋ + 1`.

The book's proof marks each colour `L` or `R` independently and uniformly at random, then
deletes the `R`-marked colours from the lists on the left side and the `L`-marked colours
from the lists on the right. A vertex is left with an empty list with probability `2 ^ (-k)`,
so by the union bound some marking leaves every one of the `2n` vertices a usable colour;
choosing from the surviving lists uses each colour on one side only. -/
theorem completeBipartiteChoosable_of_lt_two_pow {n k : ℕ} (hn : n < 2 ^ (k - 1)) :
    CompleteBipartiteChoosable n k := by
  sorry

/-- **Non-2-colourable hypergraphs obstruct choosability** (Zhao, Theorem 1.4.3).

If some `k`-uniform hypergraph with `n` edges is not 2-colourable, then `K_{n,n}` is not
`k`-choosable.

The book's proof views the vertex set of the hypergraph as the colour set, and gives the
`i`-th vertex on each side of `K_{n,n}` the list consisting of the `i`-th edge. A proper
list colouring would then 2-colour the hypergraph. -/
theorem not_completeBipartiteChoosable_of_not_twoColorable {n k : ℕ}
    {V : Type} [Fintype V] [DecidableEq V] {E : Finset (Finset V)}
    (hk : ∀ e ∈ E, #e = k) (hcard : #E = n) (hE : ¬ TwoColorable E) :
    ¬ CompleteBipartiteChoosable n k := by
  sorry

end PMC
