import ProbMethods.Weighted

/-!
# §4.1, §4.4 — First moments in a random graph

Zhao, *Probabilistic Methods in Combinatorics*, §4.1 (triangles) and §4.4 (clique number).

Both sections open with the same computation, so both live here. Each is stated as a finite
identity; the `n → ∞` threshold phrasing is the part this project's conventions keep out of
statements.

Graphs are edge sets in `Sym2 V`, so `PMC.bweight p` is the `G(n, p)` distribution
(`ProbMethods/Weighted.lean`), and both results are immediate from
`PMC.sum_bweight_mul_card_filter`.
-/

open Finset

namespace PMC

/-- **The expected number of `k`-cliques in `G(n, p)` is `C(n, k) * p ^ C(k, 2)`**
(Zhao, §4.4).

An identity, with no hypothesis on `p` or `k`: the patterns are the edge sets spanned by
the `C(n, k)` vertex `k`-sets, each carrying `C(k, 2)` edges. Forcing the right-hand side
below `1` is what bounds the clique number from above. -/
theorem sum_bweight_mul_card_cliqueSets {V : Type*} [Fintype V] [DecidableEq V]
    (p : ℝ) (k : ℕ) :
    ∑ E ∈ (univ : Finset (Sym2 V)).powerset, bweight p E * (#(cliqueSets k E) : ℝ)
      = (Fintype.card V).choose k * p ^ (k.choose 2) := by
  have h := sum_bweight_mul_card_filter (α := Sym2 V) p
    (powersetCard k (univ : Finset V)) spannedEdges (k.choose 2)
    (fun t ht => by
      rw [mem_powersetCard] at ht
      rw [card_spannedEdges, ht.2])
  rw [card_powersetCard, card_univ] at h
  exact h

/-- **The expected number of triangles in `G(n, p)` is `C(n, 3) * p ^ 3`** (Zhao, §4.1) —
the `k = 3` case of the clique count.

With `p ≍ 1 / n` this is bounded, which is the quantitative content of the threshold in the
notes. -/
theorem sum_bweight_mul_card_triangles {V : Type*} [Fintype V] [DecidableEq V] (p : ℝ) :
    ∑ E ∈ (univ : Finset (Sym2 V)).powerset, bweight p E * (#(triangles E) : ℝ)
      = (Fintype.card V).choose 3 * p ^ 3 := by
  have h := sum_bweight_mul_card_cliqueSets (V := V) p 3
  rw [show Nat.choose 3 2 = 3 from by decide] at h
  simp only [triangles_eq]
  exact h

end PMC
