import ProbMethods.Weighted
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# §4.1 — Triangles in a random graph, first moment

Zhao, *Probabilistic Methods in Combinatorics*, §4.1.

The notes ask when `G(n, p)` typically contains a triangle and answer with a threshold at
`p ≍ 1/n`. What is stated here is the first-moment computation the threshold rests on, as a
finite identity; the `n → ∞` phrasing is the part this project's conventions keep out of
statements.

Graphs are edge sets in `Sym2 V`, so `PMC.bweight p` is the `G(n, p)` distribution on them
(`ProbMethods/Weighted.lean`).
-/

open Finset

namespace PMC

/-- **The expected number of triangles in `G(n, p)` is `C(n, 3) * p ^ 3`** (Zhao, §4.1).

An identity, not an estimate: each of the `C(n, 3)` vertex triples spans three specific
edges, and a fixed set of three edges is present with weight exactly `p ^ 3`
(`PMC.sum_bweight_superset`). Exchanging the order of summation is the whole proof, and no
hypothesis on `p` is needed.

With `p ≍ 1 / n` the right-hand side is bounded, which is the quantitative content of the
threshold in the notes. -/
theorem sum_bweight_mul_card_triangles {V : Type*} [Fintype V] [DecidableEq V] (p : ℝ) :
    ∑ E ∈ (univ : Finset (Sym2 V)).powerset, bweight p E * (#(triangles E) : ℝ)
      = (Fintype.card V).choose 3 * p ^ 3 := by
  classical
  have hcard : ∀ E : Finset (Sym2 V), (#(triangles E) : ℝ)
      = ∑ t ∈ powersetCard 3 (univ : Finset V),
          (if spannedEdges t ⊆ E then (1 : ℝ) else 0) := by
    intro E
    rw [triangles, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : spannedEdges t ⊆ E <;> simp [h]
  have h32 : Nat.choose 3 2 = 3 := by decide
  calc ∑ E ∈ (univ : Finset (Sym2 V)).powerset, bweight p E * (#(triangles E) : ℝ)
      = ∑ E ∈ (univ : Finset (Sym2 V)).powerset, ∑ t ∈ powersetCard 3 (univ : Finset V),
          bweight p E * (if spannedEdges t ⊆ E then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun E _ => ?_
        rw [hcard E, Finset.mul_sum]
    _ = ∑ t ∈ powersetCard 3 (univ : Finset V), ∑ E ∈ (univ : Finset (Sym2 V)).powerset,
          bweight p E * (if spannedEdges t ⊆ E then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ _t ∈ powersetCard 3 (univ : Finset V), p ^ 3 := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [mem_powersetCard] at ht
        have hconv : ∑ E ∈ (univ : Finset (Sym2 V)).powerset,
            bweight p E * (if spannedEdges t ⊆ E then (1 : ℝ) else 0)
              = ∑ E ∈ (univ : Finset (Sym2 V)).powerset.filter
                  (fun E => spannedEdges t ⊆ E), bweight p E := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun E _ => ?_
          by_cases h : spannedEdges t ⊆ E <;> simp [h]
        rw [hconv, sum_bweight_superset, card_spannedEdges, ht.2, h32]
    _ = (Fintype.card V).choose 3 * p ^ 3 := by
        rw [Finset.sum_const, card_powersetCard, card_univ, nsmul_eq_mul]

end PMC
