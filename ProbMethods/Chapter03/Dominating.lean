import ProbMethods.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# §3.1 — Dominating sets

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 3.1.1.
-/

open Finset

namespace PMC

/-- **Small dominating sets** (Zhao, Theorem 3.1.1).

Every graph with minimum degree `δ > 1` has a dominating set of size at most
`((log (δ + 1) + 1) / (δ + 1)) * n`.

The book's proof is the alteration method in two steps. Include each vertex of `V`
independently with probability `p`, giving a set `X`; then let `Y` be the vertices that
neither lie in `X` nor have a neighbour in `X`, so that `X ∪ Y` is dominating by
construction. A vertex lands in `Y` with probability at most `(1 - p) ^ (1 + δ)`, so

    E|X ∪ Y| ≤ p * n + (1 - p) ^ (1 + δ) * n ≤ (p + exp (-p * (1 + δ))) * n

using `1 + x ≤ exp x`. Setting `p = log (δ + 1) / (δ + 1)` minimises the bracket and gives
the stated bound.

**Note on the formalization.** The distribution here is *not* uniform — it is
`Bernoulli p` with `p` generally irrational — so this is the first node in the project that
the pure counting convention does not cover. It does not need `MeasureTheory` either: over
a finite vertex set the expectation is a finite weighted sum
`∑ X ⊆ univ, p ^ #X * (1 - p) ^ (n - #X) * f X`, and `Finset.prod_add` supplies
`∑ X, p ^ #X * (1 - p) ^ (n - #X) = (p + (1 - p)) ^ n = 1`. Averaging against those
weights is the whole probabilistic content. -/
theorem exists_isDominating_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {δ : ℕ} (hδ : 1 < δ)
    (hdeg : ∀ v, δ ≤ G.degree v) :
    ∃ U : Finset V, IsDominating G U ∧
      (#U : ℝ) ≤ (Real.log (δ + 1) + 1) / (δ + 1) * Fintype.card V := by
  sorry

end PMC
