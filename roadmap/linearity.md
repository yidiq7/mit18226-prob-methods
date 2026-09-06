# Chapter 2 — Linearity of Expectations

Phase 1 covers §2.3 only. Sections 2.1 (Hamilton paths in tournaments), 2.2 (sum-free
subsets), 2.4 (sampling), 2.5 (unbalancing lights) and 2.6 (the crossing number
inequality) open in phase 2, where they need definitions — tournaments, Hamilton path
counts, crossing numbers — that Mathlib does not supply and that must be authored at the
centralized layer first.

## Turán's theorem and independent sets (§2.3)

Mathlib has Turán's theorem in structural form
(`SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`): the extremal `K_{r+1}`-free
graphs are the Turán graphs. It does not have the edge-count bound the notes derive, nor
Caro–Wei. Both are nodes here.

### caro_wei
`PMC.exists_isIndepSet_caro_wei` — Theorem 2.3.2 (Caro 1979, Wei 1981).

Every graph has an independent set of size at least `∑ v, 1 / (d v + 1)`.

Zhao's proof: take a uniformly random ordering of the vertices and keep every vertex that
precedes all of its neighbours. The kept set is independent, and `v` is kept exactly when
it comes first among `{v} ∪ N(v)`, which happens with probability `1 / (d v + 1)`; so the
expected size is `∑ v, 1 / (d v + 1)` and some ordering does at least as well.

Remark 2.3.4 gives a derandomization that is likely the easier Lean route: repeatedly
remove a vertex of smallest degree together with its neighbours, charging weight
`1 / (d v + 1)` to each vertex removed. Total weight removed per step is at most 1, so the
process runs for at least `∑ v, 1 / (d v + 1)` steps, each contributing one vertex to an
independent set. Either proof is acceptable.

### caro_wei_clique
`PMC.exists_isClique_caro_wei` — Corollary 2.3.5.

Every `n`-vertex graph has a clique of size at least `∑ v, 1 / (n - d v)`. Apply
`caro_wei` to the complement, where `v` has degree `n - 1 - d v`, so
`1 / (deg_{Gᶜ} v + 1) = 1 / (n - d v)`.

### turan_edges
`PMC.card_edgeFinset_le_of_cliqueFree` — Theorem 2.3.6 (Turán 1941).

An `n`-vertex `K_{r+1}`-free graph has at most `(1 - 1/r) · n² / 2` edges.

Zhao's proof: `K_{r+1}`-freeness bounds the clique from `caro_wei_clique` by `r`, so
`r ≥ ∑_v 1/(n - d_v) ≥ n / (n - (1/n) ∑_v d_v) = n / (n - 2m/n)` by the AM–HM inequality
(equivalently, convexity of `x ↦ 1/x`). Rearranging gives `m ≤ (1 - 1/r) n² / 2`.

This is the one node in phase 1 with a real analytic step. Do not hand-roll the AM–HM
inequality: Mathlib has it as `Finset.sq_sum_div_le_sum_sq_div` (Sedrakyan's lemma, aka
Titu's or Engel's form, in `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`), which
gives `∑ (f i)^2 / g i ≥ (∑ f i)^2 / ∑ g i`. Taking `f ≡ 1` and `g v = n - d v` is exactly
the step needed. `Finset.sum_degrees_eq_twice_card_edges` supplies `∑ v, d v = 2 * m`.
