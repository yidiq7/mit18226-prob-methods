import ProbMethods.Chapter06.ProductLLL

/-!
# §6.3 — Independent transversals (Theorem 6.3.1)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 6.3.1: a graph of maximum degree `Δ`
whose vertex set is partitioned into parts of size at least `2eΔ` has an independent set
containing one vertex from each part.

**Every probabilistic component is already proved.** What is missing is the graph
bookkeeping that feeds them to the local lemma. The four components:

* `PMC.exists_avoiding_of_lll` — the local lemma on a product sample space. Supply the
  events, the coordinate block each depends on, a probability bound `p` and a degree bound
  `d`; independence is discharged internally, so this proof never mentions `PMC.wprob`.
* `PMC.exists_enumeration` — trims the parts to size exactly `k` and enumerates each by
  `Fin k`, making the sample space the *uniform* product `Fin r → Fin k`. A transversal built
  from it is automatically a transversal of the original parts.
* `PMC.card_adj_pairs_le` — the ordered adjacent pairs starting in a set `S` number at most
  `#S · Δ`. With `S = Vᵢ ∪ V_j` of size `2k` this is the notes' `2kΔ`.
* `PMC.wprob_unifProd_coord` — fixing one coordinate has probability `1/k`; block
  independence multiplies it to `1/k²` for the two coordinates a bad event pins down.

## The intended proof

Index bad events by `c : Fin r × Fin r × Fin k × Fin k`, valid when `c.1 < c.2.1` and
`w c.1 c.2.2.1` is adjacent to `w c.2.1 c.2.2.2`; take

* `A c = {f | f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2}` and `C c = {c.1, c.2.1}` when valid,
* `A c = ∅` and `C c = ∅` otherwise.

Invalid indices cost nothing: an empty event is never violated, has probability `0`, and is
determined on the empty block, so it is disjoint from every other block. That is what lets
the index type be the whole product rather than a subtype of valid indices.

**`c.1 < c.2.1` is load-bearing twice.** It counts each cross-part edge once, keeping the
dependency degree at `2kΔ` rather than `4kΔ` — the latter would only prove the theorem for
parts of size `4eΔ`, which is weaker than 6.3.1. And it is what makes the degree injection
injective: send a neighbouring index `(i',j',a',b')` to the ordered pair
`(w i' a', w j' b')` when `i' ∈ {i,j}` and to `(w j' b', w i' a')` otherwise; a collision
would need both `(i,j,a,b)` and `(j,i,b,a)` to be indices, which `i < j` forbids.

## Errata in the source

The notes write the local-lemma condition as `e (1/k²)(2kΔ + 1) ≤ 1`. That is **false** for
`k = ⌈2eΔ⌉` at small `Δ`: at `Δ = 2`, `k = 11` and `e · 45 / 121 ≈ 1.011 > 1`. The
dependency neighbourhood excludes the event itself, so the degree is `2kΔ - 1` and the
condition is `e (1/k²)(2kΔ) = 2eΔ/k ≤ 1`, which holds exactly when `k ≥ 2eΔ`. **Use
`d = 2kΔ - 1`.**

## Two Lean pitfalls, both of which cascade

An earlier attempt at this proof was written in one go and abandoned; build it block by
block, compiling after each.

* `set f := fun c => …` makes `rw [hfdef]` useless — it produces an un-beta-reduced
  `(fun c => …) c`, so the following `if_pos` never matches. Do not rewrite: `f c` is
  *definitionally* the body, so `rw [show f c = … from if_pos hc]` works.
* `rcases (h : c' = c) with rfl` may eliminate `c` rather than `c'`, giving "unknown
  identifier `c`" far from the cause. Use `rcases … with heq | _` and `rw [heq]`.

An order contradiction of the shape `c₁.1 < c₁.2.1 = c₂.1 < c₂.2.1 = c₁.1` should be a
`calc` chain ending in `lt_irrefl`; the `▸` version does not elaborate, and `Fin` rules out
`omega`.
-/

open Finset

namespace PMC

section Transversal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Theorem 6.3.1.** A graph of maximum degree `Δ` whose vertices are partitioned into
parts of size at least `2eΔ` has an independent set with one vertex from each part. -/
theorem exists_independent_transversal (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ r k : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (hΔpos : 0 < Δ)
    (part : Fin r → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (part i) (part j))
    (hsize : ∀ i, k ≤ #(part i))
    (hk : 2 * Real.exp 1 * Δ ≤ k) :
    ∃ v : Fin r → V, (∀ i, v i ∈ part i) ∧ ∀ i j, i ≠ j → ¬ G.Adj (v i) (v j) := by
  sorry

end Transversal

end PMC
