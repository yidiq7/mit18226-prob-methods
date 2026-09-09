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

section Events

variable (G : SimpleGraph V) [DecidableRel G.Adj] {r k : ℕ} (w : Fin r → Fin k → V)

/-- The index of a bad event: an ordered pair of parts with `i < j`, and a slot in each.

`abbrev`, not `def`: reducibility is what lets `if_pos` fire on `tEvent`/`tBlock` below
without a rewrite, which is the trap that sank the first attempt at this proof. -/
abbrev tValid (c : Fin r × Fin r × Fin k × Fin k) : Prop :=
  c.1 < c.2.1 ∧ G.Adj (w c.1 c.2.2.1) (w c.2.1 c.2.2.2)

/-- The bad event: both chosen slots are the ones joined by an edge. Invalid indices get the
empty event, which is never violated, has probability `0`, and is determined on the empty
block — so it is disjoint from everything and costs nothing. -/
abbrev tEvent (c : Fin r × Fin r × Fin k × Fin k) : Finset (Fin r → Fin k) :=
  if tValid G w c then
    (univ : Finset (Fin r → Fin k)).filter (fun f => f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2)
  else ∅

/-- The coordinates a bad event depends on. -/
abbrev tBlock (c : Fin r × Fin r × Fin k × Fin k) : Finset (Fin r) :=
  if tValid G w c then {c.1, c.2.1} else ∅

/-- Each bad event depends only on the two part-indices in its block. -/
theorem determinedOn_tEvent (c : Fin r × Fin r × Fin k × Fin k) :
    DeterminedOn (tBlock G w c) (tEvent G w c) := by
  by_cases hc : tValid G w c
  · rw [show tEvent G w c = (univ : Finset (Fin r → Fin k)).filter
        (fun f => f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2) from if_pos hc,
      show tBlock G w c = ({c.1, c.2.1} : Finset (Fin r)) from if_pos hc]
    intro f g hfg
    simp only [mem_filter, mem_univ, true_and]
    rw [hfg c.1 (by simp), hfg c.2.1 (by simp)]
  · rw [show tEvent G w c = (∅ : Finset (Fin r → Fin k)) from if_neg hc]
    intro f g _
    simp

/-- **A bad event has probability `1/k²`**: it pins down two distinct coordinates, and
block independence multiplies `PMC.wprob_unifProd_coord` twice. -/
theorem wprob_tEvent_le [Nonempty (Fin k)] (c : Fin r × Fin r × Fin k × Fin k) :
    wprob (unifProd (Fin r) (Fin k)) (tEvent G w c) ≤ 1 / (k : ℝ) ^ 2 := by
  by_cases hc : tValid G w c
  · rw [show tEvent G w c = (univ : Finset (Fin r → Fin k)).filter
        (fun f => f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2) from if_pos hc]
    have hne : c.1 ≠ c.2.1 := ne_of_lt hc.1
    have hsplit : (univ : Finset (Fin r → Fin k)).filter
          (fun f => f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2)
        = ((univ : Finset (Fin r → Fin k)).filter fun f => f c.1 = c.2.2.1)
          ∩ ((univ : Finset (Fin r → Fin k)).filter fun f => f c.2.1 = c.2.2.2) := by
      ext f
      simp [and_assoc]
    have hdet1 : DeterminedOn ({c.1} : Finset (Fin r))
        ((univ : Finset (Fin r → Fin k)).filter fun f => f c.1 = c.2.2.1) := by
      intro f g hfg
      simp only [mem_filter, mem_univ, true_and]
      rw [hfg c.1 (by simp)]
    have hdet2 : DeterminedOn ((univ : Finset (Fin r)) \ {c.1})
        ((univ : Finset (Fin r → Fin k)).filter fun f => f c.2.1 = c.2.2.2) := by
      intro f g hfg
      simp only [mem_filter, mem_univ, true_and]
      rw [hfg c.2.1 (by simp [Ne.symm hne])]
    rw [hsplit, wprob_unifProd_mul_of_determinedOn hdet1 hdet2,
      wprob_unifProd_coord, wprob_unifProd_coord, Fintype.card_fin, div_mul_div_comm,
      one_mul, sq]
  · rw [show tEvent G w c = (∅ : Finset (Fin r → Fin k)) from if_neg hc, wprob_empty]
    positivity

end Events

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
