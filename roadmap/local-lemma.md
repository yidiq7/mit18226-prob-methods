# Chapter 6 — Lovász Local Lemma

## Why this chapter is work rather than missing theory

Mathlib has no local lemma — the survey in [mathlib-survey.md](mathlib-survey.md) found no
`lovasz`, `local_lemma` or `localLemma` anywhere. But unlike Talagrand (§9.5) or the
container theorem (Chapter 11), the local lemma is **fully expressible in the finite
weighted framework** already built here: events are `Finset`s of a finite sample space,
`PMC.wprob` is their probability, and the dependency structure is a neighbour map
`N : ι → Finset ι`. Nothing about it needs measure theory or a limit.

That makes it the highest-value target among the unstarted chapters, and the most-cited
result in the book.

## The framework

`ProbMethods/Weighted.lean` gained the event layer: `PMC.wprob w A = ∑ ω ∈ A, w ω`, with
monotonicity, the empty and universal cases, and `wprob_compl`.

`ProbMethods/Chapter06/LocalLemma.lean` adds `PMC.noneOf A T = T.inf (fun j => (A j)ᶜ)` —
the event that none of `A j` for `j ∈ T` occurs. Writing it as a `Finset.inf` gives
`noneOf A ∅ = univ` for free, which is the base case both inductions need. Checked by
evaluation: over `∅` it is the whole space, and peeling indices intersects complements as
it should.

### lll — **proved**
`PMC.lovasz_local_lemma`, the asymmetric form: if `wprob w (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)`
and each `A i` is independent of every subfamily of complements drawn from outside
`insert i (N i)`, then

    ∏ i, (1 - x i) ≤ wprob w (noneOf A univ)

which is positive since each `x i < 1`.

**The independence hypothesis quantifies over every subfamily `T` disjoint from
`insert i (N i)`.** That is what mutual independence means and it is essential — pairwise
independence does not suffice for the local lemma. Getting this wrong would make the
statement either false or trivial, so it is worth stating explicitly rather than through a
convenience predicate.

**How the proof went.** Two inductions, as planned:

* `lll_peel` (inner, induction on the index set `U`): given the main bound for all
  *strictly smaller* index sets, `(∏ j ∈ U, (1 - x j)) * P(noneOf V) ≤ P(noneOf (U ∪ V))`.
  The step uses `PMC.wprob_compl_inter` — `P(Bᶜ ∩ S) = P(S) - P(B ∩ S)` — to peel one index.
* `lll_key` (outer, strong induction on `#T`): split `T` into `T ∩ N i` and `T \ N i`,
  bound the numerator by independence across the second part, bound the denominator below
  by `lll_peel` on the first, and close with
  `Finset.prod_le_prod_of_subset_of_le_one` — more factors in `[0,1]` means a smaller
  product, which is what lets `hbound`'s `∏ j ∈ N i` dominate `∏ j ∈ T ∩ N i`.

The final statement is then `lll_peel` at `V = ∅`, where `noneOf A ∅ = univ` has weight `1`.

**The thing that mattered in Lean**: the informal proof divides by `wprob w (noneOf A T)`,
which is not known to be positive at the point of division — the conclusion is precisely
what establishes positivity. Everything is therefore phrased multiplicatively, and no
division appears anywhere in the development. That was the single design decision the proof
turned on.

## Symmetric form — proved

`PMC.lovasz_local_lemma_symmetric`: if every event has probability at most `p`, depends on
at most `d` others, and `e * p * (d + 1) ≤ 1`, then with positive probability none occurs.
This is the form every application in §6.2–§6.6 uses.

From the asymmetric form at `x i = 1 / (d + 1)`. The analytic input is
`1 / e ≤ (d / (d + 1)) ^ d` (`inv_exp_le_pow`), which comes from `1 + t ≤ exp t` at
`t = 1/d`: that gives `(1 + 1/d) ^ d ≤ exp 1`, and `(d/(d+1)) * (1 + 1/d) = 1` inverts it.

**`0 < d` is required, and textbooks leave it implicit.** At `d = 0` the choice
`x i = 1/(d+1) = 1` violates the asymmetric form's `x i < 1`. That case is separately
trivial — mutual independence gives `P(none) = ∏ (1 - P(A i))` directly — but it is a real
side condition, not a formality.

## Applications

**The independence hypothesis is the real cost of any application**, and the tool for it is
now proved: `PMC.card_filter_inter_prod` (`Weighted.lean`) says properties depending on
*disjoint blocks of coordinates* factor,

    #{S ⊆ V : P (S ∩ C) ∧ Q (S ∩ (V \ C))} = #{U ⊆ C : P U} * #{W ⊆ V \ C : Q W}

by the bijection `S ↦ (S ∩ C, S ∩ (V \ C))`. Checked numerically as well as formally (both
sides give `9` on `Fin 4` with `C = {0,1}`).

**On top of it, the discharge is packaged once.** `PMC.DeterminedBy C A` says membership in
`A` depends only on `S ∩ C`, and `PMC.card_inter_mul_of_determinedBy` then gives

    #(A ∩ A') * 2 ^ n = #A * #A'

for `A` determined by `C` and `A'` determined by `univ \ C` — i.e. `P(A ∩ A') = P(A) P(A')`
under the uniform measure. **So an application of the local lemma only has to exhibit the
blocks and check they are disjoint**, rather than re-derive independence. The key step is
that determinacy gives `S ∈ A ↔ S ∩ C ∈ A`, which turns the event into a filter of the
shape `card_filter_inter_prod` expects.

### §6.2 — both substantive inputs proved

`ProbMethods/Chapter06/Coloring.lean`. Colourings are subsets `S ⊆ V`, so the sample space
is `Finset V` under the uniform weight, and `PMC.monoEvent edge i` is the event that edge
`i` is monochromatic.

* `PMC.determinedBy_monoEvent` — monochromaticity on `edge i` depends **only** on the
  colours of `edge i`'s vertices. This is the fact that discharges the local lemma's
  independence hypothesis: two edges sharing no vertex give events on disjoint blocks, so
  `PMC.card_inter_mul_of_determinedBy` applies directly.
* `PMC.card_monoEvent` — a `k`-edge is monochromatic under exactly `2 * 2 ^ (n - k)`
  colourings, i.e. with probability `2 ^ (1-k)`. Proved through `DeterminedBy.card_eq`: the
  monochromatic *traces* on the edge are exactly `∅` and the edge itself, so the count is
  `2` times the free coordinates. Checked numerically at `(n,k) = (4,2)` and `(5,3)`, both
  giving `8`.

### §6.2 — the non-uniform criterion (Theorem 6.2.4) — done

`PMC.exists_two_coloring_of_weight_sum`: a hypergraph all of whose edges have at least
three vertices is 2-colourable as soon as

    ∑_{f ≠ e, f ∩ e ≠ ∅} 2^(-#f) ≤ 1/8   for every edge e.

`PMC.lovasz_local_lemma_quarter` (Corollary 6.1.10) at the monochromatic events: `#e ≥ 3`
gives `P(A_e) = 2^{1-#e} ≤ 1/4 < 1/2`, and the hypothesis gives
`∑_{f ∈ N(e)} P(A_f) = 2 ∑ 2^{-#f} ≤ 1/4`.

This needed `PMC.wprob_monoEvent`, the *exact* probability `2^{1-#e}` rather than the `≤`
bound the symmetric application uses — the point of the criterion is that it sums
probabilities over neighbours of **different sizes**, which is the notes' Remark 6.2.5: the
sign to look past the symmetric local lemma is bad events of very different probabilities.

Sanity check on how much it buys: for a 3-uniform hypergraph the hypothesis reads
`#N(e) ≤ 1`, where the symmetric form (Theorem 6.2.1) needs `e(d+1)/4 ≤ 1`, i.e. `d = 0`.

One deliberate difference from the notes: the sum here is over *indices* `j ≠ i` rather than
over distinct edges, so two indices carrying the same edge set are counted twice. That makes
the hypothesis stronger than the notes' and the theorem no weaker, and it keeps the indexed
convention the rest of the file uses.

### §6.2 — done

`PMC.exists_two_coloring_of_local_lemma`: a `k`-uniform hypergraph in which every edge
meets at most `d` others is 2-colourable once `e (d+1) 2^(1-k) ≤ 1`. This strengthens
§1.3's `PMC.twoColorable_of_card_lt_two_pow`, which bounds the *total* number of edges —
here the bound is local, so it applies to arbitrarily large hypergraphs.

The assembly took four supporting pieces, all reusable for §6.3–§6.4:

* `PMC.unifColoring` and `PMC.wprob_unifColoring` — the uniform weight `1/2^n` on
  colourings, under which probability is literally counting.
* `PMC.wprob_unifColoring_mul_of_determinedBy` — independence in the exact shape the local
  lemma's `hindep` wants, obtained from `PMC.card_inter_mul_of_determinedBy` by dividing
  through by `(2^n)^2`.
* `PMC.determinedBy_noneOf` — "none of the edges in `T` is monochromatic" is determined by
  any block containing all of them (Finset induction through `noneOf_insert`).
* `PMC.mem_noneOf` — membership in `noneOf`, which turns the positive probability the local
  lemma returns into an actual colouring.

**Non-vacuity was checked**, not assumed: instantiating at two 4-edges sharing a vertex on
7 points (`k = 4`, `d = 1`, `e·2·(2/16) ≈ 0.68 ≤ 1`) discharges every hypothesis, so the
theorem is not true-by-empty-hypotheses. Worth doing for any statement whose hypotheses are
a numeric inequality — a mis-stated constant turns the whole result into a tautology, and
nothing in the gate would catch it.

### §6.2's other numbered results, from the coverage audit

* `PMC.exists_two_coloring_of_local_lemma'` is **Theorem 6.2.6** in the finite case: edges of
  size *at least* `k` rather than exactly `k`. The generalisation cost nothing — an edge of
  size `m ≥ k` is monochromatic with probability `2^{1-m} ≤ 2^{1-k}`, and the symmetric local
  lemma only ever wanted an upper bound. Theorem 6.2.1 is now the uniform corollary. The
  notes also state 6.2.6 for *infinite* vertex sets, which needs their compactness Lemma
  6.2.7; that is not claimed here.
* `PMC.exists_two_coloring_of_regular` is **Corollary 6.2.2**: for `k ≥ 9`, every `k`-uniform
  `k`-regular hypergraph is 2-colourable. The degree count is the content — an edge has `k`
  vertices, each lying in `k` edges, one being the edge itself, so it meets at most `k(k-1)`
  others. The side condition `2e(k²-k+1) ≤ 2ᵏ` is an induction from `k = 9`; the *step* needs
  only `k² - 3k + 1 ≥ 0`, true from `k = 3`, so **`9` is forced by the base case**, not by the
  induction.

### Product sample spaces are now available

`ProbMethods/Product.lean`. §6.2 could use `PMC.DeterminedBy` because a 2-colouring *is* a
subset. The remaining applications choose one value per coordinate — §6.4 colours vertices
from `ZMod k`, §6.3 picks one vertex per part — so their sample space is a product `ι → β`
and `DeterminedBy` does not reach it.

`PMC.DeterminedOn` and `PMC.card_inter_mul_of_determinedOn` are the product analogue, with
`PMC.wprob_unifProd_mul_of_determinedOn` in the shape the local lemma's `hindep` wants.

The whole content is `PMC.spliceOn`: take the coordinates in `C` from one point and the
rest from another. **Splicing is an involution on pairs** — `(f,g) ↦ (splice f g, splice g f)`
twice is the identity — which identifies `A ×ˢ B` with `(A ∩ B) ×ˢ univ` in one step, with
no case analysis. Avoiding the obvious route `(ι → β) ≃ (C → β) × (Cᶜ → β)` was deliberate:
that drags dependent types through every step, whereas splicing keeps everything at
`ι → β`. Same choice `PMC.masked` made for Chapter 10's tuples, and it paid off both times.

### The product-space local lemma is now packaged

`ProbMethods/Chapter06/ProductLLL.lean`. `PMC.exists_avoiding_of_lll` is the twin of §6.2's
`PMC.exists_two_coloring_of_local_lemma`, for a product sample space: supply the events, the
coordinate block each one depends on, a bound `p` on their probabilities, and a bound `d` on
how many other blocks each block meets, and it returns a point avoiding every event.
Independence is discharged internally, so an **application never has to mention `wprob`** —
which is the whole point of packaging it. Usability was verified end to end by instantiating
it on a small concrete product with all seven hypotheses discharged, not just by type-checking
the statement.

The earlier note here said §6.3 would need a *weighted* product version, because parts have
different sizes. That is avoided: after the trimming step all parts have size exactly
`k = ⌈2eΔ⌉`, so enumerating each part by `Fin k` makes the sample space `Fin r → Fin k`,
which is uniform. The trimming is `Finset.exists_subset_card_eq` and an independent
transversal of the trimmed parts is one of the originals.

`PMC.exists_enumeration` performs the trimming and the enumeration in one step, and was
checked on parts of *different* sizes (4 and 2, enumerated at 2) — the case trimming exists
for.

For events on **more than two** coordinates — §6.4's bad event constrains a vertex's whole
out-neighbourhood — use `PMC.wprob_unifProd_forall`: independent coordinates multiply, so
the probability is the product of the per-coordinate ones. Checked on `(Fin 3 → Fin 4)`:
`36` of `64` functions have both coordinates `0` and `1` nonzero, i.e. `(3/4)²`.

The probability side is also done: `PMC.wprob_unifProd_coord` gives `1/k` for one
coordinate, and block independence multiplies it to `1/k²` for the two coordinates a bad
event pins down. Checked on `(Fin 3 → Fin 4)`: `16` of `64` for one coordinate and `4` of
`64` for two.

### The §6.3 assembly was attempted and abandoned once; read this first

All four components are proved and committed. The assembly — one theorem, about 250 lines —
was written in one go, and that was the mistake. **Build it block by block, compiling after
each**, because two Lean pitfalls hit repeatedly and both produce cascading errors that are
hard to attribute once the file is large:

* **`set f := fun c => …` makes `rw [hfdef]` useless.** Rewriting turns `f c` into an
  un-beta-reduced `(fun c => …) c`, so the following `if_pos` never matches. The fix is not to
  rewrite at all: `f c` is *definitionally* the body, so `if_pos hc : f c = …` typechecks
  directly and can be used with `rw [show f c = … from if_pos hc]`. (`simp only [hfdef]` also
  works, since `simp` beta-reduces, but the `show` form is clearer about intent.)
* **`rcases (h : c' = c) with rfl` can eliminate the wrong variable.** Both sides are locals,
  and Lean may substitute away `c` — which is still needed for the rest of the proof, giving
  "unknown identifier `c`" many lines later. Use `rcases … with heq | _` and `rw [heq]`.

Also: an order contradiction of the shape `c₁.1 < c₁.2.1 = c₂.1 < c₂.2.1 = c₁.1` should be a
`calc` chain ending in `lt_irrefl`, not a `▸` chain — the `▸` version does not elaborate,
and `Fin` means `omega` is unavailable.

What remains for §6.3 is graph bookkeeping rather than probability:

* **Index the bad events by pairs `(i, j, a, b)` with `i < j` and `w i a` adjacent to
  `w j b`.** The ordering matters: indexing by *ordered* pairs doubles the dependency degree
  to `4kΔ`, which forces `|Vᵢ| ≥ 4eΔ` and is strictly weaker than Theorem 6.3.1. With
  `i < j` each cross-part edge is counted once and the degree is `2kΔ`, matching the notes.
* Take the index type to be the *full* product `Fin r × Fin r × Fin k × Fin k`, setting
  `A c = ∅` and `C c = ∅` for invalid indices. Empty events are never violated, have
  probability `0`, and are determined on `∅`, so they are disjoint from every block and cost
  nothing — this avoids carrying a subtype of valid indices.
* Bound the dependency degree by `2kΔ - 1`. The counting core is proved:
  `PMC.card_adj_pairs_le` says the ordered adjacent pairs whose first vertex lies in `S`
  number at most `#S · Δ`, and with `S = Vᵢ ∪ V_j` of size `2k` that is the notes' `2kΔ`.
  It was checked **tight** on `K₄` (`2 · 3 = 6`), so the bound is not loose.

  What is left is the *injection*: send a neighbouring index `(i',j',a',b')` to the ordered
  pair `(w i' a', w j' b')` if `i' ∈ {i,j}`, and to `(w j' b', w i' a')` otherwise. It is
  injective, and the reason is exactly the `i < j` convention — a collision would need
  `c' = (i',j',a',b')` and `c'' = (j',i',b',a')` both in the index set, which `i < j` forbids.
  The `- 1` is then the self-exclusion from the errata above; without it the notes' displayed
  inequality is false at `Δ = 2`.

### §6.3 and §6.4, read off the notes

**Theorem 6.3.1.** `G = (V,E)` has maximum degree `Δ`, and `V = V₁ ∪ ⋯ ∪ V_r` is a partition
with `|Vᵢ| ≥ 2eΔ` for every `i`. Then `G` has an independent set containing one vertex from
each `Vᵢ`.

The notes' proof is the one to follow, and its shape suits the library well:

1. **Trim.** May assume `|Vᵢ| = k := ⌈2eΔ⌉`, else drop vertices. In Lean this is
   `Finset.exists_subset_card_eq`, and an independent transversal of the trimmed parts is
   one of the originals — so the reduction is genuinely cheap, not a hand-wave.
2. Pick `vᵢ ∈ Vᵢ` uniformly and independently. With all parts of size exactly `k`, the
   sample space is a **uniform product** `Fin r → Fin k` once each part is enumerated —
   exactly what `ProbMethods/Product.lean` now covers, so no weighted product layer is
   needed after all.
3. Bad events indexed by **edges**, not by pairs of parts: `A_e` = both endpoints of `e` are
   picked, `P(A_e) = 1/k²`, and `A_e ∼ A_f` when some `Vᵢ` meets both. The notes explicitly
   contrast this with the pair-indexed "Attempt 1", whose dependency degree is too large.

**Errata (Theorem 6.3.1's arithmetic).** The notes write the local-lemma condition as
`e (1/k²)(2kΔ + 1) ≤ 1`. That is **false** for `k = ⌈2eΔ⌉` at small `Δ`: at `Δ = 2`,
`k = 11` and `e · 45 / 121 ≈ 1.011 > 1`. The fix is the self-exclusion the symmetric local
lemma allows: an edge `e` incident to `Vᵢ ∪ V_j` is one of the at most `2kΔ` edges meeting
that set, and the dependency neighbourhood excludes `e` itself, so `d ≤ 2kΔ - 1` and
`e p (d + 1) ≤ e (1/k²)(2kΔ) = 2eΔ/k ≤ 1` exactly when `k ≥ 2eΔ`. The theorem is correct;
the displayed inequality is off by that one edge. **Formalize with `d + 1 ≤ 2kΔ`.**

### §6.3 — proved by a contributor (PR #43, merged)

Task #41 published the statement with a `sorry`. A contributor claimed it 36 seconds later
and delivered a verified, self-contained proof (PR #43). **The orchestrator proved it
concurrently and closed the issue four minutes before that PR arrived — a process error.**
A published task belongs to whoever claims it; proving a claimed task discards a
contributor's compute and, worse, the reason to contribute at all.

All nine checks passed and the PR is merged, so Theorem 6.3.1 is the first result in this
project proved by someone other than the orchestrator.

The resolution kept both: `Transversal.lean` is restored to the exact published base so the
contributor's patch applies to it byte-for-byte, and the orchestrator's modular pieces —
`PMC.tEvent`, `PMC.determinedOn_tEvent`, `PMC.wprob_tEvent_le`, `PMC.card_tNbr_le` — move to
`TransversalBlocks.lean`, where they remain verified and available for §6.5 without
competing for the theorem's name.

**Check the lease before proving anything yourself.** `choir orch tasks` shows claims; the
race was avoidable by reading it.

**Theorem 6.4.3 (Alon–Linial 1989).** Every directed graph with minimum out-degree `δ` and
maximum in-degree `Δ` contains a cycle of length divisible by `k`, as long as
`k ≤ δ / (1 + log(1 + δΔ))`. Theorem 6.4.1 and Corollary 6.4.2 are the `d`-regular
specialisations.

### The probabilistic half of §6.4 — proved

`PMC.exists_labelling_with_successor`: in a loopless digraph where every vertex has
out-degree exactly `δ` and in-degree at most `Δ`, if

    e ((k-1)/k)^δ (Δ + δΔ + 1) ≤ 1

then the vertices can be labelled by `ZMod k` so that **every vertex has an out-neighbour
carrying the next label**. That is 6.4.3's hypothesis-side statement as a self-contained
theorem, and it is the object its cycle argument consumes.

The assembly is short because all four inputs were built to fit `exists_avoiding_of_lll`
directly: the blocks are `PMC.dblk r v`, the probability bound is `PMC.wprob_dEvent_le`,
the degree bound is `PMC.card_digraph_dependency_le`, and `PMC.determinedOn_dEvent` (the
last piece, proved here) says the event only reads coordinates inside its block. **The
local lemma's `hfar` — far-apart events have disjoint blocks — is discharged from the
*definition* of the dependency neighbourhood**, which is why the whole degree count enters
through a single lemma rather than being re-derived inside the assembly.

Non-vacuity checked on the complete digraph on 9 vertices at `k = 2`, where out-degree and
in-degree are both `8` and `e·(1/2)⁸·(8 + 64 + 1) ≈ 0.775 ≤ 1`: all six hypotheses
discharge, so the numeric side condition is satisfiable.

**What is left of §6.4 is not probabilistic.** Deriving 6.4.3 from this labelling means
extracting a directed cycle whose length is divisible by `k` — a walk argument on digraphs,
see below.

The inputs, for reference: label
vertices with `ZMod k` uniformly, so the sample space is the uniform product `V → ZMod k`;
`A_v` is "no out-neighbour of `v` is labelled `x_v + 1`", whose probability
`(1 - 1/k)^{d⁺(v)}` is `PMC.wprob_unifProd_forall`; and the dependency degree `Δ + δΔ` is
`PMC.card_digraph_dependency_le`, counted the notes' own three ways and checked **tight** on
the directed 4-cycle.

Note that this is the notes' *first-pass* degree bound, which gives
`k ≤ δ/(1 + log(1 + Δ + δΔ))`. Theorem 6.4.3's stated constant
`k ≤ δ/(1 + log(1 + δΔ))` needs their "final trick" — the observation that `A_v` is
independent of every `A_w` with `N⁺(v)` disjoint from `N⁺(w) ∪ {w}`, a strictly smaller
dependency digraph. The first-pass version is what is proved above; the trick can be
layered on top of it without touching the assembly, since it only shrinks `N`.

### §6.4 — Theorem 6.4.3 is done

`ProbMethods/Chapter06/DivisibleCycle.lean`. The combinatorial half was expected to be the
bulk of the work, because Mathlib develops walks and cycles for `SimpleGraph` but not for
digraphs. **It is not, and no digraph machinery was built.**

The observation that avoids it: choosing at each vertex *one* out-neighbour carrying the
next label packages the labelling as a successor **function** `f : V → V`, and a directed
cycle is then exactly a *periodic orbit* of `f`. So

* `PMC.exists_cycle_of_successor` — iterating `f` from any vertex must repeat in a finite
  type (`Finite.exists_ne_map_eq_of_infinite`), which produces a periodic point; the cycle
  is its orbit. Its vertices are distinct by
  `Function.iterate_injOn_Iio_minimalPeriod`, and since the label rises by `1` per step,
  returning to the start after `p` steps gives `x u = x u + p`, i.e. `(p : ZMod k) = 0`, so
  `k ∣ p`. **Taking the *minimal* period is what makes the vertices distinct** — the period
  the pigeonhole hands over is a closed walk, not a cycle.

  A cycle of length `p` is recorded as a `c : ℕ → V` with `r (c n) (c (n+1))` for all `n`,
  `c (n + p) = c n`, and `c` injective on `Set.Iio p`: `p` distinct vertices in directed
  cyclic order, with no `Walk` analogue needed.

* `PMC.exists_cycle_length_dvd` — Theorem 6.4.3 for out-degree exactly `δ`, the two halves
  joined. The `choose` step is where "every vertex has *an* out-neighbour with the next
  label" becomes "*the* chosen out-neighbour", which is what makes the orbit argument
  available at all.

* `PMC.exists_cycle_length_dvd_of_le_outdegree` — Theorem 6.4.3 with the notes' hypothesis,
  **minimum** out-degree `δ`, by deleting out-edges: choose `δ` out-neighbours at each
  vertex and run the argument on the sub-digraph, whose out-degree is exactly `δ` and whose
  in-degree only dropped. **This reduction is necessary, not cosmetic**: the probability
  bound wants the out-degree *large* and the dependency-degree bound wants it *small*, so no
  single inequality on `δ` serves both. The notes leave the step implicit.

* `PMC.exists_cycle_length_dvd_of_log_bound` — the notes' shape,
  `k ≤ δ / (1 + log(1 + Δ + δΔ))`. The analytic step is `(k-1)/k = 1 - 1/k ≤ exp(-1/k)`,
  so the left side of the local lemma's condition is at most `exp(1 - δ/k) M`, which is
  `≤ 1` exactly when `1 + log M ≤ δ/k`.

Non-vacuity checked at both ends: the complete digraph on 9 vertices at `k = 2` for the
direct numeric form, and on 25 vertices at `k = 2` for the log form
(`2(1 + log 601) = 14.8 ≤ 24`).

**What is left in §6.4** is only the constant: `Δ + δΔ` where the notes have `δΔ`. That gap
is the first-pass dependency digraph, and their final trick only *shrinks* `N`, so it plugs
into the same assembly without touching anything above.

### §6.5 — the lopsided local lemma is proved, and the weakening was free

`PMC.lovasz_local_lemma_lopsided` and `PMC.lovasz_local_lemma_symmetric_lopsided`
(Erdős–Spencer). The dependency hypothesis is negative correlation,

    P(A i ∩ noneOf A T) ≤ P(A i) · P(noneOf A T),

an inequality rather than the independence equality. **The existing proof already sufficed.**
It uses the hypothesis exactly once, in a `calc` chain that only ever travels upward, to
replace `P(A i ∩ noneOf A T₂)` by `P(A i) P(noneOf A T₂)` — so an inequality in that
direction is all it needed. The change is one `=` to one `≤` in `lll_key`, and the
independence forms `PMC.lovasz_local_lemma` and `PMC.lovasz_local_lemma_symmetric` become
one-line corollaries, so every §6.2–§6.4 application is untouched.

This is worth recording as a general lesson: **a proof written multiplicatively, with no
division, tends to generalize from equality hypotheses to inequality hypotheses for free.**
The earlier decision to avoid dividing by `P(noneOf A T)` was made to dodge a positivity
problem, and it paid a second time here.

**Corollary 6.5.6, the derangement bound, is also proved**
(`PMC.wprob_derangeOn_univ_ge`): a uniform random permutation of an `n`-element set has no
fixed point with probability at least `(1 - 1/n)^n`. It is the smallest application of the
lopsided form and shows why that form is needed: the events `σ i = i` are **not**
independent, so `PMC.lovasz_local_lemma` cannot be used, but they are negatively correlated,
and the dependency neighbourhood is *empty*.

The supporting layer is `ProbMethods/Permutation.lean`, and it rests on a single device:
**composing with a transposition.** `σ ↦ Equiv.swap t t' * σ` is a bijection between the
permutations sending `i` to `t` and those sending `i` to `t'`, which gives

* `PMC.wprob_unifPerm_apply_eq` — `P(σ i = t) = 1/n`, *exactly*. An upper bound would not do:
  the lopsided hypothesis has `P(A i)` itself on the right-hand side.
* `PMC.card_filter_fix_le` and `PMC.wprob_fix_inter_derangeOn_le` — the same transposition,
  now applied to permutations that avoid fixed points on a set `S` with `i ∉ S`. It cannot
  create a fixed point at `j ∈ S`, because that needs `σ j = swap i t j`, which forces `j = t`
  and `σ t = i` — impossible when `σ i = i` already. **This is Theorem 6.5.5's random
  injection argument for single-edge matchings**, with the transposition in the role of the
  permutation of `Y` carrying `F₀` to `T`.

The negative correlation was checked to be *strict* (`Fin 3` with `S = {1}`: `3 < 4`, i.e.
`1/6 < 2/9`), so this is not independence in disguise.

**Erratum in Corollary 6.5.6's proof.** The notes write "Since `P(A_i) = 1 - 1/n`, we can set
`x_i = 1 - 1/n`". Both numbers are the same slip: `P(A_i) = 1/n` and the choice is
`x_i = 1/n`, which is what makes the displayed `(1 - 1/n)^n` come out.

**The one missing ingredient is published as a task**: `PMC.exists_perm_extend`, that a
partial injection extends to a permutation *fixing every point outside its domain and image*.
Mathlib's `Equiv.extendSubtype` does "something arbitrary outside" — its construction happens
to be the identity off the union, but that is not exposed as a lemma. The clause is not
decoration: 6.5.5 needs the column permutation carrying one matching to another to leave
every other column alone, or it could create a forbidden pattern elsewhere.

**Theorem 6.5.11's probability input is also proved**, `PMC.wprob_pairEvent`:
`P(σ i₁ = j₁ ∧ σ i₂ = j₂) = 1/(n(n-1))`. One transposition again suffices — hold the first
column fixed and `Equiv.swap` moves the second anywhere else, fixing `j₁` precisely because
both columns differ from it. The `n-1` rather than `n` is the constraint `σ i₂ ≠ σ i₁`, which
is why the fibering runs over `univ.erase j₁`.

So of Theorem 6.5.11 (Erdős–Spencer) the probability side is done and the dependency side
waits on 6.5.5, i.e. on task #44.

### §6.5 — Theorem 6.5.11 proved, modulo the dependency input

`ProbMethods/Chapter06/LatinTransversal.lean`. `PMC.exists_latin_transversal`: if every entry
of an `n × n` array appears at most `m` times and `4 e m ≤ n`, the array has a Latin
transversal — a permutation `σ` with the entries `c i (σ i)` pairwise distinct.

The negative-dependence input (Theorem 6.5.5, which waits on task #44) is an **explicit
hypothesis** `hlop`, in exactly the shape `PMC.lovasz_local_lemma_symmetric_lopsided` consumes.
So the theorem is sorry-free and does not depend on `PMC.exists_perm_extend`'s `sorry`; what is
missing is visible in its statement, and discharging it later is a one-line change.

Everything else in the notes' proof is done:

* the probability `1/(n(n-1))` — `PMC.wprob_pairEvent`, already proved;
* the degree count `PMC.card_badNbrs_le`: `#N(p) ≤ 4n(m-1)`. A neighbour has one of its two
  cells on one of `p`'s four lines (`PMC.crossCells`, of size at most `4n`) and its other cell
  among the at most `m - 1` remaining cells with that entry, so the neighbourhood is covered by
  a `biUnion` over the lines;
* the arithmetic `e(4n(m-1) + 2) ≤ n(n-1)`, which is where `4 e m ≤ n` enters.

Two decisions worth recording.

**Each unordered bad pair must be one index.** Indexing the bad events by *ordered* pairs of
cells lists every event twice, which doubles the degree — and the constant `n/(4e)` does not
survive a factor of two. Orienting each pair by `i₁ < i₂` fixes this, and it also gives the
row-distinctness `i₁ ≠ i₂` for free.

**The crude `4n` beats the notes' `4n - 4`.** The notes count the four lines by
inclusion–exclusion; here they are a union bound over two rows and two columns, because the
slack in `e p (d+1) ≤ 1` is of order `4en` against `n` and four cells' worth of over-count
costs nothing. The degree bound also holds for the non-bad indices (whose events are empty),
so no case split on badness is needed anywhere.

Spot-checked by evaluation on the cyclic Latin square of order 3: `9` bad pairs — three pairs
of equal entries for each of the three symbols — and a maximum neighbourhood of `9`, against
the bound `4·3·(3−1) = 24`. (The theorem itself says nothing at `n = 3`: `4em ≤ 3` forces
`m = 0`.)

What remains of §6.5 is Theorem 6.5.5 in **full generality** (arbitrary vertex-disjoint
matchings in the random injection model) and the Latin-transversal application built on it.
The single-edge case above is the same argument, so the generalization is a matter of
replacing the transposition by a permutation carrying one matching to another; the
bookkeeping, not the idea, is the work.

§6.6 (algorithmic local lemma, Moser–Tardos) needs its own setup: an entropy-compression or
witness-tree argument, which is a different proof technique rather than a variant statement.
