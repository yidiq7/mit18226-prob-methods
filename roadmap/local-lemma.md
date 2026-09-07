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

What remains for the full statement (a `k`-uniform hypergraph in which every edge meets at
most `d` others is 2-colourable once `e (d+1) 2^(1-k) ≤ 1`) is arithmetic assembly: fix the
uniform weight `1/2^n`, set `p = 2^(1-k)`, take the dependency graph to be "shares a
vertex", and feed `PMC.lovasz_local_lemma_symmetric`.

The remaining sections (§6.3 independent transversals, §6.4 directed cycles, §6.5 lopsided
local lemma, §6.6 algorithmic local lemma) each need their own setup; §6.5 in particular
needs a different independence hypothesis (lopsidependency) and so a variant statement, not
just an application.
