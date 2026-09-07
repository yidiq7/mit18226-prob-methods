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

## Symmetric form and applications

The symmetric local lemma (`e p (d+1) ≤ 1` with `#(N i) ≤ d` and `wprob w (A i) ≤ p`)
follows by taking `x i = 1/(d+1)` and using `(1 - 1/(d+1))^d > 1/e`. Worth stating as a
corollary once the general form is proved, since every application in §6.2–§6.6 uses the
symmetric version.

§6.2 (colouring hypergraphs) strengthens §1.3's `property_b_lower`, which is already
proved, so it is a natural first application.
