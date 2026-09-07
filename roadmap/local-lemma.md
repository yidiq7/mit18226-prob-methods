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

### lll — stated, not proved
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

**Proof strategy.** Two nested inductions.

1. By induction on `#T`: for `i ∉ T`,
   `wprob w (A i ∩ noneOf A T) ≤ x i * wprob w (noneOf A T)`.
   Split `T` into `T₁ = T ∩ N i` and `T₂ = T \ N i`. Bound the numerator using
   independence across `T₂`, which gives `wprob w (A i) * wprob w (noneOf A T₂)`; bound the
   denominator below by `(∏ j ∈ T₁, (1 - x j)) * wprob w (noneOf A T₂)` using the inductive
   hypothesis, peeling `T₁` one element at a time. Since `T₁ ⊆ N i`, the product in
   `hbound` dominates `∏ j ∈ T₁, (1 - x j)` and the ratio collapses to `x i`.
2. By induction on `S`, from
   `wprob w (noneOf A (insert i S)) ≥ (1 - x i) * wprob w (noneOf A S)`.

**The one thing to get right in Lean**: the informal proof divides by
`wprob w (noneOf A T)`, which is not yet known to be positive at the point of division.
Keep everything multiplicative — that is why the statement and both inductive claims above
are phrased as products rather than conditional probabilities.

## Symmetric form and applications

The symmetric local lemma (`e p (d+1) ≤ 1` with `#(N i) ≤ d` and `wprob w (A i) ≤ p`)
follows by taking `x i = 1/(d+1)` and using `(1 - 1/(d+1))^d > 1/e`. Worth stating as a
corollary once the general form is proved, since every application in §6.2–§6.6 uses the
symmetric version.

§6.2 (colouring hypergraphs) strengthens §1.3's `property_b_lower`, which is already
proved, so it is a natural first application.
