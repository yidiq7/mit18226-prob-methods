# Chapter 4 — Second Moment

## The structural finding for this chapter, and for much of the book

Sections 4.1–4.4 are all statements about the Erdős–Rényi random graph `G(n, p)`, and the
obvious reading is that they are blocked: Mathlib has no `G(n, p)`, which is also what
keeps §3.4 out of phase 3.

**That reading is wrong, and the §3.1 proof is why.** `G(n, p)` on a *fixed* vertex set is
exactly a finite Bernoulli weight sum over edge sets:

    w E = p ^ #E * (1 - p) ^ (N - #E)     over  E ∈ (univ : Finset (Sym2 V)).powerset

with `N = Fintype.card (Sym2 V)`, and `Finset.prod_add` gives `∑ w = 1`. That is the same
device `dominating` (§3.1) uses, now validated: a non-uniform, real-parameter distribution
handled as a finite weighted sum, with no `MeasureTheory` and no `PMF`. Everything in
Chapters 1–2 that was done by *uniform* counting generalises to weighted counting this way,
and the edge-indicator independence that random-graph arguments lean on is just the product
factorisation `prod_add` already encodes.

**What remains genuinely hard is the asymptotics, not the probability.** Every result in
4.1–4.4 is phrased "with high probability as `n → ∞`", and it is the limit — plus the
`o(1)`/`≲` bookkeeping — that has no cheap encoding, not the random graph. This project
already has a convention for exactly that (`README.md`: asymptotic statements are deferred
or made explicit), and it applies here: state the finite-`n` inequality with explicit
constants, and leave the limit statement out.

So the ordering for this chapter is: **build the weighted-counting layer first**, then
state the explicit-constant forms. None of it needs machinery Mathlib lacks.

**The layer now exists**, in `ProbMethods/Weighted.lean`:

* `PMC.bweight p X = p ^ #X * (1 - p) ^ (card α - #X)` — take `α := Sym2 V` for `G(n, p)`;
* `PMC.sum_bweight` — the weights total `1`;
* `PMC.sum_bweight_superset` — a fixed `B` is contained with weight `p ^ #B`, i.e. a fixed
  subgraph appears with weight `p ^ (its edge count)`. This is the opening step of every
  first-moment random-graph argument;
* `PMC.sum_bweight_disjoint` — a fixed `B` is avoided with weight `(1 - p) ^ #B`;
* `PMC.wchebyshev` / `PMC.wchebyshev'` with `PMC.wmean`, `PMC.wvar`.

All axiom-clean. What remains for §4.1–§4.4 is the combinatorics on top, not the
probability.

## Weierstrass approximation (§4.7) — UPSTREAM

Theorem 4.7.x is in Mathlib as `bernsteinApproximation_uniform`
(`Mathlib/Analysis/SpecialFunctions/Bernstein.lean`), which is exactly the Bernstein-polynomial
proof the notes give. Recorded as `upstream`; never published as a task.

## Distinct sums (§4.6) — the tractable node

Theorem 4.6.3: if some `k`-element subset of `[n]` has all `2 ^ k` subset sums distinct,
then `n ≳ 2 ^ k / sqrt k`.

**This one is uniform**, so the Chapter 1–2 counting convention covers it directly: `X` is
`∑ ε i * x i` with `ε` ranging over all `2 ^ k` sign patterns, i.e. over
`(univ : Finset (Fin k)).powerset`. The pieces:

* `μ = (∑ x) / 2` and `σ² = (∑ x²) / 4 ≤ n² k / 4`;
* Chebyshev over a finite weighted space — **now available** as `PMC.wchebyshev` and
  `PMC.wchebyshev'` in `ProbMethods/Weighted.lean`, with `PMC.wmean` and `PMC.wvar`.
  Mathlib's Chebyshev is `MeasureTheory`-only and does not apply to a bare finite sum;
* distinct subset sums give `P(X = v) ≤ 2 ^ (-k)` for each value `v`, so the count of
  patterns landing in an interval of length `2 n sqrt k` is at most `2 n sqrt k`;
* combining bounds `3/4 ≤ 2 n sqrt k * 2 ^ (-k)`, hence `n ≥ 3 * 2 ^ k / (8 sqrt k)`.

State it with that explicit constant rather than `≳`.

**Erratum.** The notes print this combination as `2 n sqrt k 2^(-k) ≤ 3/4`, with the
inequality reversed — that direction bounds `n` *above* and contradicts the stated
conclusion. The Chebyshev bound gives `P ≥ 3/4` and the distinctness bound gives
`P ≤ 2 n sqrt k 2^(-k)`, so the correct combination is `3/4 ≤ 2 n sqrt k 2^(-k)`. Unlike
the Proposition 2.4.4 erratum this one is confined to the proof; the theorem as stated is
true.

Theorem 4.6.4 (Harper's vertex-isoperimetric inequality on the hypercube) is quoted, not
proved, and belongs with Chapter 9's concentration material rather than here.

## Hardy–Ramanujan (§4.5) — not yet stated

The number of distinct prime divisors `ω(m)` concentrates around `log log n` for `m` drawn
uniformly from `[n]`. The distribution *is* uniform, so counting applies, and Mathlib has
`ω` as `Nat.ArithmeticFunction.cardDistinctFactors`. What it needs beyond that is
Mertens-type estimates on `∑ 1/p`, which is where the work is. Stateable in explicit form;
not attempted yet.

## Random graph sections (§4.1–4.4)

### random_triangle (§4.1) — proved
`PMC.sum_bweight_mul_card_triangles`: the expected number of triangles in `G(n, p)` is
exactly `C(n, 3) * p ^ 3`.

An identity, not an estimate, and it needs no hypothesis on `p`. Each of the `C(n, 3)`
triples spans three edges and a fixed edge set is present with weight `p ^ #B`
(`sum_bweight_superset`), so exchanging the order of summation is the whole proof. This is
the quantitative content the threshold at `p ≍ 1/n` rests on; the `n → ∞` statement itself
is deliberately not stated, per the asymptotics convention.

**This is the proof that the layer works.** A random-graph result, in a project with no
`MeasureTheory` and no `PMF`, in about thirty lines on top of `Weighted.lean`.

### clique_number (§4.4) — proved
`PMC.sum_bweight_mul_card_cliqueSets`: the expected number of `k`-cliques is exactly
`C(n, k) * p ^ C(k, 2)`. Again an identity, with no hypothesis on `p` or `k`, and §4.1 is
now literally its `k = 3` case.

### The general lemma
Both are instances of `PMC.sum_bweight_mul_card_filter` (`Weighted.lean`): **if every
pattern in a family has `m` elements, the weighted count of patterns contained in a random
subset is `#patterns * p ^ m`.** That is the first moment method stated once. `g` need not
be injective, so coincident patterns are counted with multiplicity and no side condition is
needed.

### subgraph_threshold (§4.2) — proved
`PMC.sum_bweight_mul_card_copies`: the expected number of *labelled* copies of a fixed
graph `H` is exactly `(number of embeddings W ↪ V) * p ^ e(H)`.

Copies are indexed by embeddings rather than by subgraphs, which is the notes' labelled
count and avoids the automorphism factor entirely. The one fact needed beyond the general
lemma is that `Sym2.map` of an injection is injective, so an embedding carries `H` to an
edge set of the same size — Mathlib has `Sym2.map` but no injectivity lemma for it, so it is
proved here.

### The second moment, in the same generality
`PMC.sum_bweight_mul_card_filter_sq` gives the weighted mean of the *square* of a pattern
count as `∑ i, ∑ j, p ^ #(g i ∪ g j)`. No new weight computation was needed: two patterns
are both present exactly when their union is, so `sum_bweight_superset` applies to the pair
unchanged. The diagonal terms give `p ^ #(g i)` and the off-diagonal terms are precisely the
overlap structure the second-moment method turns on.

`PMC.wsecond_moment` is then the method itself: **where a count vanishes, the total weight
is at most `wvar / (wmean) ^ 2`**. It is phrased for an arbitrary set on which the count
vanishes rather than for a `filter`, so no decidability of real equality appears at the call
site.

### random_triangle_second (§4.1, positive direction) — proved
`PMC.sum_bweight_triangleFree_le`: any family of triangle-free graphs carries
`G(n, p)`-weight at most `Var / (C(n,3) p ^ 3) ^ 2`. With `PMC.wmean_card_triangles`
identifying the mean, this is the "typically contains a triangle" half of the threshold in
finite form.

What is left in §4.1 is the *overlap analysis*: bounding
`∑ t, ∑ t', p ^ #(spannedEdges t ∪ spannedEdges t')` explicitly.

**The governing identity is now proved.** `PMC.spannedEdges_inter`: two vertex sets span
exactly the edges of their *intersection* in common. Hence
`PMC.card_spannedEdges_union`:

    #(spannedEdges s ∪ spannedEdges t) + C(#(s ∩ t), 2) = C(#s, 2) + C(#t, 2)

For two `3`-sets that reads `3 + 3 - C(#(s ∩ t), 2)`, i.e. **3, 5, 6, 6** as they share
3, 2, 1, 0 vertices — checked by evaluation, matching the hand analysis. So the overlap
between two potential copies is governed by the overlap of their *vertex* sets and nothing
finer, which is what makes the case analysis finite.

**The two remaining ingredients are now proved.**

* `PMC.wvar_eq_wmean_sq_sub` (`Weighted.lean`): `wvar = E[X²] - (E X)²` when the weights
  total `1`, which is what turns the second moment from
  `sum_bweight_mul_card_filter_sq` into a variance.
* `PMC.card_partners_le` (`Chapter04/Variance.lean`): at most `C(3,2) * n = 3n` triples meet
  a fixed triple in two or more vertices, since such a `t'` is `insert v u` for a `2`-subset
  `u ⊆ t` and a vertex `v`. Checked against the true counts: `10` actual against the bound
  `18` at `n = 6`, `13` against `21` at `n = 7` — a valid over-count, and the factor `n` is
  what matters.

### variance_triangles — proved
`PMC.wvar_card_triangles_le`: **`Var ≤ 3 n C(n,3) p ^ 3`**.

`E[X]² = ∑ over pairs of p ^ 6`, so the pairs sharing at most one vertex — which span
exactly `6` edges — cancel against it *term by term*, and only the `≥ 2`-sharing pairs
survive. Each of those spans `3` or `5` edges, hence contributes at most `p ^ 3` once
`p ≤ 1`, and there are at most `C(n,3) * 3n` of them.

`Var / E² = 3n / (C(n,3) p ^ 3)` is small exactly when `n p → ∞`, so the crude `3n`
over-count loses nothing that matters, and §4.1 is complete in finite form: the first
moment, the second moment, the variance bound, and the triangle-free weight bound
(`sum_bweight_triangleFree_le`) that combines them.

**What is deliberately absent is only the limit statement.** "`G(n,p)` contains a triangle
with high probability when `np → ∞`" is the asymptotic wrapper around these inequalities,
and this project does not state asymptotics.

### Still to do
§4.3's general threshold theorem is the one whose natural statement is genuinely
asymptotic; expect it to stay deferred longest.
