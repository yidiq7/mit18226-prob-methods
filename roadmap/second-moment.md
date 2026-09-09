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

## One modelling point, worth stating plainly

The ground set is `Sym2 V`, which **includes the diagonal**: `N = card (Sym2 V) = n(n+1)/2`,
not `C(n,2)`. So the weight `PMC.bweight p` tosses `n` extra coins, one per loop `s(v,v)`.

This does not affect anything proved here, and the reason is worth recording rather than
rediscovering. Every event and count in Chapters 4 and 8 is a function of the *off-diagonal*
coordinates only — `PMC.spannedEdges t` contains no loop, so `HasTriangle`, `triangles`,
`cliqueSets`, and the copies of `H` never look at one — and the marginal of the off-diagonal
coordinates under `bweight p` is exactly independent `Bernoulli(p)`. The loop coins integrate
out.

Where it *would* bite is a statement about the whole edge set, e.g. "`P(G` is empty`)`", which
here is `(1-p)^{n(n+1)/2}` rather than `(1-p)^{C(n,2)}`. No such statement is claimed.

## Corollary 4.1.8 — proved

`PMC.tendsto_wprob_zero_of_var_div_sq_mean`: if `Var X_n = o((E X_n)²)` along a sequence of
finite weighted spaces then the weight of `{X_n = 0}` tends to `0`. `PMC.wsecond_moment`
divided by `(E X)²` and squeezed.

Stated over a *family* of spaces `Ω : ℕ → Type*`, which is what an asymptotic statement about
`G(n,p)` needs — the sample space changes with `n` — and which costs nothing in Lean. The
concrete instance is §4.1's threshold, where `Ω n = Finset (Sym2 (Fin n))`.

## Weierstrass approximation (§4.7) — UPSTREAM

Theorem 4.7.1 is in Mathlib as `bernsteinApproximation_uniform`
(`Mathlib/Analysis/SpecialFunctions/Bernstein.lean`), which is exactly the Bernstein-polynomial
proof the notes give — down to the variance computation `bernstein.variance`, which is the
notes' `Var(X̄) = x(1-x)/n`. Recorded as `upstream`; never published as a task.

**The bridge is now proved**: `PMC.exists_polynomial_approx`
(`ProbMethods/Chapter04/Weierstrass.lean`) states the theorem in the notes' form — for every
`ε` there is a polynomial uniformly within `ε` on `[0,1]` — and derives it from Mathlib's
density statement. Worth having for the same reason the FKG bridge in Chapter 7 was: Mathlib
says "the polynomial functions are dense in `C([a,b], ℝ)`" and an application wants an
explicit `ε`, so the unravelling should happen once.

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

## Theorem 4.6.6 (Dubroff–Fox–Xu) — proved, modulo Harper

`ProbMethods/Chapter04/DubroffFoxXu.lean`. `PMC.choose_le_of_distinct_subset_sums`: if `k`
integers bounded by `n` have distinct subset sums then `C(k, ⌊k/2⌋) ≤ n` — the best known
leading constant for §4.6's problem, and a 2021 result.

The reduction, which is the paper's content, is proved in full:

* `PMC.card_lowHalf` — the subsets summing to *below* half the total are exactly half of the
  `2^k` subsets. Distinctness is what rules out summing to exactly half (that subset would tie
  with its complement), so complementation pairs every subset with exactly one of the two
  sides.
* `PMC.card_boundary_lowHalf_le` — the vertex boundary has at most `n` points. A boundary point
  is an *insertion* `S ∪ {i}`, never an erasure, because erasing only lowers the sum and would
  keep the point inside; so its sum lies strictly between `T/2` and `T/2 + n`, an interval
  holding at most `n` integers, and distinctness makes the sum injective on the boundary.

Harper's inequality is an **explicit hypothesis**, in the boundary form the proof needs: a set
of size exactly `2^{k-1}` has at least `C(k, ⌊k/2⌋)` boundary points. It is not derived from the
ball form (task #46) because for even `k` the extremal set is a ball *plus part of one level*,
which the ball form does not reach.

**A statement bug caught by a numeric check, worth recording.** The hypothesis was first
written with `2^{k-1} ≤ #A` rather than `#A = 2^{k-1}`. That version is false — at `A = univ`
the boundary is empty — so the theorem would have been vacuously true while looking right.
Brute force over `k ≤ 4` found it, and also confirmed the equality version is true *and tight*:
the minimum boundary of a half-cube-sized set is exactly `C(k, ⌊k/2⌋)` for `k = 1, 2, 3, 4`.
The lesson: an assumed hypothesis needs its own sanity check, because a false one makes
everything downstream provable.

## Hardy–Ramanujan (§4.5) — not yet stated

The number of distinct prime divisors `ω(m)` concentrates around `log log n` for `m` drawn
uniformly from `[n]`. The distribution *is* uniform, so counting applies, and Mathlib has
`ω` as `Nat.ArithmeticFunction.cardDistinctFactors`. What it needs beyond that is
Mertens-type estimates on `∑ 1/p`, which is where the work is. Stateable in explicit form;
not attempted yet.

## §4.1's threshold, asymptotically — proved

`ProbMethods/Chapter04/TriangleThreshold.lean`. Both halves of the triangle threshold, in the
notes' own phrasing:

* `PMC.tendsto_probTriangleFree_one` (Proposition 4.1.2): `np → 0` ⟹ `G(n,p)` is triangle-free
  with probability `1 - o(1)`. First moment and Markov: `E[#triangles] = C(n,3)p³ ≤ (np)³/6`.
* `PMC.tendsto_probHasTriangle_one` (Theorem 4.1.11): `np → ∞` ⟹ `G(n,p)` contains a triangle
  with probability `1 - o(1)`. Second moment:
  `P(triangle-free) ≤ 1/(C(n,3)p³) + 3n/(C(n,3)p) ≲ 1/(np)³ + 1/(n²p)`, and both terms vanish
  once `np → ∞` — the second because `n²p = n·(np)`.

**This did not require changing the convention on asymptotics.** The limit statements sit *on
top of* explicit bounds (`PMC.probHasTriangle_le`, `PMC.probTriangleFree_mul_le`) rather than
in place of them, and each limit is a few lines of `Filter` work once the bound is there. The
sample space is `Finset (Sym2 (Fin n))` for each `n` and the asymptotics live in
`Filter.Tendsto` over `n`; nothing about the finite framework had to move.

**The sharper variance was the real work** (`PMC.wvar_card_triangles_le'`):

    Var ≤ C(n,3)(p³ + 3n p⁵).

The earlier `PMC.wvar_card_triangles_le` bounds every overlapping pair by `p³`, which gives
`P(triangle-free) ≲ 1/(n²p³)` — and that does *not* vanish throughout `np → ∞`; at
`p = n^{-9/10}` it diverges, so the cruder bound cannot prove Theorem 4.1.11 at all. Keeping
the two overlap classes apart is what fixes it: `t' = t` contributes `p³` and there is one such
term, while `#(t ∩ t') = 2` contributes `p⁵` and there are at most `3n` such `t'`. This is the
"overlap analysis" the second-moment section previously flagged as remaining work.

## §4.2, §4.4 — the first-moment halves — proved

`ProbMethods/Chapter04/CliqueThreshold.lean`. One statement covers both:
`PMC.tendsto_probHasClique_zero` — the probability of containing a `k`-clique vanishes as soon
as the expected number `C(n,k)p^{C(k,2)}` does (`PMC.probHasClique_le` is Markov, on top of
`PMC.sum_bweight_mul_card_cliqueSets`). Its two instances are the notes':

* `PMC.tendsto_probHasClique_four_zero` — Theorem 4.2.5's first half: `n⁴p⁶ → 0`, i.e.
  `p ≪ n^{-2/3}`, gives no `K₄` whp;
* `PMC.tendsto_probHasClique_half_zero` — Theorem 4.4.2(a): `f(n,k) = C(n,k)2^{-C(k,2)} → 0`
  gives `ω(G(n,1/2)) < k` whp.

`PMC.tendsto_probHasCopy_zero` is the same first moment for an **arbitrary** `H` — Theorem
4.2.10's first half for `H` itself: `n^{v(H)}p^{e(H)} → 0` gives no copy of `H` whp, via
`PMC.sum_bweight_mul_card_copies` and `Fintype.card_embedding_eq`. The notes' sharper form runs
the argument on the *densest subgraph* `H'` of `H` (since `X_{H'} = 0` already forces
`X_H = 0`), which needs the maximum edge–vertex ratio `m(H)` as a separate construction; that
is not built here and is the honest gap between this and 4.2.10 as stated.

The second-moment halves are *not* proved: 4.2.5's other direction, 4.2.10's other direction
and 4.4.2(b) all need `Δ*` for the relevant family, whose overlap analysis is the general
analogue of `PMC.wvar_card_triangles_le'` — and as §4.1 showed, a crude version of that bound
does not reach the threshold at all.

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

### bollobas_thomason — Lemma 4.3.7

`PMC.sum_bweight_notMem_le_pow` (`ProbMethods/Chapter04/BollobasThomason.lean`):
`P(Ω_p ∉ F) ≤ P(Ω_{p/m} ∉ F)^m` for upward-closed `F`. Statement published as a task; proof
open.

This is the non-asymptotic engine behind **Theorem 4.3.6** ("every sequence of non-trivial
monotone properties has a threshold"), which the notes derive from it — so it is the piece
worth having, and 4.3.6 follows from it without further probability. Two steps, only the first
a coupling:

* `m` independent copies of `Ω_{p/m}` have union distributed as `Ω_q` with
  `q = 1 - (1-p/m)^m`, and upward-closure makes "union outside `F`" imply "every copy outside
  `F`", so independence gives the `m`-th power;
* `q ≤ p` by Bernoulli, and `p ↦ P(Ω_p ∉ F)` is *antitone* — the non-strict form of task #50
  (`PMC.strictMonoOn_sum_bweight`), provable directly by the same one-coordinate coupling.

Stated without the notes' non-triviality hypothesis on `F`, which the inequality does not need:
at `F = ∅` both sides are `1`, and at `F = univ` the left side is `0`.

### threshold_exists — Theorem 4.3.6

`PMC.exists_isThreshold`, with `PMC.IsThreshold` as Definition 4.3.1: every sequence of
non-trivial monotone properties has a threshold. Statement published as a task; proof open.

The notes single 4.3.6 out as the reason Lemma 4.3.7 is worth having, so the two are published
as a pair — 4.3.7 (task #57) is the non-asymptotic content, and this is the asymptotic
wrapper. Take `q n` to be the `p` at which the probability is exactly `1/2`; it exists because
`p ↦ ∑_{X ∈ F n} bweight p X` is a polynomial, hence continuous, and is `0` at `p = 0` and `1`
at `p = 1` — those two endpoint facts are `PMC.notMem_empty_of_monotone` and
`PMC.mem_univ_of_monotone`, which is exactly what non-triviality buys. Then 4.3.7 gives
`P(Ω_p ∈ F) ≤ 1 - 2^{-1/m}` below the threshold and `≥ 1 - 2^{-m}` above it, and `m → ∞`
finishes both directions.

Remark 4.3.3 (two thresholds differ by a bounded factor, so one may say *the* threshold) is not
part of the statement.
