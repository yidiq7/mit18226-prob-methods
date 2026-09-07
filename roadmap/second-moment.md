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

So the ordering for this chapter is: **build the weighted-counting layer first** (the
`G(n,p)` weights, the expected count of a fixed subgraph, Chebyshev over a finite weighted
space), then state the explicit-constant forms. None of it needs machinery Mathlib lacks.

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
* Chebyshev over a finite uniform space — **not** in Mathlib in that form, and it should be
  authored at the centralized layer, since Chapters 4, 5 and 9 all want it;
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

## Random graph sections (§4.1–4.4) — pending the weighted-counting layer

4.1 (does a typical random graph contain a triangle), 4.2 (thresholds for fixed subgraphs),
4.3 (thresholds), 4.4 (clique number). All follow once the layer above exists, in
explicit-constant finite-`n` form. 4.3's general threshold theorem is the one whose natural
statement is genuinely asymptotic; expect it to stay deferred longest.
