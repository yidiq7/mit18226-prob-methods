# Chapter 3 — Alterations

The chapter's method is: make a random construction, then repair the blemishes. Chapter 1's
`ramsey_alteration` already used it; here it is the organising idea.

Of the five sections, one is formalized, one is upstream in Mathlib, and three are recorded
below with the specific obstacle that keeps them out of this phase. As elsewhere in this
project, the reason is written down so it is not rediscovered.

## Dominating sets (§3.1)

`PMC.IsDominating` (`ProbMethods/Basic.lean`): `U` is dominating in `G` when every vertex
outside `U` has a neighbour in `U`.

### dominating
`PMC.exists_isDominating_card_le` — Theorem 3.1.1.

A graph with minimum degree `δ > 1` has a dominating set of size at most
`((log (δ + 1) + 1) / (δ + 1)) * n`.

Zhao's proof is the two-step alteration. Include each vertex independently with probability
`p` to get `X`; let `Y` be the vertices neither in `X` nor adjacent to `X`, so `X ∪ Y`
dominates by construction. A vertex lands in `Y` with probability at most
`(1 - p) ^ (1 + δ)`, so `E|X ∪ Y| ≤ (p + exp (-p (1 + δ))) * n` using `1 + x ≤ exp x`, and
`p = log (δ + 1) / (δ + 1)` minimises the bracket.

**This is the first node whose distribution is not uniform** — it is `Bernoulli p` with `p`
generally irrational — so the counting convention that carried Chapters 1 and 2 does not
apply. It does *not* follow that `MeasureTheory` is needed. Over a finite vertex set the
expectation is a finite weighted sum

    ∑ X ∈ univ.powerset, p ^ #X * (1 - p) ^ (n - #X) * f X

and `Finset.prod_add` gives `∑ X, p ^ #X * (1 - p) ^ (n - #X) = (p + (1 - p)) ^ n = 1`.
Averaging against those weights is the entire probabilistic content, and it is elementary.
Expect later chapters to reuse this device wherever the parameter is a real number.

## Heilbronn triangle problem (§3.2) — DEFERRED

Theorem 3.2.3: for every `n` there are `n` points in the unit square with every triple
spanning a triangle of area at least `c n⁻²`.

Deferred on machinery, not on statement: the statement is expressible (the constant is
existential), but the proof integrates over an annulus to bound
`P(area(p,q,r) ≤ ε)`, which is integral geometry over `ℝ²`. The algebraic alternative the
notes give — points on the parabola `(x, x²)` over `𝔽ₚ`, with areas bounded below by Pick's
theorem — replaces analysis with lattice geometry, but Pick's theorem is not in Mathlib
either. Revisit if either becomes available.

## Markov's inequality (§3.3) — UPSTREAM

Theorem 3.3.1 is in Mathlib as `MeasureTheory.mul_meas_ge_le_lintegral` and
`MeasureTheory.meas_ge_le_lintegral_div` (`Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`).
Recorded as `upstream`; never published as a task.

## High girth and high chromatic number (§3.4) — not yet stated

Theorem 3.4.1 (Erdős 1959): for all `k, ℓ` there is a graph with girth `> ℓ` and chromatic
number `> k`.

The statement is clean and finite, and it is a genuinely appealing target. The proof is not:
it takes `G(n, p)` with `p = (log n)² / n`, bounds the expected number of short cycles,
applies Markov to delete them, and bounds the independence number — every step asymptotic
in `n`, with "for `n` sufficiently large" throughout. That needs a working theory of the
Erdős–Rényi random graph, which this project does not have and Mathlib does not supply.
Opening it means building that first, and it should be its own phase rather than a task
appended here.

## Random greedy colouring (§3.5) — not yet stated

Theorem 3.5.1 (Radhakrishnan–Srinivasan 2000): there is a constant `c > 0` such that every
`k`-uniform hypergraph with at most `c * sqrt (k / log k) * 2 ^ k` edges is 2-colourable.
This strengthens `property_b_lower` (§1.3), which is proved.

The constant is existential, so the statement is expressible. The proof maps each vertex
independently and uniformly into `[0, 1]` and splits the interval into `L`, `M`, `R` — a
continuous construction, and unlike §3.1 the weights are not a finite Bernoulli product
over subsets, since the ordering induced on the vertices is what carries the argument. A
discretisation (random ordering plus a random three-way split of the positions) looks
workable and would keep it finite, but that is a reformulation to design rather than a
proof to write, so it is not stated yet.
