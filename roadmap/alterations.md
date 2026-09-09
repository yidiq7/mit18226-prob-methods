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

## High girth and high chromatic number (§3.4) — proved

`PMC.exists_girth_chromatic`: for all `k, ℓ` there is a finite graph with girth `> ℓ` and
chromatic number `> k` (Erdős 1959).

**This entry previously said the proof "needs a working theory of the Erdős–Rényi random graph,
which this project does not have and Mathlib does not supply", and that it should be its own
phase.** That was wrong twice over. What the proof needs from `G(n,p)` is two first moments,
both of which `ProbMethods/Weighted.lean` already computes for `bweight` on `Finset (Sym2 V)`;
and the asymptotics are avoidable entirely.

Four pieces:

* **`PMC.lt_chromaticNumber_of_mul_indepNum_lt`** — `k · α(G) < #V → χ(G) > k`. The colour
  classes of a proper colouring are independent sets and partition `V`. Mathlib has `indepNum`
  and `chromaticNumber` but not this inequality.
* **`PMC.support_mem_badSets`** — the deterministic heart, and the choice that shrank the whole
  development. A cycle of length `≤ ℓ` has a vertex set `t` with `3 ≤ #t ≤ ℓ` spanning **at
  least `#t` edges**; replacing "carries a short cycle" by that plain edge count is what lets
  the first moment method reach it. No cyclic orderings, no modular `Fin` arithmetic, and the
  probabilistic side never mentions walks. (`#t = L` exactly, because for a closed walk the
  start reappears in the tail — `Walk.support_tail_of_not_nil` plus `Walk.end_mem_support` —
  whose vertices are distinct for a cycle.)
* **the two moments** — `PMC.sum_bweight_card_badSets_le` bounds the expected number of bad
  sets by `∑_{j=3}^{ℓ} C(n,j) C(C(j,2),j) p^j`, via witnesses (`PMC.badPairs`: a `j`-set of
  vertices together with `j` present pairs inside it) so that
  `PMC.sum_bweight_mul_card_filter` applies unchanged. `PMC.sum_bweight_indep_le` is the union
  bound over candidate independent sets, each needing its `C(x,2)` pairs absent
  (`PMC.sum_bweight_disjoint`).
* **`PMC.exists_girth_chromatic_of_good`** — the alteration: delete the least vertex of every
  bad set. No short cycle survives, more than `n/2` vertices remain, and the independence
  number only drops.

**The asymptotics go away when `n` is a power.** With `L = ℓ+1`, `M = 4L-2` and any integer
`r > max(6k, 4L·2^{L²})`, take

    n = r^{M+2},   p = r^{-M},   x = 3 r^{M+1}.

Then `nʲpʲ = r^{2j} ≤ r^{2L}` for every cycle length `j ≤ L`, so the bad-set moment is at most
`L·2^{L²}·r^{2L} < n/4` — an exponent comparison. And `p·C(x,2) ≥ p x²/4 = (9/4) n`, so the
independence bound `2ⁿ e^{-(9/4)n} < 1/2` holds for **every** `r`, since `9/4 > log 2`. The
notes' `p = (log n)²/n` forces "for `n` sufficiently large" at three separate points; powers of
`r` replace all of it with `omega` on exponents, and the only transcendental fact used is
`log 2 < 0.694`.

Stated with `SimpleGraph.egirth`, the `ℕ∞`-valued girth: `girth` is `0` for an acyclic graph,
so "girth `> ℓ`" in that form would additionally demand that the graph *have* a cycle, which
is not what the notes ask. `ℓ < egirth` says exactly "no cycle of length `≤ ℓ`".

Checked numerically before committing: at `(k,ℓ) = (1,1), (2,2), (3,3)` all three numeric
hypotheses hold with large slack (`n ≈ 10^17, 10^46, 10^97`). The parameters are astronomical,
as they are in the notes' proof — the theorem is an existence statement.

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
