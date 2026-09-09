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

## Heilbronn triangle problem (§3.2) — statement published

`PMC.exists_heilbronn_config`: for some absolute `c > 0` and every `n`, there are `n` points of
`[0,1]²` no three of which span a triangle of area below `c/n²`. Statement published as a task;
proof open.

This entry said "deferred on machinery, not on statement", and the second half was right — the
statement is elementary, the area being the determinant `PMC.twiceArea`. What was missing was a
route that stays finite. Three are now recorded:

* the notes' alteration over `([0,1]²)^{2n}` — a random triple has area below `ε` with
  probability `O(ε)` (the base is `O(1)`, so the third point must land in a strip of width
  `O(ε)`), so the expected number of bad triples among `2n` points is `O(ε n³)`, which is below
  `n` at `ε = c/n²`, and deleting one point per bad triple leaves `n`. Needs `Measure.pi` and
  the volume of a strip;
* **a grid**: sample from `(1/N)·[N]²` with `N ≈ n³`. The strip estimate becomes a
  lattice-point count, `PMC.bweight` product weights apply, and the alteration is unchanged.
  The discretisation costs a constant factor in `c`, which the existential absorbs. This is the
  route to try first — it needs nothing this development does not already have;
* the algebraic construction the notes mention — points on the parabola `(x, x²)` over `𝔽ₚ`,
  areas bounded below via Pick's theorem — which stays blocked, Pick's theorem not being in
  Mathlib.

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

## Random greedy colouring (§3.5) — proved

`PMC.twoColorable_of_card_le`: every `k`-uniform hypergraph with at most
`(1/4) · 2^k · √(k / log k)` edges is 2-colourable (Radhakrishnan–Srinivasan 2000, by the
argument of Cherkashin–Kozik 2015). **The constant is explicit**; the notes leave it
existential, and say the small `k` "can be handled exceptionally by later reducing the
constant `c`" — here `k = 2` falls to §1.3's `2^{k-1}` bound, which the hypothesis already
implies at `k = 2`.

This entry previously said the proof "maps each vertex independently and uniformly into
`[0,1]`… a continuous construction", and that a discretisation "is a reformulation to design
rather than a proof to write". The reformulation is small, and two changes made it so.

**Levels instead of the unit interval.** Vertices get independent uniform values in `Fin (32k)`,
so all three events are *product* events over disjoint coordinate blocks and the entire
probabilistic input is `PMC.wprob_unifProd_forall`, already in `ProbMethods/Product.lean`:

* an edge inside `L` or `R` — `(lo/N)^k` and `((N-hi)/N)^k` (`PMC.wprob_lowEvent`,
  `PMC.wprob_highEvent`);
* a conflict whose shared vertex sits at level `j` — the blocks `{v}`, `e \ {v}` and `f \ e` are
  disjoint when `e ∩ f = {v}`, so the probability is exactly
  `(1/N)·((j+1)/N)^{k-1}·((N-j)/N)^{k-1}` (`PMC.wprob_confEvent`). The notes' Beta integral
  `∫_M x^{k-1}(1-x)^{k-1}` is the `N → ∞` limit of the sum of these; the discrete version needs
  only `4(j+1)(N-j) ≤ (N+1)²`, i.e. AM–GM.

Conflicts can only come from pairs meeting in *exactly one* vertex — a second shared vertex
would have to lie both before and after the first (`PMC.inter_eq_singleton_of_conflict`) — which
is why the union bound runs over `≤ m²` pairs.

**A middle block that does not depend on `m`.** The notes minimise over `p` and land on
`p = log(2^{k-1}k/m)/k`. Taking

    p = log k / (2k)

instead, both conditions hold with room to spare: writing `u = m 2^{1-k}`,

    u(1-p)^k < u e^{-pk} = u/√k ≤ 1/(2√(log k)) ≤ 1/2,   u²p ≤ (k/(4 log k))·(log k/(2k)) = 1/8.

`N = 32k` is then large enough that rounding `p` to a multiple of `1/N` and the factor
`(1+1/N)^{2(k-1)} ≤ 2` both stay inside that room, so every estimate is an inequality between
explicit rationals and `log k`.

### pluhar_coloring — the deterministic half, without the recursion

`PMC.exists_bichromatic_of_no_conflict`. The notes colour greedily from left to right, which as
a *definition* makes the colour of `v` depend on every earlier vertex. That recursion is not
needed. Colour `v` **red exactly when `v` is the last vertex of some edge** — non-recursive, and
the same two lines prove it works:

* no edge is all blue: an edge's own last vertex is red;
* no edge is all red: its *first* vertex `v` is red, so `v` ends some edge `f`, and
  `last(f) = v = first(e)` is a conflict.

Ties among vertex values are broken by the vertex index (`PMC.vkey`, the lexicographic key),
which is what makes the induced order total so that every nonempty edge has a first and a last
vertex — `Finset.exists_max_image` and `exists_min_image` then supply them.

Checked numerically before committing, at `k = 3, 4, 5, 6, 8, 12, 20, 40, 100, 400` with
`m = ⌊(1/4)2^k√(k/log k)⌋`: the two block terms total `0.20–0.40` and the conflict term
`0.11–0.14`, so the union bound lands at `0.33–0.51` against the required `< 1` — comfortable
at every `k`, and the slack grows with `k`.

