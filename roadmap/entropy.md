# Chapter 10 — Entropy

Zhao, *Probabilistic Methods in Combinatorics*, Chapter 10.

**Section numbering, read off the notes' own table of contents** (an earlier version of this
file had it wrong, which is worth flagging because the mistake was silent):

| § | Title | Status |
|---|---|---|
| 10.1 | Basic properties | proved, incl. the binomial tail bound in both forms |
| 10.2 | Permanent, perfect matchings, Steiner triple systems | not started |
| 10.3 | Sidorenko's inequality | not started |
| 10.4 | Shearer's lemma | **complete** — Thms 10.4.1, 10.4.3, 10.4.5, 10.4.9; Cors 10.4.6, 10.4.7 |

The named results now in the library: **Theorem 10.4.1** (`PMC.wentropy_shearer_triple`),
**Theorem 10.4.3** (`PMC.loomis_whitney`), **Theorem 10.4.5** (`PMC.shearer`),
**Corollary 10.4.7** (`PMC.card_pow_le_prod_card_projSet`), and Corollary 10.4.6 as the same
counting theorem at `k = n - 1`. `PMC.card_orderedTriangles_sq_le` is *not* a numbered
result — §10.4's own triangle theorem is 10.4.9 about triangle-*intersecting* families.

## What Mathlib has, and what it doesn't

Mathlib has the *analytic* groundwork and nothing above it:

* `Real.negMulLog` (`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`) — `-x log x`
  with concavity, derivatives, and `negMulLog_nonneg` on `[0,1]`. This is the right base.
* `Real.binEntropy` (`Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean`).
* `Mathlib/InformationTheory/` holds coding theory and Kullback–Leibler for measures —
  not the entropy of a finite random variable.

There is **no** entropy of a random variable, no subadditivity, no chain rule, no Shearer.
So Chapter 10 needs its own layer, and `ProbMethods/Chapter10/Entropy.lean` is it: a random
variable is a function `X : Ω → β` on the weighted sample space, `PMC.wdist` is its
distribution, and `PMC.wentropy w X = ∑ b, negMulLog (P (X = b))` is its entropy in nats.

## Status

| Piece | Status |
|---|---|
| `PMC.sum_mul_log_div_le` — Gibbs' inequality | proved |
| `PMC.wdist`, `PMC.sum_wdist`, `PMC.wdist_le_one` | proved |
| `PMC.wentropy`, `PMC.wentropy_nonneg` | proved |
| `PMC.wentropy_le_log_card` — uniform maximises entropy | proved |
| `PMC.wentropy_pair_le` — subadditivity `H(X,Y) ≤ H(X) + H(Y)` | proved |
| `PMC.wcondDist`, `PMC.wcondEntropy` | proved |
| `PMC.wentropy_chain` — chain rule `H(X,Y) = H(X) + H(Y\|X)` | proved |
| `PMC.wcondEntropy_le` — conditioning reduces entropy | proved |
| `PMC.wentropy_equiv` — relabelling invariance | proved |
| `PMC.wentropy_submodular` — `H(X,Y,Z) + H(X) ≤ H(X,Y) + H(X,Z)` | proved |
| `PMC.wcondEntropy_le_of_pair` — `H(Y\|X,Z) ≤ H(Y\|X)` | proved |
| `PMC.wentropy_congr` — entropy depends only on the fibres | proved |
| `PMC.wentropy_comp_le` — `H(f ∘ Z) ≤ H(Z)` | proved |
| `PMC.masked`, `PMC.tupleEntropy` and its three properties | proved |
| `PMC.shearer_of_submodular` — Shearer for set functions | proved |
| **`PMC.shearer` — Shearer's lemma** | proved |
| `PMC.wentropy_le_log_card_image` — `H(Z) ≤ log #(attained values)` | proved |
| `PMC.wentropy_uniform_of_injective` — `H = log \|Ω\|` | proved |
| `PMC.card_pow_le_prod_card_projSet` — Shearer as a count | proved |
| **`PMC.loomis_whitney`** — Thm 10.4.3 | proved |
| **`PMC.loomis_whitney_general`** — Cor 10.4.6 | proved |
| **`PMC.card_orderedTriangles_sq_le`** — the triangle bound | proved |
| `PMC.shearer_subset` — Shearer for a sub-tuple | proved |
| `PMC.wentropy_add_wmean_le_log_sum_exp` — Gibbs variational principle | proved |
| `PMC.tupleEntropy_union_le` — block subadditivity | proved |
| `PMC.wcondEntropy_masked_antitone` — `H(X_i\|X_T) ≤ H(X_i\|X_S)` | proved |
| `PMC.condProd`, `PMC.sum_condProd` — conditionally independent copies | proved |
| **`PMC.card_matchSet_le_prod`** — Brégman, Thm 10.2.1 | proved |
| **`PMC.card_indepSets_pow_le`** — Kahn–Zhao, Thm 10.4.12 | proved |
| `PMC.mul_tupleEntropy_univ_le` — the bipartite entropy skeleton | proved |
| `PMC.wcondEntropy_congr_left` — `H(Y\|Z)` depends only on `Z`'s fibres | proved |
| `PMC.card_kddHom` — `hom(K_{d,d},H) = ∑_a #commonNbhd(a)^d` | proved |
| **`PMC.card_homSetR_pow_le`** — Galvin–Tetali, Thm 10.4.14 | proved |

## The one trap: `log 0 = 0`

Everything here rests on Gibbs' inequality, `∑ P log (Q/P) ≤ 0`. Under Mathlib's convention
`log 0 = 0` **that statement is false as usually written**: take `P = (½,½)` and
`Q = (1,0)`, where the second term contributes `½ · log 0 = 0` instead of `-∞` and the sum
comes out `½ log 2 > 0`. So `PMC.sum_mul_log_div_le` carries an explicit absolute-continuity
hypothesis `hac : ∀ b, P b ≠ 0 → Q b ≠ 0`.

In both applications the hypothesis is free, and for the same reason each time: a marginal
is positive wherever the joint distribution is, because `PMC.wprob` is monotone and the
joint event's fibre sits inside the marginal's. Expect to discharge `hac` that way in the
chain rule and in Shearer too.

## Sanity checks performed

The definitions were pinned down numerically before anything was built on them: a constant
random variable has entropy `0`, and a fair coin has entropy `log 2`. Both are `example`s
that compiled. Worth doing for any *definition* that later theorems are stated in terms of
— a subtly wrong `wdist` would have made every theorem here true and meaningless.

## The chain rule, and the empty-fibre convention

`PMC.wentropy_chain` is termwise Mathlib's `Real.negMulLog_mul` applied to the
factorisation `P(X = b, Y = c) = P(X = b) · P(Y = c | X = b)`. The one place it needs
thought is the fibres where `P(X = b) = 0`: there `wcondDist` is `0/0 = 0` and does *not*
sum to one, so the factorisation argument does not apply — but both sides vanish on such a
fibre, so the identity holds with **no side condition**. Defining `wcondDist` by plain
division, and taking Lean's `x/0 = 0`, is what buys that.

`PMC.wcondEntropy_le` (`H(Y|X) ≤ H(Y)`) then falls straight out of the chain rule and
subadditivity: the two inequalities are the same fact read in opposite directions.

## Submodularity, and one Lean-level annoyance

`PMC.wentropy_submodular` is Gibbs against `Q(x,y,z) = P(x,y) P(x,z) / P(x)`. Two things
worth knowing before writing the next one of these:

* **`Fintype.sum_prod_type` leaves projections behind.** Rewriting `∑ q : β × γ × δ` into
  `∑ b, ∑ c, ∑ d` produces summands containing `(c, d).1`, not `c`. Those are *definitionally*
  `c` but not syntactically, so every subsequent `rw [← Finset.sum_mul]` fails with
  "pattern not found" for no visible reason. The fix that worked is the private helper
  `sum_triple`, stated with `f` in **curried** form: its own proof closes by `exact` (which
  is up to defeq), and callers instantiate `f` explicitly, so `rw` never has to guess a
  higher-order pattern and the result comes back projection-free.
* **`set` fights defeq here.** Abbreviating the distributions with `set` means every
  hypothesis produced *after* the `set` (e.g. from `wdist_nonneg`) mentions the unfolded
  form while the goal mentions the abbreviation, and each `rw` then needs a direction-correct
  `hPX`. Writing the terms out in full was shorter overall.

## Shearer: where to make the cut

`PMC.shearer` is proved, and the thing worth remembering is *where the proof was split*.
The entropy side ends at three facts about the set function `S ↦ H(X_S)`
(`ProbMethods/Chapter10/Entropy.lean`):

* `PMC.tupleEntropy_empty` — normalised at `∅`;
* `PMC.tupleEntropy_mono` — monotone;
* `PMC.tupleEntropy_submodular` — submodular in diminishing-returns form.

**Everything after that has no entropy in it.** `PMC.shearer_of_submodular`
(`ProbMethods/Chapter10/Shearer.lean`) proves Shearer for *any* normalised monotone
submodular set function, and `PMC.shearer` is the one-line instance. That cut is worth
copying for the other Chapter 10 results: the combinatorial half is where the content is,
it is reusable, and it can be checked without knowing what entropy is.

The mechanism is the chain decomposition `PMC.sum_chain_eq`: fixing a linear order,
`f S = ∑ i ∈ S, (f (insert i (S ∩ prefixLt i)) - f (S ∩ prefixLt i))`, which telescopes on
peeling off `max' S`. Submodularity then replaces each increment by the one taken over the
*whole* prefix — which no longer depends on `S`, so the family can be summed and each
coordinate's multiplicity counted.

Two representation choices that paid off:

* **Masking, not restriction.** `PMC.masked X S ω i = if i ∈ S then some (X i ω) else none`,
  so every `X_S` has the *same* type `ι → Option β`. Restricting to a subtype would put
  `X_S` and `X_T` in different types and force dependent-type bookkeeping at every step.
  `Option β` rather than a default value avoids requiring `Inhabited β` and keeps "erased"
  distinguishable from every real value.
* **`PMC.wentropy_congr` stated via mutual determination**, not via a bijection of value
  types. `X_{S ∪ T}` and `(X_S, X_T)` carry the same information but their value types admit
  no bijection at all; what is true is that explicit maps `g`, `h` invert each other *along
  the ranges*, which is exactly what the lemma asks for.

## Counting with entropy

`PMC.card_pow_le_prod_card_projSet` is the general counting form of Shearer, and
`PMC.loomis_whitney` its `Fin 3` instance. The conversion from entropy to counts has exactly
two halves, and both are worth having as named lemmas:

* `PMC.wentropy_uniform_of_injective` — under the uniform weight on `A`, the *whole* tuple
  determines the point, so its entropy is `log #A` **exactly**. This is the lower half.
* `PMC.wentropy_le_log_card_image` — a mask takes at most `#(trace of A on S)` values, so
  its entropy is at most the log of that. Note this had to be the *image* version:
  `PMC.wentropy_le_log_card` bounds by the size of the whole value type, which here is
  `#(ι → Option β)` and useless. The quantity the combinatorics is about is always the
  number of values actually attained.

Traces are recorded as masked tuples (`PMC.projSet`), matching the representation choice
made for `PMC.tupleEntropy`, so the two fit together with no conversion.

**Checked tight, not merely true:** the full `2 × 2 × 2` cube has `8` points and three
`4`-point shadows, and `8² = 64 = 4 · 4 · 4`. A loose or mis-stated exponent would not
achieve equality, so this is a stronger check than non-vacuity.

## The triangle bound reuses the Loomis–Whitney instance exactly

`PMC.card_orderedTriangles_sq_le`: `t² ≤ (2m)³` where `t` counts *ordered* triangles, so
`#triangles ≤ (2m)^{3/2}/6`. What is worth noticing is that this is **the same Shearer
instance** as Loomis–Whitney — `ι = Fin 3`, `k = 2`, the three 2-subsets — with exactly one
extra observation: the trace of the ordered triangles on any two coordinates consists of
*ordered edges*, of which there are `2m`. So the general counting form did all the work and
the graph theory contributed one line.

The two supporting lemmas are worth keeping separate:

* `PMC.card_orderedEdges` — there are exactly `2m` ordered edges, by fibring over the first
  endpoint and quoting Mathlib's handshake lemma.
* `PMC.card_projSet_pair_le` — a two-coordinate trace injects into any set of pairs
  containing the corresponding pairs. Stated for arbitrary indices and an arbitrary target,
  so the caller supplies only the adjacency fact and nothing about triangles.

Counts were `#eval`-checked rather than assumed: `24` ordered triangles and `12` ordered
edges on `K₄` (against `4·3·2` and `2·6`), and `0` and `8` on a 4-cycle. The bound is
asymptotically tight on `K_n`, where the two sides' ratio tends to `1`.

## Next

Two things:



## §10.2 — the random-order machinery is in place

`ProbMethods/RandomOrder.lean`. Radhakrishnan's proof of Brégman–Minc reveals the rows in a
uniformly random order, and its one distributional input is the step the notes leave as an
exercise ("(Why?)"): for a fixed row, the number of *greedily available* choices is uniform
on `{1, …, d}`.

Stripped of the setting, that is a fact about a uniformly random permutation `τ` and a fixed
`S`: the **rank** of `i ∈ S` — how many members of `S` are revealed at or after `i` — is
uniform on `{1, …, #S}` (`PMC.wprob_tauRank_eq`). Two observations give it:

* `PMC.card_filter_tauRank_eq_one` — for each `τ`, *exactly one* member of `S` has rank `k`;
  the rank is a bijection from `S` onto `{1, …, #S}`, by strict monotonicity.
* `PMC.card_filter_tauRank_congr` — the ranks are equidistributed across the members of `S`,
  since right-multiplying `τ` by `Equiv.swap i i'` exchanges their roles and preserves `S`.

Summing the first over `i ∈ S` and applying the second gives `#S` classes of equal size.

**This needs no order machinery, and that was the design choice worth making.** The obvious
route — pick out the `k`-th smallest element of `τ(S)` and swap it into place — needs
`Finset.orderIsoOfFin` and sorted lists; double counting needs only a transposition. The
`LinearOrder` is used only to *say* what "revealed after" means.

`PMC.wmean_log_tauRank` then gives Brégman's per-row bound `E[log(rank)] = log(d!)/d`. It is
stated through `PMC.wmean_comp_tauRank`, which takes an arbitrary `f`, because the
distribution and not the function is the content.

Checked numerically on `Fin 3`: uniform over the three ranks with two orders each, and on the
proper subset `{0,2}`, two ranks with three orders each.

### The other two entropy inputs are proved

* `PMC.wcondEntropy_le_sum_log_card` (`CondSupport.lean`) — **conditional entropy is at most
  the expected log of the conditional support**: if `Y ω ∈ T (X ω)` always, then
  `H(Y | X) ≤ ∑_b P(X = b) log #(T b)`. This is the step that turns entropy back into
  counting; in the application `T b` is the set of columns still free for a row once the
  earlier rows are known. It rests on `PMC.sum_negMulLog_le_log_card`, the same fact stated
  for a bare *distribution* — which is what makes it reusable here, since a conditional
  distribution is a `PMC.wcondDist` with no underlying map to speak of. Fibres of probability
  zero contribute nothing to either side, so there is no side condition.

* `PMC.tupleEntropy_univ_eq_sum_predSet` (`OrderChain.lean`) — **the chain rule along an
  arbitrary order**: for every permutation `τ`,
  `H(X_univ) = ∑ᵢ H(Xᵢ | X_{predecessors of i})`. A telescoping sum over the prefixes of `τ`
  (`Finset.sum_range_sub`), reindexed by `τ.symm`, on top of `PMC.tupleEntropy_insert`
  (adding one coordinate to a mask adds exactly that coordinate's conditional entropy).

That identity holding for *every* order is the structural half of Radhakrishnan's proof; the
probabilistic half is averaging over a random one.

### Theorem 10.2.1 (Brégman–Minc) — proved

`PMC.card_matchSet_le_prod` (`Chapter10/Bregman.lean`): a `0-1` matrix whose `i`-th row has
`dᵢ` ones has permanent at most `∏ᵢ (dᵢ!)^{1/dᵢ}`.

The assembly, in the order it was built:

1. `PMC.card_avail_eq_tauRank` — **the combinatorial identity the notes leave implicit.** The
   columns of row `i` not yet taken correspond, via `σ⁻¹`, to the members of `PMC.hitSet` that
   `τ` reveals at or after `i`: each one of row `i` sits in the column `σ j` for exactly one
   row `j`, and it is still available precisely when that `j` has not been revealed. This is
   what makes the abstract rank lemma applicable to a matrix.
2. `PMC.tupleEntropy_matchCoord_univ` — `H(σ) = log (per A)`, since a uniform matching is
   determined by its coordinates. The no-matchings case is separate; there both sides are `0`.
3. `PMC.log_card_matchSet_le` — the bound for one *fixed* order: chain rule along `τ`, then
   each conditional entropy bounded by the log of the free columns.
4. `PMC.log_card_matchSet_le_sum_log_factorial` — average over `τ`, exchanging the two
   expectations with `Finset.sum_comm`.

**The point of the whole proof, in one line**: bounding each conditional entropy by `log dᵢ`
— the naive worst case, which the notes flag as "too lossy" — would give
`per A ≤ ∏ dᵢ`; revealing in a random order replaces `log dᵢ` by the *average* of
`log 1, …, log dᵢ`, which is `log(dᵢ!)/dᵢ`.

**Checked against the equality cases**, which is the strongest evidence available that the
constant is right, since a mis-stated exponent would break them: the all-ones `3×3` matrix has
`per = 6 = ∏ (3!)^{1/3}`, a permutation matrix has `per = 1 = ∏ (1!)^{1}`, and the `2+1`
block-diagonal matrix has `per = 2 = (2!)^{1/2}(2!)^{1/2}·1`. A strict case was checked too
(rows `{0,1}, {0}` on `Fin 2`: `per = 1 < √2`).

### Corollary 10.2.2, bipartite case — proved

`PMC.card_matchSet_sq_le_prod`: for a bipartite graph,
`pm(G)² ≤ ∏_{x ∈ X} (d_x!)^{1/d_x} · ∏_{y ∈ Y} (d_y!)^{1/d_y}`, i.e.
`pm(G) ≤ ∏_v (d_v!)^{1/(2d_v)}` over all `2n` vertices. Brégman applied to each side in
turn, which needs the permanent to be transpose-invariant — that is the inversion `σ ↦ σ⁻¹`
(`PMC.card_matchSet_colOf`, checked on an asymmetric example).

### Theorem 10.2.6's Brégman step — proved; its asymptotic form is not

`PMC.card_hamCycleSet_le_prod`: the number of Hamilton cycles of a tournament is at most
`∏ᵢ (dᵢ!)^{1/dᵢ}`, with `dᵢ` the out-degree. In this encoding the notes' first inequality —
a Hamilton cycle *is* a `1`-factor — is literally a subset relation, so the content is
Brégman. Checked on the cyclic tournament on `Fin 3` (`per = 1`, bound `1`, equality) and the
transitive one (`per = 0`, since the sink has out-degree `0`).

**Theorems 10.2.6 and 10.2.4 themselves are not claimed.** Reaching `O(√n · n!/2ⁿ)` needs
log-concavity of `x ↦ (x!)^{1/x}` — which the notes state as "One can check (omitted)" — plus
a smoothing argument over degree sequences of total `C(n,2)`, and Stirling. That is an
analysis project, not a missing line, so the log-concavity is published as a task
(`PMC.factorial_rpow_log_concave`).

**Erratum (Theorem 10.2.6's omitted step).** The notes write "the function `g(x) = (x!)^{1/x}`
is log-concave, i.e., `g(n) g(n+2) ≥ g(n+1)²` for all `n ≥ 0`". The displayed inequality is
log-*convexity* and is **false for every `n ≥ 1`**: at `n = 1` it reads `1 · 6^{1/3} ≥ 2`,
i.e. `1.817 ≥ 2`. The word is right and the inequality is flipped. Checked numerically for
`n` up to 4000: the notes' direction fails at every `n ≥ 1`, and the concave direction holds
at every `n ≥ 1`, failing only at `n = 0` — where `(0!)^{1/0}` is a convention artifact, so
the committed statement carries `1 ≤ m`. The smoothing argument needs the concave direction,
so this is a typo rather than a hole in the proof.

**Only the bipartite case of Corollary 10.2.2 is claimed, and that is deliberate.** The notes derive the general
statement from `pm(G ⊔ G) ≤ pm(G × K₂)`, which they leave as an exercise — and that
inequality, not the appeal to Brégman, is the actual content of Kahn–Lovász. Formalizing the
general case means proving that exercise, which is a separate combinatorial project.

<!-- superseded plan -->
**The former plan for Theorem 10.2.1** was: take `σ` uniform on the permutations
compatible with the matrix, so `PMC.wentropy_uniform_of_injective` gives
`H(σ) = log (per A)`; apply the order chain rule for each fixed `τ`; bound each conditional
term by `PMC.wcondEntropy_le_sum_log_card` with `T` the free columns; then average over `τ`
and use `PMC.wmean_log_tauRank` for the per-row `log (dᵢ!)/dᵢ`, exchanging the two
expectations with `Finset.sum_comm`.

* **§10.2** — Theorem 10.2.1 (Brégman–Minc): `per A ≤ ∏ (dᵢ!)^{1/dᵢ}` for a 0–1 matrix with
  row sums `dᵢ`. **Harder than anything in §10.4**, and worth knowing why before starting:
  Radhakrishnan's proof reveals the chosen entries in a *uniform random order*, so it needs
  conditional entropy over a random permutation of the rows — a second layer of randomness
  on top of the permutation being counted — and the statement carries real exponents
  `1/dᵢ`.
## §10.3 — Theorem 10.3.3 (Blakey–Roy) is proved

`ProbMethods/Chapter10/Sidorenko.lean`. `PMC.sidorenko_path3`: for every graph `G` on `n`
vertices with `m` edges, `hom(P₄, G) · n² ≥ (2m)³`, i.e. `t(P₄, G) ≥ t(K₂, G)³`
(`PMC.sidorenko_path3_density`) — Sidorenko's conjecture for the three-edge path.

**The notes' entropy proof is carried out with no conditional-entropy machinery at all.**
Writing the walk distribution's entropy out explicitly, the argument reduces to exactly two
applications of **Gibbs' inequality** (`PMC.sum_mul_log_div_le`, already in §10.1):

* `PMC.sum_log_div_card_le_log_sum_div_card` — Jensen for `log`, i.e. AM–GM, from Gibbs
  against the uniform distribution on the directed edges. This converts
  `hom(P₄, G) = ∑_{(y,z)} d(y)d(z)` (`PMC.card_walk3`, fibred over the middle edge) into
  `∑_v d(v) log d(v)`.
* `PMC.sum_degree_mul_log_degree_ge` — `∑_v d(v) log d(v) ≥ 2m log(2m/n)`, from Gibbs against
  the uniform distribution on vertices with `P(v) = d(v)/2m`. This is the notes'
  `H(X) ≤ log n` step in counting form.

That both steps are the *same lemma* is the thing worth recording. Gibbs' inequality **is**
the entropy inequality, so a proof that uses only Gibbs is the entropy proof — just written
out, without needing conditional independence, `H(Z|X,Y) = H(Z|Y)`, or a four-variable chain
rule. Had the argument gone through conditional entropies it would have needed a
conditional-independence lemma the library does not have.

**Checked on `K₃`, where the bound is attained**: `6` directed edges, `24` walks, and
`6³ = 216 = 24 · 3²`. Equality for regular graphs is the right behaviour — the conjecture says
the random graph is the minimiser.

### Theorem 10.3.6's case `F = K₂,₂` — proved, by Cauchy–Schwarz

`PMC.sidorenko_C4`: `hom(C₄, G) · n⁴ ≥ (2m)⁴`, i.e. `t(C₄, G) ≥ t(K₂, G)⁴`. Grouping a
`C₄`-homomorphism by its pair of *opposite* vertices gives `hom(C₄, G) = ∑_{a,c} N(a,c)²`
with `N` the codegree (`PMC.card_walk4`), and `∑ N(a,c) = ∑_v d(v)²` (`PMC.sum_codeg`), so
two applications of `sq_sum_le_card_mul_sum_sq` — over the `n²` pairs, then over the `n`
vertices — give the bound.

**This deviates from the notes deliberately.** Their entropy proof of the `K₂,₂` case needs a
conditional-independence step the library does not have, while Cauchy–Schwarz needs nothing
new. The statement is theirs; only the route differs, and the roadmap says so rather than
implying the entropy proof was formalized.

Checked on `K₃`: `hom(C₄, K₃) = 18 = tr(A⁴)`, and `6⁴ = 1296 ≤ 18 · 81`.

### Theorem 10.3.5 for stars — proved, and it locates the difficulty

`PMC.sidorenko_star`: `hom(K₁,ₜ, G) · n^{t-1} ≥ (2m)^t`. A star-homomorphism is a centre
together with `t` independent neighbours of it, so `hom(K₁,ₜ, G) = ∑_v d(v)^t`
(`PMC.card_starHom`), and the inequality is then exactly the power-mean inequality
`pow_sum_div_card_le_sum_pow`. Checked on `K₃` at `t = 2`: `36 = 12 · 3`, equality.

Stars are trees, so this is an infinite family of cases of Theorem 10.3.5 — and it is worth
recording next to the harder ones because it **locates the difficulty**: the obstacle in
Sidorenko's conjecture is not trees with a single branch vertex, where the count factorises
outright, but the ones whose entropy bookkeeping needs a genuine chain rule along the tree.

### Theorem 10.3.6 in full — proved

`PMC.sidorenko_biclique`: `hom(K_{s,t}, G) · n^{2st-s-t} ≥ (2m)^{st}` for **all** `s, t`. The
notes demonstrate `K₂,₂` and remark that the same proof extends; with the star case in hand
the extension needs no entropy at all —

    hom(K_{s,t}, G) = ∑_{a ∈ Vˢ} N(a)^t ≥ (∑_a N(a))^t / (nˢ)^{t-1}     [power mean]
    ∑_a N(a) = ∑_b d(b)ˢ ≥ (2m)ˢ / n^{s-1}                              [the star case]

and multiplying out gives the exponent. Parametrising by `s+1`, `t+1` keeps every exponent a
genuine natural number, with no truncated subtraction. **This subsumes both earlier cases**:
`s = t = 1` is `C₄` and `s = 0` is the star. Checked on `K₃`, where the `(2,2)` count is `18`,
agreeing with the closed-4-walk count as it must since `C₄ = K₂,₂`.

### The conditional-independence tool now exists

`PMC.wcondEntropy_pair_eq_of_condIndep`: if the conditional distribution of `X` given
`(Y, Z)` depends only on `Y`, then `H(X | Y, Z) = H(X | Y)`. This is the step the notes invoke
as "[cond indep]", and the one whose absence was recorded twice above as the reason for taking
Cauchy–Schwarz routes instead.

The proof is a regrouping, not an inequality: the fibres of `(Y, Z)` above a fixed `Y`-value
all carry the same conditional distribution, so their weights collapse onto the marginal of
`Y` (`PMC.sum_wdist_pair_right`).

**What this does and does not unblock.** The gap in the *library* is closed. Each application
still has to verify the hypothesis for its own distribution, and for trees that means
building the tree-indexed Markov distribution and proving its marginals are degree-biased —
which is the remaining work in Theorem 10.3.5, not the entropy identity.

What remains in §10.3: Theorem 10.3.5 in full (all trees — the same argument, but the entropy
bookkeeping is over a tree rather than a path, so it does need the conditional-independence
step), Theorem 10.3.6 (complete bipartite), and Theorem 10.3.7. Remark 10.3.8's Möbius graph
is an open case of the conjecture and is not a node.

* **§10.3** — Sidorenko's inequality, about homomorphism densities. Note Remark 10.3.8: the
  Möbius graph `K₅,₅ ∖ C₁₀` is the smallest open case, so part of the section is an open
  problem rather than something to formalize.
* **Theorem 10.4.9 — proved** (`PMC.card_lt_of_triangle_intersecting`). Every
  triangle-intersecting family of graphs on `n` labelled vertices has size
  `< 2 ^ (C(n,2) - 2)`, so §10.4 is complete.

  Two choices worth recording. The split uses `⌈n/2⌉`, not `⌊n/2⌋`, because
  `PMC.card_blocks_containing` needs blocks of size at least two and `⌈n/2⌉ ≥ 2` already at
  `n = 3`, whereas `⌊3/2⌋ = 1`; the two give the same block size `r`, so nothing is lost.
  And `PMC.HasTri` is phrased through a 3-element *vertex set* rather than three explicit
  edges, which keeps non-diagonality proofs out of the statement.

  The simplification over the notes held up: the covering multiplicity is a direct binomial
  count, and no group action on edges was ever needed. Non-vacuity was checked with a
  **nonempty** family — on 3 vertices `{all edges}` is triangle-intersecting and
  `1 < 2^(3-2) = 2` — since a mis-stated `HasTri` would have made the hypothesis
  unsatisfiable and the theorem vacuous.

## Next

Two things:



* **§10.2** — Theorem 10.2.1 (Brégman–Minc): `per A ≤ ∏ (dᵢ!)^{1/dᵢ}` for a 0–1 matrix with
  row sums `dᵢ`. **Harder than anything in §10.4**, and worth knowing why before starting:
  Radhakrishnan's proof reveals the chosen entries in a *uniform random order*, so it needs
  conditional entropy over a random permutation of the rows — a second layer of randomness
  on top of the permutation being counted — and the statement carries real exponents
  `1/dᵢ`.
* **§10.3** — Sidorenko's inequality, about homomorphism densities. Note Remark 10.3.8: the
  Möbius graph `K₅,₅ ∖ C₁₀` is the smallest open case, so part of the section is an open
  problem rather than something to formalize.
* (done — see above) in `ProbMethods/Chapter10/Intersecting.lean`
  (`PMC.two_mul_card_traceOn_le`, `PMC.exists_pair_same_side`), with Corollary 10.4.7 already
  available as `PMC.card_pow_le_prod_card_projSet`.

  **One simplification over the notes is worth taking.** The notes obtain the covering
  multiplicity `k` "by symmetry and averaging", which in Lean would mean a transitive action
  of `Sₙ` on edges. It is unnecessary: the number of `S` with `|S| = ⌊n/2⌋` that put a given
  edge `{u,v}` inside a part is
  `C(n-2, ⌊n/2⌋-2) + C(n-2, ⌊n/2⌋)` — both endpoints in `S`, or both outside — which
  visibly does not depend on which edge it is. A **direct count, no symmetry argument.**

  **All the non-arithmetic content is now proved.**
  `PMC.card_pow_le_prod_of_traces_intersecting` combines Corollary 10.4.7 with the
  intersecting bound into `#F ^ k ≤ ∏_j 2^(#A_j) / 2`, and Corollary 10.4.7 itself is now
  available in the notes' own set-family form (`PMC.card_pow_le_prod_card_image_inter`),
  bridged from the tuple form by the indicator encoding. Both were checked **tight** on the
  star family, which is a stronger check than non-vacuity: an off-by-one in the halving would
  not achieve equality.

  What remains is finite counting on the edge set. Of the six steps, two are now done:

  1. the edge type is `{e : Sym2 (Fin n) // ¬ e.IsDiag}`, whose cardinality is `C(n,2)` from
     Mathlib's `Sym2.card_subtype_not_diag` — **and it now works with the container bound**,
     since the `LinearOrder` hypothesis is gone;
  2. **done**: `PMC.card_within` gives `#(edges inside S) = C(#S,2)`, so
     `#(A_S) = C(a,2) + C(b,2)` follows by disjointness of the two blocks;
  3. **done**: `PMC.card_blocks_containing` — for a fixed edge, the number of `m`-sets
     putting both endpoints on the same side is `C(n-2,m-2) + C(n-2,m)`, a direct count with
     no symmetry argument. Note `2 ≤ m` is required and not cosmetic: at `m = 0` the
     truncated `m - 2` makes the first term `C(n-2,0) = 1` while no `0`-set contains both
     endpoints;
  4. **done**: `PMC.choose_mul_block_eq` — `C(n,m) · r = C(n,2) · k`. Both sides count the
     pairs `(S, e)` with `e` inside a part of `S`; the point is that `r` and `k` are both
     *constant*, so each side collapses to a product;
  5. **done**: `r ≤ C(n,2)/2` is `PMC.two_mul_choose_two_add_le`, resting on
     `PMC.two_mul_choose_two`;
  6. the exponent assembly — the only step left, and it is worked out:

     the container bound gives `#𝒢^k ≤ (2^r/2)^N` with `N = C(n,m)`; `rN = k·C(n,2)` is
     step (4); and `2r < C(n,2)` (`PMC.two_mul_choose_two_add_lt`, the strict form) gives
     `2k < N`, whence `(r-1)N < k(C(n,2)-2)` and the conclusion follows on taking `k`-th
     roots. Side conditions: `k ≥ 1` (true for `m ≤ n`) and `C(n,2) ≥ 2` (so `n ≥ 3`).
     `n ≤ 2` is separate and trivial — with at most one edge no intersection can contain a
     triangle, so the family is empty.

     Still to define: "`G ∩ G'` contains a triangle", and the trace-intersecting hypothesis,
     which follows from `PMC.exists_pair_same_side` — two of the triangle's three vertices
     lie on the same side of `S`, and the edge between them is in `PMC.block S`.

  On (5), the balance hypothesis is load-bearing rather than decorative: `a = 7, b = 0`
  gives `2 · 21 = 42 > 21`, so an unbalanced split breaks the bound outright. That is checked
  numerically alongside the two balanced cases.

  On (2), one trick is worth reusing. The bijection `PMC.within S ≃ PMC.Edge ↥S` needs, for
  surjectivity, a *lift* of an edge of `V` with both ends in `S` to an edge of `↥S` — awkward
  to write as a function. But surjectivity is a `Prop`, so `Sym2.ind` destructs the edge into
  an actual pair and the lift is immediate. Choosing `Finset.card_bij` (which asks for
  surjectivity) over `Finset.card_bij'` (which asks for an explicit inverse) is what makes
  that available. Relatedly, `Sym2.ind` needs any hypothesis mentioning the element — here
  the non-diagonality proof — `revert`ed first.

### The `LinearOrder` hypothesis is gone

`PMC.shearer_of_submodular` and the whole chain below it — `PMC.shearer`,
`PMC.card_pow_le_prod_card_projSet`, `PMC.card_pow_le_prod_card_image_inter`,
`PMC.card_pow_le_prod_of_traces_intersecting`, `PMC.card_projSet_pair_le` — no longer
require `[LinearOrder ι]`. The order is used only by `PMC.sum_chain_eq`'s peeling and never
appears in a conclusion, so it had no business in the interface; it was also *actively*
blocking Theorem 10.4.9, whose edge type is a subtype of `Sym2` and has no natural order.

**The fix, and the two things that do not work.** Any `Fintype` with decidable equality
carries a linear order (transport from `Fin (card ι)`), and the goal is a `Prop`, so
`Trunc.induction_on` supplies one. The subtlety is that a transported `LinearOrder` brings
its own `LinearOrder.toDecidableEq`, a *different term* from the ambient `DecidableEq ι`, so
every `Finset.filter` and `insert` in the statement stops matching — and the two goals
**print identically**, which makes this confusing to diagnose.

* Overriding the field by structure update, `{ LinearOrder.lift' e e.injective with
  toDecidableEq := … }`, does not typecheck: `LinearOrder` extends several classes.
* Converting each hypothesis with `convert … using n` leaves unsolved goals.
* **What works:** name the instance binder (`[inst : DecidableEq ι]`) and `subst` it against
  `Subsingleton.elim` — `have hDE : inst = @LinearOrder.toDecidableEq ι lo := Subsingleton.elim _ _;
  subst hDE`. That rewrites the goal *and* every hypothesis in one step, because the instance
  is a genuine local. `DecidableEq` is a subsingleton pointwise, so the elim is free.

Verified by applying the container bound to `{e : Sym2 (Fin n) // ¬ e.IsDiag}`, whose
cardinality is `C(n,2)` via Mathlib's `Sym2.card_subtype_not_diag`. That is exactly the
setting Theorem 10.4.9 needs, so its remaining work really is only arithmetic now.

## Next

Two things:



* **§10.2** — Theorem 10.2.1 (Brégman–Minc): `per A ≤ ∏ (dᵢ!)^{1/dᵢ}` for a 0–1 matrix with
  row sums `dᵢ`. **Harder than anything in §10.4**, and worth knowing why before starting:
  Radhakrishnan's proof reveals the chosen entries in a *uniform random order*, so it needs
  conditional entropy over a random permutation of the rows — a second layer of randomness
  on top of the permutation being counted — and the statement carries real exponents
  `1/dᵢ`.
* **§10.3** — Sidorenko's inequality, about homomorphism densities. Note Remark 10.3.8: the
  Möbius graph `K₅,₅ ∖ C₁₀` is the smallest open case, so part of the section is an open
  problem rather than something to formalize.
* (done — see above) in `ProbMethods/Chapter10/Intersecting.lean`
  (`PMC.two_mul_card_traceOn_le`, `PMC.exists_pair_same_side`), with Corollary 10.4.7 already
  available as `PMC.card_pow_le_prod_card_projSet`.

  **One simplification over the notes is worth taking.** The notes obtain the covering
  multiplicity `k` "by symmetry and averaging", which in Lean would mean a transitive action
  of `Sₙ` on edges. It is unnecessary: the number of `S` with `|S| = ⌊n/2⌋` that put a given
  edge `{u,v}` inside a part is
  `C(n-2, ⌊n/2⌋-2) + C(n-2, ⌊n/2⌋)` — both endpoints in `S`, or both outside — which
  visibly does not depend on which edge it is. A **direct count, no symmetry argument.**

  **All the non-arithmetic content is now proved.**
  `PMC.card_pow_le_prod_of_traces_intersecting` combines Corollary 10.4.7 with the
  intersecting bound into `#F ^ k ≤ ∏_j 2^(#A_j) / 2`, and Corollary 10.4.7 itself is now
  available in the notes' own set-family form (`PMC.card_pow_le_prod_card_image_inter`),
  bridged from the tuple form by the indicator encoding. Both were checked **tight** on the
  star family, which is a stronger check than non-vacuity: an off-by-one in the halving would
  not achieve equality.

  What remains is finite counting on the edge set. Of the six steps, two are now done:

  1. the edge type is `{e : Sym2 (Fin n) // ¬ e.IsDiag}`, whose cardinality is `C(n,2)` from
     Mathlib's `Sym2.card_subtype_not_diag` — **and it now works with the container bound**,
     since the `LinearOrder` hypothesis is gone;
  2. **done**: `PMC.card_within` gives `#(edges inside S) = C(#S,2)`, so
     `#(A_S) = C(a,2) + C(b,2)` follows by disjointness of the two blocks;
  3. **done**: `PMC.card_blocks_containing` — for a fixed edge, the number of `m`-sets
     putting both endpoints on the same side is `C(n-2,m-2) + C(n-2,m)`, a direct count with
     no symmetry argument. Note `2 ≤ m` is required and not cosmetic: at `m = 0` the
     truncated `m - 2` makes the first term `C(n-2,0) = 1` while no `0`-set contains both
     endpoints;
  4. **done**: `PMC.choose_mul_block_eq` — `C(n,m) · r = C(n,2) · k`. Both sides count the
     pairs `(S, e)` with `e` inside a part of `S`; the point is that `r` and `k` are both
     *constant*, so each side collapses to a product;
  5. **done**: `r ≤ C(n,2)/2` is `PMC.two_mul_choose_two_add_le`, resting on
     `PMC.two_mul_choose_two`;
  6. the exponent assembly — the only step left, and it is worked out:

     the container bound gives `#𝒢^k ≤ (2^r/2)^N` with `N = C(n,m)`; `rN = k·C(n,2)` is
     step (4); and `2r < C(n,2)` (`PMC.two_mul_choose_two_add_lt`, the strict form) gives
     `2k < N`, whence `(r-1)N < k(C(n,2)-2)` and the conclusion follows on taking `k`-th
     roots. Side conditions: `k ≥ 1` (true for `m ≤ n`) and `C(n,2) ≥ 2` (so `n ≥ 3`).
     `n ≤ 2` is separate and trivial — with at most one edge no intersection can contain a
     triangle, so the family is empty.

     Still to define: "`G ∩ G'` contains a triangle", and the trace-intersecting hypothesis,
     which follows from `PMC.exists_pair_same_side` — two of the triangle's three vertices
     lie on the same side of `S`, and the edge between them is in `PMC.block S`.

  On (5), the balance hypothesis is load-bearing rather than decorative: `a = 7, b = 0`
  gives `2 · 21 = 42 > 21`, so an unbalanced split breaks the bound outright. That is checked
  numerically alongside the two balanced cases.

  On (2), one trick is worth reusing. The bijection `PMC.within S ≃ PMC.Edge ↥S` needs, for
  surjectivity, a *lift* of an edge of `V` with both ends in `S` to an edge of `↥S` — awkward
  to write as a function. But surjectivity is a `Prop`, so `Sym2.ind` destructs the edge into
  an actual pair and the lift is immediate. Choosing `Finset.card_bij` (which asks for
  surjectivity) over `Finset.card_bij'` (which asks for an explicit inverse) is what makes
  that available. Relatedly, `Sym2.ind` needs any hypothesis mentioning the element — here
  the non-diagonality proof — `revert`ed first.

### The one real obstacle, and it is not mathematical

**`PMC.shearer_of_submodular` and everything downstream carry `[LinearOrder ι]`, and the
natural edge type has no linear order.** The chain decomposition `PMC.sum_chain_eq` needs an
order to peel the largest element, but *no conclusion in the chain mentions one* — it is an
artifact of the proof sitting in the interface. The candidate edge types
(`{e : Sym2 (Fin n) // ¬ e.IsDiag}`, which is where `Sym2.card_subtype_not_diag` gives
`C(n,2)` for free, or `{e : Finset (Fin n) // #e = 2}`) are subtypes of types Mathlib does
not linearly order.

The obvious fix — derive an order inside the proof, since any `Fintype` with decidable
equality carries one via `Fintype.truncEquivFin` and `LinearOrder.lift'`, and the goal is a
`Prop` so `Trunc.induction_on` supplies it — **was attempted and does not work naively.** A
transported `LinearOrder` brings its own `LinearOrder.toDecidableEq`, which is a different
term from the ambient `DecidableEq ι`, so every `Finset.filter` and `insert` in the
statement stops matching and the application fails with two goals that print identically.
Overriding the field via structure update (`{ LinearOrder.lift' … with toDecidableEq := … }`)
does not typecheck either, because `LinearOrder` extends several classes.

Two routes that should work, in order of preference:

1. **Bridge the instances explicitly.** `DecidableEq ι` is a subsingleton (pointwise
   `Subsingleton (Decidable p)` plus `funext`), so `Subsingleton.elim` gives the equality of
   the two instances; convert the hypotheses with it — `Finset.filter_congr_decidable`
   handles the `filter` occurrences and `congr` the `insert` ones.
2. **Give the edge type an order and keep the interface as is.** Index edges by
   `Fin (C(n,2))` and carry an explicit bijection to the 2-element vertex subsets, so the
   order is `Fin`'s and all the counting happens on the subset side.

Route 1 is worth doing regardless of 10.4.9: it removes a hypothesis no application should
have to satisfy.

## §10.4 — Lemma 10.4.13, the bipartite swapping trick

`ProbMethods/Chapter10/Swapping.lean`. `PMC.card_indepSets_sq_le_card_indepCover`:
`i(G)² ≤ i(G × K₂)`, unconditionally.

This is what reduces Kahn–Zhao (Theorem 10.4.12) from all `d`-regular graphs to the bipartite
ones, and **unlike the rest of §10.4 it is not an entropy argument** — the notes give an
explicit injection, and this formalises it:

* `i(2G) = i(G)²`, so it suffices to inject `I(2G) → I(G × K₂)`.
* `PMC.crossing_slice` — the bad edges are *bipartite*, witnessed by the copy-`0` slice, so a
  crossing set exists at all.
* `PMC.swapSet_mem_indepCover` — swapping along a crossing set repairs every bad edge. Four
  cases: two put two vertices of `S` in the *same* copy, contradicting independence in `2G`;
  the other two give a bad edge with both endpoints on one side of `A`, contradicting
  crossing.
* `PMC.sameEdge_swapSet` and `PMC.crossing_iff_crossingT` — **the image remembers the bad
  edges**, hence the whole crossing family, hence the canonical choice made from it.

The design point worth recording: the canonical crossing set is `PMC.pickMin`, **a function of
the crossing family alone** (least index under a fixed indexing of the subsets of `V`). The
notes say "fix an arbitrary order on all subsets"; what the injectivity argument actually
needs is that the choice depend on nothing but the family, since that family is what the image
reveals.

Both products are given as *relations* on `V × Bool` rather than `SimpleGraph` structures:
independence only ever needs the relation, so there are no `symm` or `loopless` obligations.

Checked: equality at `K₂` (`9 = 3²`, the cover being two disjoint edges — not a 4-cycle) and
strict at `K₃` (`16 ≤ 18`, the cover being a 6-cycle).

## §10.4 — Theorem 10.4.12, Kahn–Zhao

`ProbMethods/Chapter10/KahnZhao.lean`. `PMC.card_indepSets_pow_le`: for every `n`-vertex
`d`-regular graph,

    i(G)^(2d) ≤ (2^(d+1) - 1)^n.

The notes state it as `i(G) ≤ i(K_{d,d})^{n/(2d)}`; the fractional exponent is an artifact of
taking logarithms, and cleared of it the theorem is a statement about natural numbers, which
is how it is stated here. Nothing is lost — the two are equivalent by monotonicity of `log`,
and the `ℕ` form is what a later application would want to chain with.

**Bipartite case** (`PMC.card_indepR_pow_le_of_bipartite`), Kahn's entropy argument, with
`X` the indicator tuple of a uniformly random independent set:

* `d·H(X) = d·H(X_A) + d·H(X_B | X_A)` — chain rule, in the block form
  `PMC.tupleEntropy_union_le`, which also gives `H(X_B|X_A) ≤ ∑_{b ∈ B} H(X_b|X_A)`.
* `d·H(X_A) ≤ ∑_{b ∈ B} H(X_{N(b)})` — Shearer. The covering multiplicity *is* regularity:
  a vertex `a ∈ A` lies in `N(b)` for exactly its `d` neighbours `b`. This needed a new form
  of the lemma, `PMC.shearer_subset`, because the vertices of `B` lie in none of the `N(b)`
  and so are covered zero times.
* `H(X_b|X_A) ≤ H(X_b|X_{N(b)})` — `PMC.wcondEntropy_masked_antitone`.
* one inequality per `b ∈ B`: `H(X_{N(b)}) + d·H(X_b|X_{N(b)}) ≤ log (2^{d+1} - 1)`.

**The per-vertex step is where this proof departs from the notes.** The notes introduce `d`
conditionally independent copies of `X_b` given `X_{N(b)}` and read the left side as
`H(X_b^{(1)}, …, X_b^{(d)}, X_{N(b)})`, bounded by `log i(K_{d,d})` because that tuple *is*
an independent set of `K_{d,d}`. The route taken here bounds the same quantity by an entropy
maximisation:

* `X_b` is determined unless `X_{N(b)}` is all-`false`, so `H(X_b|X_{N(b)}) ≤ P(0)·log 2`
  (`PMC.wcondEntropy_indepInd_le`);
* `H(X_{N(b)}) + d·log 2·P(0) ≤ log (2^d + (2^d - 1))` by the Gibbs variational principle
  `PMC.wentropy_add_wmean_le_log_sum_exp`, at the energy giving the all-`false` mask weight
  `2^d` and each of the other `2^d - 1` masks weight `1`.

The maximum is `2^{d+1} - 1 = i(K_{d,d})`, as it has to be: the extremal distribution of a
Gibbs bound is the Gibbs measure, which here is the uniform independent set of `K_{d,d}`. The
constant arrives with a reason attached rather than by exhibiting the extremal graph.

`PMC.condProd` (`Chapter10/CondCopies.lean`) builds the copies construction anyway — it is
what the notes' own §10.3 proofs use, and it is the right object to have — but Kahn–Zhao does
not need it.

**General case**: the double cover is bipartite and `d`-regular
(`PMC.card_nbrs_coverAdj`), Kahn's case applies to it, and the swapping trick transfers the
bound back: `i(G)^{2d} = (i(G)²)^d ≤ i(G × K₂)^d ≤ (2^{d+1}-1)^n`.

Checked by brute force over every regular graph on at most 6 vertices: no violations, and the
equality cases are exactly the disjoint unions of `K_{d,d}` (`n=2,d=1`; `n=4,d=1`;
`n=4,d=2` — that is `C₄ = K_{2,2}`, `i = 7`; `n=6,d=1`; `n=6,d=3` — `K_{3,3}`, `i = 15`),
which is what the theorem predicts.

## §10.4 — Theorem 10.4.14, Galvin–Tetali

`ProbMethods/Chapter10/GalvinTetali.lean`. `PMC.card_homSetR_pow_le`: for a `d`-regular
bipartite `G` and **any** target `H`, loops allowed,

    hom(G, H)^d ≤ hom(K_{d,d}, H)^{#B}.

The notes state this and say only that "the entropy proof of the bipartite case of Theorem
10.4.12 extends". It does, and the extension cost almost nothing here because the global part
of Kahn's proof was first separated out as `PMC.mul_tupleEntropy_univ_le` — Shearer on the
side `A`, chain rule and block subadditivity on the side `B`, with a per-vertex bound as a
hypothesis. Galvin–Tetali is that skeleton with a different per-vertex bound, and nothing
else changes.

**The per-vertex bound, and where the constant comes from.** The notes take `d`
conditionally independent copies of `X_b` given `X_{N(b)}` and observe the resulting tuple is
a homomorphism of `K_{d,d}`. Here it is the Gibbs variational principle again, and this time
the target constant is not put in by hand but *computed*:

* `X_b` must lie in the common neighbourhood of the values on `N(b)`, so
  `H(X_b | X_{N(b)}) ≤ E[log #commonNbhd(X_{N(b)})]`;
* `PMC.wentropy_add_wmean_le_log_sum_exp` at the energy `a ↦ d·log #commonNbhd(a)` bounds the
  whole left side by `log ∑_a #commonNbhd(a)^d`;
* and `∑_a #commonNbhd(a)^d` **is** `hom(K_{d,d}, H)` (`PMC.card_kddHom`): a homomorphism of
  `K_{d,d}` is a tuple on one side plus `d` independent choices from its common
  neighbourhood.

So the extremal graph appears as the partition function of the maximisation rather than as an
example to be checked. This is the same phenomenon as `2^{d+1} - 1 = i(K_{d,d})` in Kahn's
case, which is now visibly the instance `H = ` one edge with a loop.

**Two things worth recording about the formalization.**

*The degenerate tuples must be excluded from the partition function.* `Real.log 0 = 0` makes
`exp (d log #commonNbhd a) = 1` where `#commonNbhd a ^ d = 0`, so summing the energy over
*all* tuples would inflate the partition function above `hom(K_{d,d},H)` and break the
inequality. Restricting to the tuples with nonempty common neighbourhood is free, since an
attained tuple always has `X_b` in its common neighbourhood — but it is not optional.

*The conditioning variable is re-presented, not re-derived.* The per-vertex bound wants
`X_{N(b)}` as a function `Fin d → V(H)` (so that the partition function is a sum over tuples),
while the skeleton produces it as a mask `V → Option V(H)`. `PMC.wcondEntropy_congr_left` —
new, and the conditional analogue of `PMC.wentropy_congr` — says conditional entropy depends
only on the fibres of the conditioning variable, which lets an enumeration of `N(b)` move
between the two presentations with no probability recomputed.

**Checked**: brute force over every symmetric relation with loops on up to 3 vertices as the
target, against `2K₂`, `C₄`, `C₆`, `K₂,₂` and `K₃,₃` as the host: no violations, equality at
`K_{d,d}` itself. And the specialisation is checked *in Lean*: `PMC.card_homSetR_indepTarget`
and `PMC.card_kddHom_indepTarget` turn Theorem 10.4.14 at the independent-set target back into
the statement of `PMC.card_indepR_pow_le_of_bipartite`, which the file records as a
kernel-checked `example`. `PMC.card_properColorings_pow_le` is the other special case the
notes name, `c_q(G)^d ≤ c_q(K_{d,d})^{#B}`.

**What remains in §10.4**: Theorem 10.4.15 (Sah–Sawhney–Stoner–Zhao 2020), which removes the
bipartite hypothesis for `H = K_q`. The notes state it without proof — it is a research paper,
not an argument in the book — so it is not a node here.
