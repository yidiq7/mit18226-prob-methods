# Chapter 10 — Entropy

Zhao, *Probabilistic Methods in Combinatorics*, Chapter 10.

**Section numbering, read off the notes' own table of contents** (an earlier version of this
file had it wrong, which is worth flagging because the mistake was silent):

| § | Title | Status |
|---|---|---|
| 10.1 | Basic properties | proved |
| 10.2 | Permanent, perfect matchings, Steiner triple systems | not started |
| 10.3 | Sidorenko's inequality | not started |
| 10.4 | Shearer's lemma | Thm 10.4.1, 10.4.3, 10.4.5, Cor 10.4.7 proved; Thm 10.4.9 open |

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
| **`PMC.loomis_whitney`** | proved |
| **`PMC.card_orderedTriangles_sq_le`** — the triangle bound | proved |
| Further applications (Bregman, Kahn) | open |

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

Three things, in the notes' own order:

* **§10.2** — permanents, perfect matchings, Steiner triple systems (the Bregman-type
  results). These should go through `PMC.shearer_of_submodular` directly rather than the
  counting corollary, since the set function they need is not `S ↦ H(X_S)` for a masked
  tuple.
* **§10.3** — Sidorenko's inequality.
* **Theorem 10.4.9** — every triangle-intersecting family of graphs on `n` labelled vertices
  has size `< 2^(C(n,2) - 2)`. This is the one remaining result in the section the library
  already has the tools for, so it is the cheapest of the three.
