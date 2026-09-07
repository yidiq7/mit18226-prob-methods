# Chapter 5 — Chernoff Bound

## The Chernoff bound (§5.0) — proved

### chernoff
`PMC.card_filter_sign_sum_le` — Theorem 5.0.1.

A sum of independent uniform `±1` variables indexed by a finite set `A` is realised as a
subset `T ⊆ A` under the uniform weight, the sum being `2 * #T - #A`. The statement counts
subsets:

    #{T ⊆ A : lam * sqrt #A ≤ 2 * #T - #A}  ≤  2 ^ #A * exp (-lam ^ 2 / 2)

Dividing by `2 ^ #A` gives the notes' `P(Sₙ ≥ λ√n) ≤ exp(-λ²/2)`. Stating it as a count
keeps the whole result inside `Finset` arithmetic — no measure, and no probability space.

**It is stated over an arbitrary `Finset A`, not over `Fin n`**, which matters: §5.1 needs
the sum over a *single edge* of a hypergraph, not over the whole ground set, and the `Fin n`
form does not give that. Generalising costs nothing — the proof only ever used
`card_univ = n`.

**`0 < #A` is required, and the notes leave it implicit.** At `#A = 0` the sum is `0` and
the threshold is also `0`, so *every* subset qualifies: the left side is `1` and the right
is `exp(-λ²/2) < 1`. Checked numerically before formalizing — `n = 0` is the only failure,
and the bound holds at every `n ≥ 1` and `λ` tested.

**The proof.** The moment generating function argument, exactly as the notes give it:

* `∑ over S ⊆ univ of x ^ #S = (x + 1) ^ n` from `Finset.prod_add` with both factors
  constant — the same lemma that gives the Bernoulli weights their normalisation;
* hence `∑ S, exp (t * (2 #S - n)) = (exp (-t) + exp t) ^ n = (2 cosh t) ^ n`;
* `Real.cosh_le_exp_half_sq` is **in Mathlib**, which is what makes this section cheap —
  it is the one genuinely analytic ingredient;
* `t = λ / √n` makes the threshold contribute `exp (λ²)` and the bound `exp (λ²/2)`, so the
  ratio is `exp (-λ²/2)`. The optimisation is exact, not an estimate.

Markov's inequality is inlined (each qualifying subset contributes at least
`exp (λ²)`); `PMC.wmarkov` in `Weighted.lean` is the reusable weighted form for later use.

## Two-sided (Corollary 5.0.3) — proved

`PMC.card_filter_abs_sign_sum_le`:
`#{T ⊆ A : λ√#A ≤ |2 #T - #A|} ≤ 2 * (2 ^ #A * exp (-λ²/2))`.

The lower tail *is* the upper tail of the complement, taken **within `A`**: `T ↦ A \ T`
sends `2 #T - #A` to its negation, and it is an involution on `A.powerset`, so
`Finset.card_nbij'` gives the two tails exactly equal cardinality and one application of
the one-sided bound finishes it. No second MGF computation.

## Still to state

**Theorem 5.0.5 / Corollary 5.0.6 / Theorem 5.0.7** generalise to bounded and to Bernoulli
summands. 5.0.5 needs the convexity step `exp(tx) ≤ ((1-x)/2) exp(-t) + ((1+x)/2) exp t`
for `x ∈ [-1,1]`; the rest of the argument is unchanged. 5.0.7's asymmetric bounds need
`(1+ε) log(1+ε) - ε`, which is the same MGF method with a different optimisation.

**§5.1 Discrepancy (Theorem 5.1.1).** All ingredients now exist. The lifting step is
`PMC.card_filter_inter` (`Weighted.lean`): counting subsets of `V` by a property of
`S ∩ A` factors as `2 ^ #(V \ A)` times the count over `A.powerset`, proved by the
bijection `S ↦ S \ A` on each fibre of `S ↦ S ∩ A`. The recipe: apply the two-sided bound
to each edge `A ∈ F` with
`λ = 2 sqrt (log m)`, giving at most `2 ^ #A * exp (-2 log m) = 2 ^ #A / m ^ 2` bad
colourings *per edge* on that edge's coordinates, lift to the whole ground set by the
bijection `S ↦ (S ∩ A, S \ A)` (a factor `2 ^ (n - #A)`), and union bound over the `m`
edges to get `2 ^ n * 2 / m < 2 ^ n` bad colourings when `m ≥ 3`. So some colouring works,
with the explicit bound `2 sqrt (n log m)` rather than `O(sqrt (n log m))`.

**`m ≥ 3` is needed**, and the notes gloss it: the union bound gives failure `≤ 2/m`, which
must be `< 1`. The notes write "with probability greater than `1 - 2/m ≥ 0`", but `≥ 0` is
not enough to conclude a colouring exists — it needs `> 0`, i.e. `m > 2`.

**§5.2 nearly equiangular vectors, §5.3 Hajós counterexample** need linear algebra over
`ℝ^n` and a graph construction respectively. Theorem 5.1.3 (Spencer's "six standard
deviations suffice") is a semirandom iterative argument and is much harder than 5.1.1;
Conjecture 5.1.5 (Komlós) is open and not a node.
