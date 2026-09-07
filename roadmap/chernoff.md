# Chapter 5 — Chernoff Bound

## The Chernoff bound (§5.0) — proved

### chernoff
`PMC.card_filter_sign_sum_le` — Theorem 5.0.1.

A sum of `n` independent uniform `±1` variables is realised as a subset `S ⊆ Fin n` under
the uniform weight, the sum being `2 * #S - n`. The statement counts subsets:

    #{S : lam * sqrt n ≤ 2 * #S - n}  ≤  2 ^ n * exp (-lam ^ 2 / 2)

Dividing by `2 ^ n` gives the notes' `P(Sₙ ≥ λ√n) ≤ exp(-λ²/2)`. Stating it as a count
keeps the whole result inside `Finset` arithmetic — no measure, and no need to introduce a
probability space.

**`0 < n` is required, and the notes leave it implicit.** At `n = 0` the sum is `0` and the
threshold `λ * √0` is also `0`, so *every* subset qualifies: the left side is `1` and the
right is `exp(-λ²/2) < 1`. Checked numerically before formalizing — `n = 0` is the only
failure, and the bound holds at every `n ≥ 1` and `λ` tested.

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
`#{S : λ√n ≤ |2 #S - n|} ≤ 2 * (2 ^ n * exp (-λ²/2))`.

The lower tail *is* the upper tail of the complement: `S ↦ Sᶜ` sends `2 #S - n` to its
negation, so `Finset.card_nbij'` with complement in both directions (it is an involution)
gives the two tails exactly equal cardinality, and one application of the one-sided bound
finishes it. No second MGF computation.

## Still to state

**Theorem 5.0.5 / Corollary 5.0.6 / Theorem 5.0.7** generalise to bounded and to Bernoulli
summands. 5.0.5 needs the convexity step `exp(tx) ≤ ((1-x)/2) exp(-t) + ((1+x)/2) exp t`
for `x ∈ [-1,1]`; the rest of the argument is unchanged. 5.0.7's asymmetric bounds need
`(1+ε) log(1+ε) - ε`, which is the same MGF method with a different optimisation.

**§5.1 Discrepancy, §5.2 nearly equiangular vectors, §5.3 Hajós counterexample** are
applications. §5.1 is the most tractable: colour a hypergraph's vertices `±1` and bound the
discrepancy by applying the Chernoff bound to each edge and a union bound — both of which
now exist. §5.2 and §5.3 need linear algebra over `ℝ^n` and a graph construction
respectively.
