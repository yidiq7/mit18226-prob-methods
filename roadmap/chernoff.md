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

**Theorem 5.0.5 is deferred, and for a reason worth recording.** It quantifies over
*arbitrary* independent variables taking values in `[-1, 1]`, so the sample space is a
product of continua and is **not finite** — the counting framework does not reach it at all,
unlike everything else in Chapters 1–5. Formalizing it means either `MeasureTheory` or
restating it for finitely-supported variables. This is the first place where the finite
approach genuinely runs out, as opposed to merely needing more work.

## Corollary 5.0.6 — proved

`ProbMethods/Chapter05/HoeffdingBernoulli.lean`. For a sum of independent Bernoullis with mean
`μ`, both tails:

    P(X ≥ μ + t) ≤ exp(-2t²/n),   P(X ≤ μ - t) ≤ exp(-2t²/n),

and the notes' form `P(X ≥ μ + λ√n) ≤ e^{-λ²/2}` as the instance `t = λ√n` (the sharp bound
gives `e^{-2λ²}`).

The engine is **Hoeffding's lemma at a single Bernoulli**, `PMC.bernoulli_mgf_le`:
`p e^λ + (1-p) ≤ exp(λp + λ²/8)`, which is `PMC.wmean_exp_le_of_mem_Icc` — task #47, now proved
through the measure bridge — on the two-point space. Multiplying over coordinates uses
`PMC.sum_pweight_mul_exp`, the *exact* moment generating function already proved for Theorem
5.0.7, so the argument is: exact MGF, coordinatewise Hoeffding, Markov, optimise `λ = 4t/n`.

The lower tail is complementation rather than a second argument: `#S ≤ μ - t` says the
complement sits `t` above *its* mean `n - μ`, and `PMC.pweight_compl` (`pweight (1-p) Sᶜ =
pweight p S`) carries the weight across.

This is the first result in Chapter 5 that needed the measure bridge, and it is worth noting
what the bridge bought: 5.0.6 was previously listed as blocked on task #47.

## Theorem 5.0.7 (Bernoulli, differing probabilities) — proved

`PMC.sum_pweight_upper_tail`, in `ProbMethods/Chapter05/ChernoffBernoulli.lean`. With
`μ = ∑ p i`,

    ∑ over {S : #S ≥ (1+ε) μ} of pweight p S  ≤  exp (-μ ((1+ε) log(1+ε) - ε)).

The sample space is finite — subsets weighted by `∏ p i` inside and `∏ (1 - p i)` outside —
so nothing beyond `PMC.pweight` was needed. Two things worth recording:

* **`Finset.prod_add` never needed the factors to be equal.** `PMC.sum_pweight_mul_exp`
  gives the moment generating function `∏ i, (p i · e^t + (1 - p i))` in one rewrite, and
  differing probabilities cost nothing over the uniform case. This is the payoff for having
  defined `pweight` as a product rather than specialising to a constant `p`.
* **The optimisation is exact, not an estimate.** `t = log(1 + ε)` is the true minimiser, so
  the exponent `(1+ε) log(1+ε) - ε` comes out with no slack — which is why it looks odd but
  should not be "simplified". The coordinatewise step is `1 + x ≤ exp x`
  (`Real.add_one_le_exp`) applied to `x = p i (e^t - 1)`.

Checked numerically at seven parameter settings before trusting the statement, including
the degenerate `p ≡ 0` case where both sides are exactly `1` — a tight boundary case is a
stronger check on the exponent than a slack one.

**Theorem 5.0.5 remains deferred** for the reason above: it needs measure theory.

## Discrepancy (§5.1, Theorem 5.1.1) — proved

`PMC.exists_low_discrepancy`: for any family `F` of `m ≥ 3` subsets of an `n`-element ground
set there is a `±1` colouring under which every edge's sum is at most `2 √(n log m)` in
absolute value.

**Stated with the constant `2`, not `O(√(n log m))`** — that is what the notes' own proof
yields, and this project does not publish asymptotic statements.

The assembly, all three ingredients now in place:

* the two-sided Chernoff bound on each edge at `λ = 2 √(log m)`, for which
  `exp(-λ²/2) = m⁻²` exactly;
* `PMC.card_filter_inter` to lift from that edge's coordinates to the whole colouring
  space, contributing the factor `2 ^ #(V \ A)`;
* `Finset.card_biUnion_le` for the union bound over the `m` edges, giving at most
  `2 · 2ⁿ / m < 2ⁿ` bad colourings, so some colouring survives.

Two details worth recording. The per-edge threshold `λ √#A` is *dominated* by the uniform
threshold `2 √(n log m)` since `#A ≤ n`, so the bound applies to the larger threshold
without loss. And the empty edge needs separate treatment: its sum is `0`, which is below
the threshold, so no colouring is bad for it — the Chernoff bound itself requires `0 < #A`.

**`3 ≤ #F` is needed, and the notes gloss it.** The union bound gives failure at most
`2/m`; the notes conclude "with probability greater than `1 - 2/m ≥ 0`", but `≥ 0` does not
produce a colouring — it needs `> 0`, i.e. `m > 2`.

## Still to state

**§5.2 nearly equiangular vectors, §5.3 Hajós counterexample** need linear algebra over
`ℝ^n` and a graph construction respectively. Theorem 5.1.3 (Spencer's "six standard
deviations suffice") is a semirandom iterative argument and is much harder than 5.1.1;
Conjecture 5.1.5 (Komlós) is open and not a node.
