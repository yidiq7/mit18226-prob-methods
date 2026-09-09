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

## Theorem 5.0.5 — proved, upstream

**Theorem 5.0.5 — the deferral was wrong, and the correction is the lesson.** It was recorded
here as unreachable: it quantifies over *arbitrary* independent variables in `[-1,1]`, so the
sample space is a product of continua and the counting framework does not reach it — "the first
place where the finite approach genuinely runs out".

Half of that was right. The finite framework indeed does not reach it; **Mathlib does**, and
`PMC.measure_sum_ge_sqrt_le_of_mem_Icc` (`Chapter05/ChernoffGeneral.lean`) is a forty-line
derivation from two upstream lemmas:

* `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` — mean zero in an
  interval of length `2` is sub-Gaussian with parameter `1`;
* `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` —
  `P(∑ Xᵢ ≥ ε) ≤ exp(-ε²/(2∑cᵢ))`.

At `cᵢ = 1` that is `exp(-ε²/(2n))`, and `ε = λ√n` gives the notes' `e^{-λ²/2}` with no slack.
The theorem is stated over an arbitrary probability space, exactly as the notes state it — no
finite weight, no `PMC.wmean`.

**The lesson**, which cost this entry a wrong deferral: FKG (Chapter 7) and Weierstrass
(Chapter 4) were recorded as upstream because a survey found them. This one was recorded as
*blocked* on a structural argument about sample spaces that sounded convincing and was never
checked against Mathlib. A structural reason to give up is exactly the kind that needs
checking.

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

## Nearly equiangular vectors (§5.2, Theorem 5.2.1) — proved

`PMC.exists_nearly_equiangular`: for `a ∈ (0,1)` and `ε > 0` there is `c > 0` such that for
all large `N`, `ℝ^N` holds at least `2^{cN}` unit vectors with all pairwise inner products in
`[a - ε, a + ε]`.

**The statement needed correcting.** The notes say "for every `n`", and that is false for
small `n`: the only unit vectors in `ℝ¹` are `±1`, whose inner products are `±1`, so at
`a = 1/2, ε = 1/100` every admissible family has a single element while `2^{c·1} > 1`. The
conclusion holds for `N ≥ N₀(a, ε)`, which is what the proof gives and what the notes mean.

Two design choices, both of which shrank the proof a lot:

* **The bias goes into one coordinate.** The notes sample `v ∈ {-1,1}ⁿ` with `P(+1) = (1+√a)/2`
  so that `E[vᵢ · vⱼ] = a`, and then the pairwise products `σᵢ(k)σⱼ(k)` are the independent
  `±1` variables the Chernoff bound is applied to. Formalizing that needs the law of a *pair*
  of rows, i.e. a marginal computation on the `m × n` grid of coins. Instead `PMC.eqVec`
  puts the bias in a single constant coordinate, `v(x) = (√a, ±√((1-a)/n))`, leaving the
  other `n` coordinates *unbiased*. Then

      ⟨v(x), v(y)⟩ = a + (1 - a)(1 - 2#(x ∆ y)/n)

  is an exact algebraic identity (`PMC.sum_eqVec_mul`), `‖v(x)‖ = 1` is `a + (1-a) = 1`
  (`PMC.sum_eqVec_sq`), and the whole probabilistic content is the *balanced* two-sided
  bound `PMC.card_filter_card_dev_le`. One coordinate of the `n+1` is the price.
* **Caro–Wei replaces the union bound.** What remains is a large family of subsets with all
  pairwise Hamming distances near `n/2` — an independent set in `PMC.farGraph`. The notes get
  it from a union bound over the `m²` pairs of a random `m`-tuple; `PMC.exists_far_family`
  instead observes that **every degree of that graph is bounded by the same tail count**,
  because `y ↦ x ∆ y` injects the neighbours of `x` into the deviating subsets. Caro–Wei
  (§2.3, `PMC.exists_isIndepSet_caro_wei`) then hands over an independent set of size
  `2ⁿ/(D+1)`, and with `D ≤ 2 · 2ⁿ e^{-2δ²n}` that is `≥ e^{2δ²n}/3 ≥ e^{δ²n}`. No product
  space, no marginal, and the input is a result of the book's own Chapter 2.

`δ ≤ 1/2` is imposed (harmlessly — shrinking `δ` only strengthens the conclusion) so that
`2δ² ≤ 1/2 ≤ log 2` and hence `2ⁿ e^{-2δ²n} ≥ 1`, which is what lets the `+1` in the
denominator be absorbed. `Real.log_two_gt_d9` supplies the `log 2 ≥ 1/2`.

Checked numerically before trusting it: the inner-product identity and the unit norms to
machine precision on random pairs, and `D ≤ 2·2ⁿe^{-2t²/n}` together with
`2ⁿ/(D+1) ≥ e^{δ²n}` at five `(n, δ)` settings with `D` computed exactly from binomial
coefficients.

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
