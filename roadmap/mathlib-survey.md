# Mathlib survey for the remaining chapters

Done 2026-09-07, after Chapter 7's main theorem turned out to be upstream and I had begun
planning a proof of it. The lesson from that near-miss was to survey before planning, so
this is that survey. It **corrects one earlier misclassification** and reclassifies
Chapter 9.

## Correction: Theorem 5.0.5 is upstream, not unreachable

`chernoff.md` recorded Theorem 5.0.5 (Chernoff for arbitrary `[-1,1]`-valued variables) as
deferred because "the sample space is a product of continua and is not finite — the counting
framework does not reach it".

The first half is true and the conclusion drawn from it was wrong. **Mathlib has this
result**, in `Mathlib/Probability/Moments/SubGaussian.lean`:

* `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` — **Hoeffding's lemma**: a mean-zero
  variable valued in `[a, b]` has a sub-Gaussian MGF. This is precisely the convexity step
  5.0.5 needs.
* `measure_sum_ge_le_of_iIndepFun` — **Hoeffding's inequality**: the tail bound for a sum of
  independent sub-Gaussian variables, which is 5.0.5 itself.

So 5.0.5 is `upstream`, in `MeasureTheory` form. What is true is that *this project's* finite
framework cannot state it; that is a statement about the framework, not about the
availability of the mathematics. Recorded as upstream in `graph.json`.

## Chapter 9 (Concentration of Measure) — substantially upstream

* **§9.1 is now proved here in finite form.** `ProbMethods/Chapter09/BoundedDifferences.lean`:
  `PMC.card_filter_ge_le` is Theorem 9.1.1,
  `#{x : f x ≥ E f + t} ≤ |β|ᴺ exp(-2t²/∑cᵢ²)`, with Hoeffding's lemma (task #47) as an
  explicit hypothesis, so it is `sorry`-free and axiom-clean.

  **The martingale is concrete, and that is the point.** `PMC.avgLast` averages out the last
  coordinate; the induction is on the number of coordinates, split by `Fin.snoc`. There is no
  filtration, no conditional expectation operator and no `MeasureTheory` — which is why §9.1,
  unlike the rest of Chapter 9, fits this project's finite convention. The two facts that make
  the recursion work are `PMC.BddDiff.avgLast` (averaging preserves the constants) and
  `PMC.exists_bounds_last` (the increment is centred with spread at most `c (last N)`).

  `PMC.hoeffdingUnif_of_hoeffding` records the exact instantiation of task #47 that discharges
  the hypothesis, so §9.1 closes automatically once that task lands.

  Both tails are proved (`PMC.card_filter_le_le` by applying the upper tail to `-f`), and
  `PMC.card_filter_ge_le_one` is Theorem 9.1.1 as the notes write it — all constants `1`,
  bound `exp(-2t²/N)`. The general-constants form is their Theorem 9.1.3, which is what was
  proved first here; specialising is the cheaper direction.

  **Example 9.1.2 (coupon collector) is proved too** (`PMC.card_filter_missing_le`), with the
  mean computed *exactly*: `E Z = n(1 - 1/n)ⁿ` (`PMC.pAvg_missing`), since each type is missed
  by `(n-1)ⁿ` of the `nⁿ` draws. The sample space `Fin n → Fin n` is exactly the shape the
  bounded-differences development uses, so the application needed no bridging.

* **§9.3's Theorem 9.3.1 (Shamir–Spencer) is proved** — `PMC.card_filter_chromF_le` in
  `Chapter09/ChromaticConcentration.lean`: `P(|χ - E χ| ≥ λ√(n-1)) ≤ 2e^{-2λ²}`. **The
  statement is finite**, with no `o(1)`, and it is §9.1's flagship application: concentration
  around the mean without knowing where the mean is.

  Two details worth recording. The graph-theoretic input is that changing the edges at one
  vertex changes the chromatic number by at most one (`PMC.chromNat_le_succ_of_agree_off`) —
  recolour that vertex afresh. And the notes' window is `√(n-1)`, not `√n`, because the
  vertex-exposure coordinate at the *first* vertex controls no edge; that is captured by
  giving it bounded-difference constant `0`, which is where the general-constants form of the
  inequality (their Theorem 9.1.3) earns its keep over the all-ones form.

  The notes' sample space is a product of factors of different sizes; this uses the uniform
  product `Fin n → (Fin n → Bool)`, which is what the bounded-differences development is
  stated for, at the cost of redundant coordinates that no lemma has to mention.

* **§9.2 martingale concentration** is upstream:
  `measure_sum_ge_le_of_HasCondSubgaussianMGF` in `SubGaussian.lean` is the
  **Azuma–Hoeffding inequality**. `Mathlib/Probability/Martingale/` supplies the martingale
  theory around it (`Basic`, `Convergence`, `OptionalStopping`, `OptionalSampling`,
  `Upcrossing`, `BorelCantelli`, `Centering`).
* **§9.5 Talagrand's inequality** — absent from Mathlib; the **convex distance is now set up
  here** (`Chapter09/Talagrand.lean`) and the inequality itself is published as a task.

  The definitions are where the design choices sit, so they are recorded rather than left to
  whoever proves the analytic core: `PMC.wHamDist` (weighted Hamming distance),
  `PMC.wDistToSet` (total, taken to be `0` on the empty set), and `PMC.convexDist` as an
  `sSup` over the unit sphere of nonnegative weights — well defined because
  `PMC.wDistToSet_le_sqrt` bounds the set by `√n` via Cauchy–Schwarz. It vanishes on `A` and
  is nonnegative.

  **Theorem 9.5.21 (certifiable functions) is proved**, given the inequality as a hypothesis
  (`PMC.card_mul_card_certifiable_le`): `P(f ≤ r-t) P(f ≥ r) ≤ e^{-t²/(4s)}`. That is the
  *combinatorial* half of the section, and it turned out to need **no convex geometry at
  all** — the normalised indicator of a certificate is already a unit weight vector
  witnessing `d_T(y,A) ≥ t/√s` (`PMC.unitWeights_indicator`), and the rest is counting, with
  `PMC.card_disagree_ge` supplying the key step by *splicing* the certificate's coordinates
  in. It is also the form the section's applications use (longest increasing subsequence,
  Euclidean TSP), so those become reachable once task #49 lands.

  **Why it is worth the trouble**: the bounded differences bound degrades as `exp(-t²/n)`,
  while Talagrand's has no `n` in the exponent at all. The proof is an induction on
  coordinates with Hölder, plus the delicate elementary fact
  `inf_{0≤λ≤1} e^{(1-λ)²/4} r^{-λ} ≤ 2 - r`; the notes prove neither, which is why this is a
  task rather than a gap to fill inline.
* **§9.4 isoperimetric inequalities** — absent from Mathlib, and now **started here**
  (`ProbMethods/Chapter09/HammingCube.lean`). The cube is `Finset (Fin n)`, as in Chapter 5.
  Proved: `PMC.cubeNbhd_lowBall` (the `t`-neighbourhood of a Hamming ball is the ball of
  radius `t` larger — exactly), `PMC.card_lowBall_ge` (the Chernoff estimate, where Chapter
  5's bound at `λ = 2t/√n` gives `exp(-2t²/n)` on the nose), `PMC.card_lowBall_half_le`, the
  cube metric lemmas, and **Theorems 9.4.5 and 9.4.6 with Harper's inequality as an explicit
  hypothesis** — so those two are `sorry`-free and what is missing is visible in the
  statement. Harper's inequality itself (Theorem 9.4.3, which the notes state without proof)
  is published as task #46.

  Worth recording: 9.4.6's hypothesis had to be made **strict** where the notes write
  `|A| ≥ ε2ⁿ`. At `|A| = ε2ⁿ` exactly the counting step yields `2ⁿ ≤ 2ⁿ` and no
  contradiction; the notes' proof quietly uses a strict Chernoff bound there.

  **And with §9.1 proved, Theorem 9.4.6 no longer needs Harper at all.**
  `PMC.card_fNbhd_ge` (`Chapter09/CubeExpansion.lean`) is the notes' *second* proof: apply the
  bounded differences inequality to `f = dist(·, A)`, which has bounded differences `1` and
  vanishes on `A`; since `A` is more than an `ε` fraction, the lower tail forces `E f < t`, and
  the upper tail then puts all but an `ε` fraction within `2t` of `A`. That version carries no
  Harper hypothesis — only Hoeffding, via §9.1.

  It is stated in the `Fin n → Bool` encoding, the shape §9.1 is written for, rather than the
  `Finset (Fin n)` encoding of the Harper route. **Both encodings are kept on purpose**: a
  transfer layer whose only job would be to restate a theorem already proved is not worth its
  weight, and each proof reads best in its own encoding.
* **§9.6 Euclidean TSP** — absent, and downstream of Talagrand.

So Chapter 9 is *not* the wall it was recorded as. Its first two sections are upstream in
`MeasureTheory` form; Talagrand and the geometric sections remain genuinely absent.

## Chapter 10 (Entropy) — groundwork present, the combinatorial results absent

Present: `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean` (the `x log x` function with
its convexity), `Analysis/SpecialFunctions/BinaryEntropy.lean`, and
`Mathlib/InformationTheory/` with `KullbackLeibler/` (Basic, ChainRule, DataProcessing,
KLFun), `Coding`, `Hamming`.

Absent: any **discrete Shannon entropy of a random variable** — no definition was found —
and hence §10.1's basic properties, §10.2 (permanents, perfect matchings), §10.3
(Sidorenko) and §10.4 (**Shearer's lemma**). The analytic ingredients exist; the
combinatorial entropy layer would have to be built, starting with the definition.

## Chapters 6, 8, 11 — genuinely absent

* **Chapter 6, Lovász Local Lemma** — no `lovasz`, `local_lemma` or `localLemma` anywhere.
  The only hit was the surname in a `KruskalKatona` reference. The symmetric LLL *is*
  expressible in this project's finite weighted framework (events as subsets of a finite
  space, dependency via a graph), so this is real but reachable work, not a framework
  limitation.
* **Chapter 8, Janson inequalities** — absent. Also expressible finitely, and it builds on
  the `G(n,p)` weights and second-moment machinery already here.
* **Chapter 11, hypergraph containers** — absent.

## What this changes

The remaining work sorts into three piles, and the survey moved things between them:

1. **Upstream (do not build):** §1.2 Sperner/LYM/EKR, §2.3 Turán structural, §3.3 Markov,
   §4.7 Weierstrass, §5.0.5 Hoeffding, §7.1 FKG, §9.1–§9.2 Azuma–Hoeffding.
2. **Reachable in the finite framework:** Chapter 6 (LLL), Chapter 8 (Janson), §4.6,
   §5.0.7, `sumfree`, `unbalancing`. All build on machinery now in `Weighted.lean`.
3. **Genuinely absent from Mathlib and large:** Talagrand (§9.5), the geometric sections
   (§3.2, §9.4, §9.6), planarity (§2.6), containers (Chapter 11), the discrete entropy
   layer (Chapter 10).

**Chapter 6 is the best next target**: entirely absent from Mathlib, entirely expressible
in the framework that exists here, and the local lemma is the single most-cited result in
the book.
