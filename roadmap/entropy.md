# Chapter 10 — Entropy

Zhao, *Probabilistic Methods in Combinatorics*, Chapter 10.

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
| Shearer's lemma | open |
| Applications (counting, Loomis–Whitney, triangle bound) | open |

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

## Next: Shearer

Every structural inequality Shearer's induction needs is now proved — the chain rule,
`H(Y|X) ≤ H(Y)`, `H(Y|X,Z) ≤ H(Y|X)`, and relabelling invariance. What remains is
bookkeeping: the **n-fold chain rule** over a linearly ordered index set. Then Shearer is the usual argument: expand `H(X_S)` along the chain rule within `S`, weaken
each conditional entropy to condition on the whole prefix, and sum over the family — each
coordinate is counted at least `k` times, giving `k · H(X) ≤ ∑_{S ∈ F} H(X_S)`.

**Plan for the tuple types.** Keep all coordinate types equal and represent the restriction
`X_S` by *masking* coordinates outside `S` to a default value. Masking has the same entropy
as the genuine restriction (the map between their value sets is injective where the
distribution is supported) and it keeps every random variable at type `Ω → ι → β`, avoiding
dependent types entirely. Worth the small lemma it costs.
