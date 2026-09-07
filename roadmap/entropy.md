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
| Conditional entropy and the chain rule | open |
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

## Next

The chain rule `H(X,Y) = H(X) + H(Y | X)` is the natural next step: it needs conditional
entropy, which in this framework is `∑ b, P(X = b) * wentropy (conditioned weight) Y`, and
the conditioned weight is just `w` restricted to a fibre and renormalised. Shearer's lemma
then follows from the chain rule by the usual induction, and Shearer is what the
combinatorial applications actually use.
