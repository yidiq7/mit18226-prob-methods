import ProbMethods.Weighted
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# §4.5 — Theorem 4.5.1, Hardy–Ramanujan by Turán's second moment

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 4.5.1 (Hardy–Ramanujan 1917, this
proof Turán 1934): for every `ε > 0` there is `C` such that for all large `n`, all but an
`ε`-fraction of `x ∈ [n]` satisfy

    |ν(x) - log log n| ≤ C √(log log n),

where `ν x` is the number of *distinct* prime divisors of `x` (`Nat.primeFactors x |>.card`).

**Mertens' second theorem is an explicit hypothesis**, not an assumption hidden in the proof.
`∑_{p ≤ m} 1/p = log log m + O(1)` is analytic number theory that Mathlib does not have, and
the notes quote it too ("We quote Merten's theorem from analytic number theory"). Naming it in
the statement is the same device used for Harper's inequality in Theorem 4.6.6 and for Theorem
6.5.5 in the Latin-transversal bound: the gap stays visible in the type rather than in prose.
Everything else is the second moment method, which this development already has.

## The route

Sample `x ∈ [n]` uniformly and let `X p` be the indicator of `p ∣ x`. Put `M = n^{1/10}` and
`X = ∑_{p ≤ M} X p`.

* **`ν` and `X` differ by at most `10`.** `ν x - 10 ≤ X x ≤ ν x`, because `x ≤ n` cannot have
  more than `10` prime factors exceeding `n^{1/10}`. So it is enough to concentrate `X`, and
  the additive `10` is absorbed by `C √(log log n)`.
* **First moment.** Exactly `⌊n/p⌋` integers in `[n]` are divisible by `p`, so
  `E[X p] = ⌊n/p⌋/n = 1/p + O(1/n)`, and Mertens gives
  `E X = log log M + O(1) = log log n + O(1)`, since `log log n^{1/10} = log log n - log 10`.
* **Second moment.** For distinct primes `p, q`, `p ∣ x ∧ q ∣ x ↔ pq ∣ x`, so
  `E[X p X q] = ⌊n/pq⌋/n = 1/(pq) + O(1/n)` and the covariance of `X p, X q` is `O(1/n)`. There
  are at most `M² = n^{1/5}` pairs, contributing `O(n^{-4/5})`; the diagonal contributes
  `∑_{p ≤ M} (1/p)(1 - 1/p) ≤ log log n + O(1)`. Hence `Var X = O(log log n)`.
* **Chebyshev.** `PMC.wchebyshev` at deviation `C √(log log n)` gives an exceptional set of
  measure `O(1/C²)`, which is below `ε` once `C` is large — and `C` is allowed to depend on `ε`,
  which is exactly the shape of the statement.

The sample space is `Fin n` (or `Finset.Icc 1 n`) with uniform weights, so `PMC.wmean`,
`PMC.wvar` and `PMC.wchebyshev` apply directly; no measure theory is involved.
-/

open Finset

namespace PMC

section HardyRamanujan

/-- **Theorem 4.5.1** (Hardy–Ramanujan; Turán's proof), with Mertens' second theorem as an
explicit hypothesis: for every `ε > 0` there is a `C` such that for all large `n`, at most an
`ε`-fraction of `x ∈ [n]` have `|ν(x) - log log n| > C √(log log n)`. -/
theorem hardy_ramanujan {ε : ℝ} (hε : 0 < ε)
    (mertens : ∃ B : ℝ, ∀ m : ℕ, 3 ≤ m →
      |(∑ p ∈ Nat.primesBelow m, (1 : ℝ) / p) - Real.log (Real.log m)| ≤ B) :
    ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N,
      (#((Finset.Icc 1 n).filter fun x =>
          C * Real.sqrt (Real.log (Real.log n))
            < |(x.primeFactors.card : ℝ) - Real.log (Real.log n)|) : ℝ)
        ≤ ε * n := by
  sorry

end HardyRamanujan

end PMC
