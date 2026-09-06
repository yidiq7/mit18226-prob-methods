import ProbMethods.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# §2.5 — Unbalancing lights

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 2.5.1.

Theorem 2.5.2 is **not** a node: its proof rests on a compactness argument producing an
unspecified constant `c_k`, which is not something a statement can be checked against.
-/

open Finset

namespace PMC

/-- **Unbalancing lights** (Zhao, Theorem 2.5.1), with the constant made explicit.

Given an `n × n` array of `±1` values, some choice of row signs `x` and column signs `y`
makes `∑ i, ∑ j, a i j * x i * y j` at least `n ^ 2 * C(n-1, ⌊(n-1)/2⌋) / 2 ^ (n-1)`,
written multiplicatively to stay in `ℤ` with no division.

**The notes state this asymptotically**, as `(√(2/π) + o(1)) * n ^ (3/2)`, and reach that
form through the central limit theorem. The closed form above is the same bound before
that last step: the notes record in passing that
`E|S_n| = n * 2 ^ (1-n) * C(n-1, ⌊(n-1)/2⌋)` for `S_n` a sum of `n` independent uniform
`±1`, and summing over the `n` rows gives exactly this. Stating it this way keeps the node
in Chapter 2 instead of deferring it behind the machinery of Chapter 9, and follows the
roadmap's rule that asymptotic results are either deferred or made explicit.

Zhao's proof picks the column signs `y` uniformly at random, sets `R i = ∑ j, a i j * y j`,
and takes `x i` to be the sign of `R i`, so that the double sum becomes `∑ i, |R i|`. Each
`R i` is distributed as `S_n`, so the expectation is `n * E|S_n|` and some `y` attains it. -/
theorem exists_signs_two_pow_mul_le (n : ℕ) (a : Fin n → Fin n → ℤ)
    (ha : ∀ i j, a i j = 1 ∨ a i j = -1) :
    ∃ x y : Fin n → ℤ, (∀ i, x i = 1 ∨ x i = -1) ∧ (∀ j, y j = 1 ∨ y j = -1) ∧
      (n : ℤ) ^ 2 * ((n - 1).choose ((n - 1) / 2) : ℤ)
        ≤ (∑ i, ∑ j, a i j * x i * y j) * 2 ^ (n - 1) := by
  sorry

end PMC
