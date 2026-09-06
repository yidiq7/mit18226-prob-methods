import ProbMethods.Basic

/-!
# §1.1 — Lower bounds to Ramsey numbers

Zhao, *Probabilistic Methods in Combinatorics*, Theorems 1.1.2 and 1.1.6.
-/

open Finset

namespace PMC

/-- **Erdős' Ramsey lower bound** (Zhao, Theorem 1.1.2; Erdős 1947).

If `(n.choose k) * 2 ^ (1 - k.choose 2) < 1` then `R(k, k) > n`.

The hypothesis is stated without real exponents by clearing denominators: for `k ≥ 2`,
`(n.choose k) * 2 ^ (1 - k.choose 2) < 1` is equivalent to `2 * n.choose k < 2 ^ k.choose 2`.

The book's proof colours the edges of `Kₙ` red/blue independently and uniformly. Each of
the `n.choose k` vertex `k`-sets induces a monochromatic `K_k` with probability
`2 ^ (1 - k.choose 2)`, so by the union bound the probability that some `k`-set is
monochromatic is less than `1`; hence some colouring has none. -/
theorem not_ramseyProp_of_two_mul_choose_lt {n k : ℕ}
    (h : 2 * n.choose k < 2 ^ k.choose 2) : ¬ RamseyProp n k k := by
  sorry

/-- **Ramsey lower bound via alteration** (Zhao, Theorem 1.1.6).

For all `k, n` we have `R(k, k) > n - (n.choose k) * 2 ^ (1 - k.choose 2)`.

Stated as: there is an `m` at least that large carrying a red/blue colouring of `K_m` with
no monochromatic `K_k`. For `k ≥ 2` the deleted quantity
`(n.choose k) * 2 ^ (1 - k.choose 2)` equals `(n.choose k) / 2 ^ (k.choose 2 - 1)`.

The book's proof colours `Kₙ` at random, then deletes one vertex from every monochromatic
`K_k`. The expected number of monochromatic `K_k`'s is `(n.choose k) * 2 ^ (1 - k.choose 2)`,
so with positive probability at least that many vertices survive. -/
theorem exists_cliqueFree_of_alteration (n k : ℕ) (hk : 2 ≤ k) :
    ∃ m : ℕ, (n : ℝ) - (n.choose k : ℝ) / 2 ^ (k.choose 2 - 1) ≤ m ∧
      ∃ G : SimpleGraph (Fin m), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  sorry

end PMC
