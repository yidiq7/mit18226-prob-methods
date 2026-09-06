import ProbMethods.Basic

/-!
# §2.1 — Hamiltonian paths in tournaments

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 2.1.2.

The minimisation half of Question 2.1.1 — that the transitive tournament has exactly one
Hamilton path, and that every tournament has at least one — is not a node here; the notes
leave it as an exercise, and it is not a probabilistic argument.
-/

open Finset

namespace PMC

/-- **Szele's theorem** (Zhao, Theorem 2.1.2; Szele 1943).

Some tournament on `n` vertices has at least `n! / 2 ^ (n - 1)` Hamilton paths.

Stated multiplicatively as `n ! ≤ #(hamiltonPaths t) * 2 ^ (n - 1)`, which says the same
thing while keeping the exponent free of truncated subtraction and the statement free of
division. This was, per the notes, the first use of the probabilistic method.

The book's proof orients every edge independently and uniformly at random. Each of the `n!`
orderings of the vertices is a Hamilton path with probability `2 ^ (1 - n)`, since it
constrains `n - 1` distinct edges, so the expected number of Hamilton paths is
`n ! * 2 ^ (1 - n)` and some tournament attains at least the mean. -/
theorem exists_tournament_factorial_le_hamiltonPaths (n : ℕ) :
    ∃ t : Sym2 (Fin n) → Bool, Nat.factorial n ≤ #(hamiltonPaths t) * 2 ^ (n - 1) := by
  sorry

end PMC
