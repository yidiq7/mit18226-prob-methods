import ProbMethods.Basic

/-!
# §2.2 — Large sum-free subsets

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 2.2.1.

Remark 2.2.2's sharpenings — Alon–Kleitman's `(n + 1) / 3`, Bourgain's `(n + 2) / 3`, and
the Eberhard–Green–Manners upper bound — are not nodes: the first two are refinements of
the same argument that the notes only sketch, and the last is asymptotic.
-/

open Finset

namespace PMC

/-- **Large sum-free subsets** (Zhao, Theorem 2.2.1; Erdős 1965).

Every set of `n` nonzero integers contains a sum-free subset of size at least `n / 3`,
stated as `#A ≤ 3 * #B` to keep the claim in `ℕ` and free of division.

The book's proof averages over a *continuum*: it draws `θ` uniformly from `[0, 1]`, sets
`A_θ = {a ∈ A : {aθ} ∈ (1/3, 2/3)}` — sum-free because `(1/3, 2/3)` is sum-free in `ℝ/ℤ` —
and computes `E|A_θ| = n/3`. That route needs Lebesgue measure and is not the one to take
here; `roadmap/linearity.md` gives the discrete mod-`p` argument instead, which is a
counting proof of the same statement. -/
theorem exists_sumFree_subset (A : Finset ℤ) (h0 : (0 : ℤ) ∉ A) :
    ∃ B ⊆ A, SumFree B ∧ #A ≤ 3 * #B := by
  sorry

end PMC
