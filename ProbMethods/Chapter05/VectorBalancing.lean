import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §5.1 — balancing vectors with few fractional coefficients (Lemma 5.1.6)

Zhao, *Probabilistic Methods in Combinatorics*, Lemma 5.1.6: given `v₁, …, v_m ∈ ℝⁿ`, there
are coefficients `a₁, …, a_m ∈ [-1, 1]`, **all but at most `n` of them `±1`**, with

    a₁ v₁ + ⋯ + a_m v_m = 0.

The point is the `n`: the coefficients are signs except on a set no larger than the dimension,
however many vectors there are. In §5.1 this is the rounding step that turns a fractional
balancing into a genuine `±1` colouring on all but `n` coordinates.

## The argument

`a = 0` is a solution, so solutions exist; among them take one with **as many `±1`
coefficients as possible**. The number of such coefficients is a natural number at most `m`,
so a maximum exists — no compactness is needed, which is what keeps this in reach of a finite
argument.

If more than `n` coefficients were fractional, the vectors at those coordinates would be more
than `n` vectors in `ℝⁿ`, hence linearly dependent: some nonzero `(cᵢ)` supported on the
fractional coordinates has `∑ cᵢ vᵢ = 0`. Then `a + t c` solves the same equation for every
`t`, and it stays in `[-1,1]^m` for small `|t|` because the fractional coordinates are
*strictly* inside. Increasing `|t|` until some fractional coordinate first reaches `±1` gives a
solution with strictly more `±1` coefficients — contradicting the choice of `a`.

## Hints

* the maximisation: `Nat.findGreatest` over `k ↦ ∃ a, (constraints) ∧ k ≤ #(extreme a)`, with
  classical decidability; `a = 0` gives `k = 0` and `#(extreme a) ≤ m` bounds it;
* linear dependence: `Fintype.not_linearIndependent_iff` for the coefficients, and
  `LinearIndependent.fintype_card_le_finrank` against
  `Module.finrank ℝ (Fin n → ℝ) = n` for why the family must be dependent;
* the step size: the minimum of `(1 - a i)/c i` and `(-1 - a i)/c i` over the fractional
  coordinates with `c i ≠ 0`, taken over a `Finset`, so it is a minimum and not an infimum.

The lemma has no consumer elsewhere in this development — §5.1's Theorem 5.1.1 is already
proved and Theorem 5.1.3 (Spencer's "six standard deviations") is not attempted — so nothing
is blocked on it.
-/

open Finset

namespace PMC

/-- **Lemma 5.1.6.** Any `m` vectors in `ℝⁿ` admit coefficients in `[-1, 1]`, all but at most
`n` of them `±1`, that cancel them.

Both bounds in the statement are tight in the obvious ways: the coefficients cannot be forced
to be `±1` everywhere (take `m = 1` and `v₁ ≠ 0`), and `n` fractional coordinates are needed
(take `m = n` and `v` a basis). -/
theorem exists_signs_sum_smul_eq_zero {m n : ℕ} (v : Fin m → (Fin n → ℝ)) :
    ∃ a : Fin m → ℝ, (∀ i, |a i| ≤ 1) ∧
      #((univ : Finset (Fin m)).filter fun i => |a i| ≠ 1) ≤ n ∧
      ∑ i, a i • v i = 0 := by
  sorry

end PMC
