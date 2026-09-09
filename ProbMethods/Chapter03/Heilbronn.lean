import ProbMethods.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
# §3.2 — Theorem 3.2.3, the Heilbronn triangle problem

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 3.2.3: there is `c > 0` such that for
every `n` one can place `n` points in `[0,1]²` with every triple spanning a triangle of area at
least `c/n²`.

**The statement is elementary even though the proof is not.** It asks only for `n` points, with
the area of a triple written out as the usual determinant, so nothing continuous appears in it —
which is why this is publishable while the rest of §3.2 is not.

## Two routes, and the second one is finite

The notes argue over the continuous cube: drop `2n` uniform random points into `[0,1]²`, note
that a random triple has area below `ε` with probability `O(ε)` — the base of the triangle is
`O(1)` and the third point must land in a strip of width `O(ε)` — so the expected number of bad
triples among `2n` points is `O(ε n³)`, which is below `n` at `ε = c/n²`. Deleting one point
from each bad triple leaves `n` points and no bad triple. That is an alteration argument on
`([0,1]²)^{2n}`, so it needs `MeasureTheory.Measure.pi` and the volume of a strip.

**A grid makes it finite.** Restrict the points to `(1/N)·[N]²` with `N = n³`, say, and sample
uniformly from the `N²` grid cells instead. The strip estimate becomes a lattice-point count,
`PMC.bweight`-style product weights apply, and the alteration is the same. The discretisation
costs a constant factor in `c`, which the statement's existential absorbs. This route stays
inside the machinery this development already has, and is the one to try first.

Either way, keep `c` explicit in the proof and only existentially quantified in the statement —
the constant that comes out of the strip estimate is around `1/100`, so there is room.
-/

open Finset

namespace PMC

section Heilbronn

/-- Twice the signed area of the triangle spanned by three points of the plane. -/
def twiceArea (p q r : ℝ × ℝ) : ℝ :=
  p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)

/-- **Theorem 3.2.3 (Heilbronn).** For some absolute `c > 0` and every `n`, there are `n` points
of `[0,1]²` no three of which span a triangle of area below `c/n²`. -/
theorem exists_heilbronn_config :
    ∃ c > 0, ∀ n : ℕ, 1 ≤ n → ∃ P : Fin n → ℝ × ℝ,
      (∀ i, P i ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
      Function.Injective P ∧
      ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
        c / (n : ℝ) ^ 2 ≤ |twiceArea (P i) (P j) (P k)| / 2 := by
  sorry

end Heilbronn

end PMC
