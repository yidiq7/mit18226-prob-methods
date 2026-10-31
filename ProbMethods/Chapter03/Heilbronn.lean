import ProbMethods.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Field.ZMod

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
  -- Erdős' construction: for a prime `n < p ≤ 2n`, take the points `(i, i² mod p) / p`.
  -- The twice-area of the unscaled lattice triangle is an integer congruent mod `p` to a
  -- Vandermonde product of nonzero residues, hence a nonzero integer, so the area is at
  -- least `1 / (2p²) ≥ 1 / (8n²)`.
  refine ⟨1 / 8, by norm_num, fun n hn => ?_⟩
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  refine ⟨fun i => ((i : ℕ) / (p : ℝ), (((i : ℕ) ^ 2 % p : ℕ) : ℝ) / p), ?_, ?_, ?_⟩
  · intro i
    have hi : (i : ℕ) < p := lt_trans i.isLt hnp
    have hm : (i : ℕ) ^ 2 % p < p := Nat.mod_lt _ hp.pos
    refine ⟨⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩
    · rw [div_le_one hp0]; exact_mod_cast hi.le
    · rw [div_le_one hp0]; exact_mod_cast hm.le
  · intro i j hij
    have h := congrArg Prod.fst hij
    simp only at h
    rw [div_left_inj' hp0.ne', Nat.cast_inj] at h
    exact Fin.ext h
  · intro i j k hij hjk hik
    have hi : (i : ℕ) < p := lt_trans i.isLt hnp
    have hj : (j : ℕ) < p := lt_trans j.isLt hnp
    have hk : (k : ℕ) < p := lt_trans k.isLt hnp
    -- The integer twice-area of the unscaled lattice triangle.
    set a : ℕ := (i : ℕ)
    set b : ℕ := (j : ℕ)
    set d : ℕ := (k : ℕ)
    set T : ℤ := (a : ℤ) * (((b ^ 2 % p : ℕ) : ℤ) - ((d ^ 2 % p : ℕ) : ℤ)) +
      (b : ℤ) * (((d ^ 2 % p : ℕ) : ℤ) - ((a ^ 2 % p : ℕ) : ℤ)) +
      (d : ℤ) * (((a ^ 2 % p : ℕ) : ℤ) - ((b ^ 2 % p : ℕ) : ℤ)) with hT
    have hne : ∀ x y : ℕ, x < p → y < p → x ≠ y → ((x : ZMod p) - (y : ZMod p)) ≠ 0 := by
      intro x y hx hy hxy h
      apply hxy
      have h' : (x : ZMod p) = (y : ZMod p) := sub_eq_zero.mp h
      rw [ZMod.natCast_eq_natCast_iff'] at h'
      rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h'
    have hab : a ≠ b := fun h => hij (Fin.ext h)
    have hbd : b ≠ d := fun h => hjk (Fin.ext h)
    have had : a ≠ d := fun h => hik (Fin.ext h)
    have hTmod : (T : ZMod p) ≠ 0 := by
      have hc : ((T : ℤ) : ZMod p) =
          -(((a : ZMod p) - b) * ((b : ZMod p) - d) * ((a : ZMod p) - d)) := by
        simp only [hT, Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
          ZMod.natCast_mod, Nat.cast_pow]
        ring
      rw [hc, neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero (hne a b hi hj hab) (hne b d hj hk hbd)) (hne a d hi hk had)
    have hT0 : T ≠ 0 := fun h => hTmod (by rw [h]; simp)
    have hT1 : (1 : ℝ) ≤ |(T : ℝ)| := by
      have : (1 : ℤ) ≤ |T| := Int.one_le_abs hT0
      exact_mod_cast this
    have harea : twiceArea ((a : ℝ) / p, ((a ^ 2 % p : ℕ) : ℝ) / p)
        ((b : ℝ) / p, ((b ^ 2 % p : ℕ) : ℝ) / p)
        ((d : ℝ) / p, ((d ^ 2 % p : ℕ) : ℝ) / p) = (T : ℝ) / (p : ℝ) ^ 2 := by
      simp only [hT, twiceArea, Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast]
      field_simp
    show 1 / 8 / (n : ℝ) ^ 2 ≤ |twiceArea ((a : ℝ) / p, ((a ^ 2 % p : ℕ) : ℝ) / p)
        ((b : ℝ) / p, ((b ^ 2 % p : ℕ) : ℝ) / p)
        ((d : ℝ) / p, ((d ^ 2 % p : ℕ) : ℝ) / p)| / 2
    rw [harea, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hpn : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2n
    have hp2 : (p : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
    rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

end Heilbronn

end PMC
