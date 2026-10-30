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

/-- A point strictly inside `[-1, 1]`, moved along a nonzero direction, stays in `[-1, 1]` up to
a positive time `τ` and is at `±1` at time `τ`. -/
private lemma exists_time_to_boundary {x c : ℝ} (hx : |x| < 1) (hc : c ≠ 0) :
    ∃ τ : ℝ, 0 < τ ∧ (∀ t, 0 ≤ t → t ≤ τ → |x + t * c| ≤ 1) ∧ |x + τ * c| = 1 := by
  obtain ⟨hx₁, hx₂⟩ := abs_lt.mp hx
  rcases lt_or_gt_of_ne hc with hc | hc
  · refine ⟨(1 + x) / (-c), div_pos (by linarith) (by linarith), fun t ht₀ ht => ?_, ?_⟩
    · rw [le_div_iff₀ (by linarith)] at ht
      exact abs_le.mpr ⟨by linarith, by nlinarith⟩
    · have hτ : x + (1 + x) / (-c) * c = -1 := by
        field_simp
        ring
      rw [hτ, abs_neg, abs_one]
  · refine ⟨(1 - x) / c, div_pos (by linarith) hc, fun t ht₀ ht => ?_, ?_⟩
    · rw [le_div_iff₀ hc] at ht
      exact abs_le.mpr ⟨by nlinarith, by linarith⟩
    · have hτ : x + (1 - x) / c * c = 1 := by
        field_simp
        ring
      rw [hτ, abs_one]

/-- More than `n` indices in `S` give a nontrivial linear relation among vectors of `ℝⁿ` that is
supported on `S`. -/
private lemma exists_relation_supported_on {m n : ℕ} (v : Fin m → (Fin n → ℝ))
    (S : Finset (Fin m)) (hS : n < #S) :
    ∃ c : Fin m → ℝ, (∀ i, c i ≠ 0 → i ∈ S) ∧ ∑ i, c i • v i = 0 ∧ ∃ i, c i ≠ 0 := by
  classical
  have hdep : ¬ LinearIndependent ℝ fun i : S => v i := fun h => by
    have hcard := (Pi.basisFun ℝ (Fin n)).card_le_card_of_linearIndependent h
    rw [Fintype.card_coe, Fintype.card_fin] at hcard
    omega
  obtain ⟨g, hg, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let c : Fin m → ℝ := fun i => if h : i ∈ S then g ⟨i, h⟩ else 0
  have hc : ∀ i : S, c i = g i := fun i => by simp [c]
  refine ⟨c, fun i hi => ?_, ?_, i₁, by rwa [hc]⟩
  · by_contra h
    simp [c, h] at hi
  · calc
      ∑ i, c i • v i = ∑ i ∈ S, c i • v i :=
        (Finset.sum_subset (subset_univ S) fun i _ hi => by simp [c, hi]).symm
      _ = ∑ i : S, c i • v i := (Finset.sum_coe_sort S _).symm
      _ = 0 := by simpa only [hc] using hg

/-- The rounding step: a solution with more than `n` fractional coefficients can be replaced by
one with strictly fewer. -/
private lemma exists_fewer_fractional {m n : ℕ} (v : Fin m → (Fin n → ℝ)) {a : Fin m → ℝ}
    (ha : ∀ i, |a i| ≤ 1) (hsum : ∑ i, a i • v i = 0)
    (hn : n < #((univ : Finset (Fin m)).filter fun i => |a i| ≠ 1)) :
    ∃ b : Fin m → ℝ, (∀ i, |b i| ≤ 1) ∧ ∑ i, b i • v i = 0 ∧
      #((univ : Finset (Fin m)).filter fun i => |b i| ≠ 1) <
        #((univ : Finset (Fin m)).filter fun i => |a i| ≠ 1) := by
  classical
  obtain ⟨c, hcS, hcsum, i₁, hi₁⟩ := exists_relation_supported_on v _ hn
  have hfrac : ∀ i, c i ≠ 0 → |a i| ≠ 1 := fun i hi => by simpa using hcS i hi
  have htime : ∀ i, c i ≠ 0 →
      ∃ τ : ℝ, 0 < τ ∧ (∀ t, 0 ≤ t → t ≤ τ → |a i + t * c i| ≤ 1) ∧ |a i + τ * c i| = 1 :=
    fun i hi => exists_time_to_boundary (lt_of_le_of_ne (ha i) (hfrac i hi)) hi
  choose! τ hτ₀ hτ hτ₁ using htime
  obtain ⟨i₀, hi₀, hmin⟩ := ((univ : Finset (Fin m)).filter fun i => c i ≠ 0).exists_min_image τ
    ⟨i₁, by simpa using hi₁⟩
  have hi₀' : c i₀ ≠ 0 := by simpa using hi₀
  have ht₀ : 0 ≤ τ i₀ := (hτ₀ i₀ hi₀').le
  refine ⟨fun i => a i + τ i₀ * c i, fun i => ?_, ?_, Finset.card_lt_card ?_⟩
  · by_cases hi : c i = 0
    · simpa [hi] using ha i
    · exact hτ i hi (τ i₀) ht₀ (hmin i (by simpa using hi))
  · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, hsum, hcsum,
      smul_zero, add_zero]
  · refine Finset.ssubset_iff_of_subset (fun i hi => ?_) |>.mpr ⟨i₀, ?_, ?_⟩
    · have hb : |a i + τ i₀ * c i| ≠ 1 := by simpa using hi
      refine Finset.mem_filter.mpr ⟨mem_univ i, fun hai => hb ?_⟩
      have hc : c i = 0 := by
        by_contra hc
        exact hfrac i hc hai
      simpa [hc] using hai
    · simpa using hfrac i₀ hi₀'
    · simpa using hτ₁ i₀ hi₀'

/-- **Lemma 5.1.6.** Any `m` vectors in `ℝⁿ` admit coefficients in `[-1, 1]`, all but at most
`n` of them `±1`, that cancel them.

Both bounds in the statement are tight in the obvious ways: the coefficients cannot be forced
to be `±1` everywhere (take `m = 1` and `v₁ ≠ 0`), and `n` fractional coordinates are needed
(take `m = n` and `v` a basis). -/
theorem exists_signs_sum_smul_eq_zero {m n : ℕ} (v : Fin m → (Fin n → ℝ)) :
    ∃ a : Fin m → ℝ, (∀ i, |a i| ≤ 1) ∧
      #((univ : Finset (Fin m)).filter fun i => |a i| ≠ 1) ≤ n ∧
      ∑ i, a i • v i = 0 := by
  obtain ⟨a, ⟨ha, hsum⟩, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun a : Fin m → ℝ => (∀ i, |a i| ≤ 1) ∧ ∑ i, a i • v i = 0)
    (fun a => #((univ : Finset (Fin m)).filter fun i => |a i| ≠ 1))
    ⟨0, by simp, by simp⟩
  refine ⟨a, ha, not_lt.mp fun hn => ?_, hsum⟩
  obtain ⟨b, hb, hbsum, hlt⟩ := exists_fewer_fractional v ha hsum hn
  exact hlt.not_ge (hmin ⟨hb, hbsum⟩ hlt.le)

end PMC
