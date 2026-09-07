import ProbMethods.Weighted
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# §5.0 — The Chernoff bound

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 5.0.1.

A sum of `n` independent uniform `±1` variables is realised here as a subset `S ⊆ Fin n`
carrying the uniform weight, with the sum being `2 * #S - n`. So the statement counts
subsets rather than referring to a measure, and the bound is on the *number* of subsets
whose sign sum is large — which is `2 ^ n` times the probability.

The proof is the moment generating function argument: bound `∑ exp (t * (2 #S - n))` by
`prod_add`, apply `Real.cosh_le_exp_half_sq`, and optimise at `t = λ / √n`.
-/

open Finset

namespace PMC

/-- `∑ over T ⊆ A of x ^ #T = (x + 1) ^ #A`, from `Finset.prod_add` with both factors
constant. This is the moment generating function of the uniform measure on the subsets of
`A`. -/
private lemma sum_pow_card {α : Type*} [DecidableEq α] (A : Finset α) (x : ℝ) :
    ∑ T ∈ A.powerset, x ^ #T = (x + 1) ^ #A := by
  have h := Finset.prod_add (fun _ : α => x) (fun _ : α => (1 : ℝ)) A
  calc ∑ T ∈ A.powerset, x ^ #T
      = ∑ T ∈ A.powerset, (∏ _i ∈ T, x) * ∏ _i ∈ A \ T, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [prod_const, prod_const, one_pow, mul_one]
    _ = ∏ _i ∈ A, (x + 1) := h.symm
    _ = (x + 1) ^ #A := by rw [prod_const]

/-- **The Chernoff bound** (Zhao, Theorem 5.0.1).

At most `2 ^ n * exp (-λ² / 2)` of the `2 ^ n` subsets of `Fin n` have sign sum
`2 * #S - n` at least `λ * √n`. Dividing by `2 ^ n` gives the notes'
`P(Sₙ ≥ λ√n) ≤ exp (-λ² / 2)`.

`0 < n` is needed and the notes leave it implicit: at `n = 0` the sum is `0`, the threshold
`λ * √0` is also `0`, so *every* subset qualifies and the left side is `1` while the right
is `exp (-λ²/2) < 1`. -/
theorem card_filter_sign_sum_le {α : Type*} [DecidableEq α] (A : Finset α)
    (hA : 0 < #A) {lam : ℝ} (hlam : 0 < lam) :
    (#(A.powerset.filter fun T => lam * Real.sqrt #A ≤ 2 * (#T : ℝ) - #A) : ℝ)
      ≤ 2 ^ #A * Real.exp (-(lam ^ 2) / 2) := by
  classical
  have hnR : (0 : ℝ) < #A := by exact_mod_cast hA
  have hsq : 0 < Real.sqrt #A := Real.sqrt_pos.mpr hnR
  set t : ℝ := lam / Real.sqrt #A with htdef
  have ht0 : 0 < t := div_pos hlam hsq
  have hsqsq : Real.sqrt #A ^ 2 = (#A : ℝ) := Real.sq_sqrt hnR.le
  set F : Finset (Finset α) := A.powerset.filter
      (fun T => lam * Real.sqrt #A ≤ 2 * (#T : ℝ) - #A) with hFdef
  have hthr : t * (lam * Real.sqrt #A) = lam ^ 2 := by
    rw [htdef, div_mul_eq_mul_div, mul_comm lam (Real.sqrt #A)]
    field_simp
  have hnt : (#A : ℝ) * t ^ 2 = lam ^ 2 := by
    rw [htdef, div_pow, hsqsq]
    field_simp
  have hlow : (#F : ℝ) * Real.exp (lam ^ 2)
      ≤ ∑ T ∈ F, Real.exp (t * (2 * (#T : ℝ) - #A)) := by
    calc (#F : ℝ) * Real.exp (lam ^ 2) = ∑ _T ∈ F, Real.exp (lam ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ T ∈ F, Real.exp (t * (2 * (#T : ℝ) - #A)) := by
          refine Finset.sum_le_sum fun T hT => ?_
          rw [hFdef, mem_filter] at hT
          rw [← hthr]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT.2 ht0.le)
  have htot : ∑ T ∈ A.powerset, Real.exp (t * (2 * (#T : ℝ) - #A))
      = (Real.exp (-t) + Real.exp t) ^ #A := by
    have hterm : ∀ T : Finset α, Real.exp (t * (2 * (#T : ℝ) - #A))
        = Real.exp (2 * t) ^ (#T) * Real.exp (-(t * #A)) := by
      intro T
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [Finset.sum_congr rfl (fun T _ => hterm T), ← Finset.sum_mul, sum_pow_card]
    have h1 : Real.exp (-(t * #A)) = Real.exp (-t) ^ #A := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [h1, ← mul_pow]
    congr 1
    rw [add_mul, one_mul, ← Real.exp_add, show (2 : ℝ) * t + -t = t by ring, add_comm]
  have hcosh : (Real.exp (-t) + Real.exp t) ^ #A
      ≤ 2 ^ #A * Real.exp (lam ^ 2 / 2) := by
    have hc : Real.exp (-t) + Real.exp t = 2 * Real.cosh t := by
      rw [Real.cosh_eq]; ring
    rw [hc, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc Real.cosh t ^ #A ≤ Real.exp (t ^ 2 / 2) ^ #A :=
          pow_le_pow_left₀ (by rw [Real.cosh_eq]; positivity)
            (Real.cosh_le_exp_half_sq t) _
      _ = Real.exp ((#A : ℝ) * (t ^ 2 / 2)) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (lam ^ 2 / 2) := by
          rw [show (#A : ℝ) * (t ^ 2 / 2) = (#A : ℝ) * t ^ 2 / 2 by ring, hnt]
  have hchain : (#F : ℝ) * Real.exp (lam ^ 2) ≤ 2 ^ #A * Real.exp (lam ^ 2 / 2) := by
    calc (#F : ℝ) * Real.exp (lam ^ 2)
        ≤ ∑ T ∈ F, Real.exp (t * (2 * (#T : ℝ) - #A)) := hlow
      _ ≤ ∑ T ∈ A.powerset, Real.exp (t * (2 * (#T : ℝ) - #A)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun T _ _ => (Real.exp_pos _).le
          rw [hFdef]; exact filter_subset _ _
      _ = (Real.exp (-t) + Real.exp t) ^ #A := htot
      _ ≤ 2 ^ #A * Real.exp (lam ^ 2 / 2) := hcosh
  have hpos : 0 < Real.exp (lam ^ 2 / 2) := Real.exp_pos _
  have hexp : Real.exp (lam ^ 2) = Real.exp (lam ^ 2 / 2) * Real.exp (lam ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hkey : (#F : ℝ) * Real.exp (lam ^ 2 / 2) ≤ 2 ^ #A := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc (#F : ℝ) * Real.exp (lam ^ 2 / 2) * Real.exp (lam ^ 2 / 2)
        = (#F : ℝ) * Real.exp (lam ^ 2) := by rw [hexp]; ring
      _ ≤ 2 ^ #A * Real.exp (lam ^ 2 / 2) := hchain
  rw [show -(lam ^ 2) / 2 = -(lam ^ 2 / 2) by ring, Real.exp_neg, ← div_eq_mul_inv,
    le_div_iff₀ hpos]
  exact hkey

/-- **The two-sided Chernoff bound** (Zhao, Corollary 5.0.3).

`#{T ⊆ A : λ√#A ≤ |2 #T - #A|} ≤ 2 * (2 ^ #A * exp (-λ²/2))`, i.e.
`P(|S| ≥ λ√#A) ≤ 2 exp(-λ²/2)` after dividing by `2 ^ #A`.

The lower tail is the upper tail of the complement: `T ↦ A \ T` sends `2 #T - #A` to its
negation, so the two tails have exactly equal cardinality and one application of the
one-sided bound suffices. -/
theorem card_filter_abs_sign_sum_le {α : Type*} [DecidableEq α] (A : Finset α)
    (hA : 0 < #A) {lam : ℝ} (hlam : 0 < lam) :
    (#(A.powerset.filter fun T => lam * Real.sqrt #A ≤ |2 * (#T : ℝ) - #A|) : ℝ)
      ≤ 2 * (2 ^ #A * Real.exp (-(lam ^ 2) / 2)) := by
  classical
  set P : Finset (Finset α) := A.powerset.filter
      (fun T => lam * Real.sqrt #A ≤ 2 * (#T : ℝ) - #A) with hPdef
  set N : Finset (Finset α) := A.powerset.filter
      (fun T => 2 * (#T : ℝ) - #A ≤ -(lam * Real.sqrt #A)) with hNdef
  have hcompl : ∀ T ∈ A.powerset, 2 * ((#(A \ T) : ℕ) : ℝ) - #A = -(2 * (#T : ℝ) - #A) := by
    intro T hT
    rw [mem_powerset] at hT
    rw [card_sdiff_of_subset hT, Nat.cast_sub (card_le_card hT)]
    ring
  have hNP : #N = #P := by
    refine Finset.card_nbij' (fun T => A \ T) (fun T => A \ T) ?_ ?_ ?_ ?_
    · intro T hT
      rw [hNdef, mem_coe, mem_filter] at hT
      rw [hPdef, mem_coe, mem_filter]
      refine ⟨mem_powerset.mpr sdiff_subset, ?_⟩
      rw [hcompl T hT.1]
      linarith [hT.2]
    · intro T hT
      rw [hPdef, mem_coe, mem_filter] at hT
      rw [hNdef, mem_coe, mem_filter]
      refine ⟨mem_powerset.mpr sdiff_subset, ?_⟩
      rw [hcompl T hT.1]
      linarith [hT.2]
    · intro T hT
      rw [hNdef, mem_coe, mem_filter, mem_powerset] at hT
      exact Finset.sdiff_sdiff_eq_self hT.1
    · intro T hT
      rw [hPdef, mem_coe, mem_filter, mem_powerset] at hT
      exact Finset.sdiff_sdiff_eq_self hT.1
  have hsub : A.powerset.filter
      (fun T => lam * Real.sqrt #A ≤ |2 * (#T : ℝ) - #A|) ⊆ P ∪ N := by
    intro T hT
    rw [mem_filter] at hT
    rw [mem_union, hPdef, hNdef, mem_filter, mem_filter]
    rcases le_abs.mp hT.2 with h | h
    · exact Or.inl ⟨hT.1, h⟩
    · exact Or.inr ⟨hT.1, by linarith⟩
  have hchern := card_filter_sign_sum_le A hA hlam
  rw [← hPdef] at hchern
  calc (#(A.powerset.filter fun T => lam * Real.sqrt #A ≤ |2 * (#T : ℝ) - #A|) : ℝ)
      ≤ ((#(P ∪ N) : ℕ) : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ ((#P : ℕ) : ℝ) + ((#N : ℕ) : ℝ) := by exact_mod_cast card_union_le P N
    _ = 2 * ((#P : ℕ) : ℝ) := by rw [hNP]; ring
    _ ≤ 2 * (2 ^ #A * Real.exp (-(lam ^ 2) / 2)) := by linarith [hchern]

end PMC
