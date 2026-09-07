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

/-- `∑ over S ⊆ univ of x ^ #S = (x + 1) ^ n`, from `Finset.prod_add` with both factors
constant. This is the moment generating function of the uniform measure on subsets. -/
private lemma sum_pow_card {n : ℕ} (x : ℝ) :
    ∑ S ∈ (univ : Finset (Fin n)).powerset, x ^ #S = (x + 1) ^ n := by
  have h := Finset.prod_add (fun _ : Fin n => x) (fun _ : Fin n => (1 : ℝ)) univ
  calc ∑ S ∈ (univ : Finset (Fin n)).powerset, x ^ #S
      = ∑ S ∈ (univ : Finset (Fin n)).powerset,
          (∏ _i ∈ S, x) * ∏ _i ∈ (univ : Finset (Fin n)) \ S, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [prod_const, prod_const, one_pow, mul_one]
    _ = ∏ _i ∈ (univ : Finset (Fin n)), (x + 1) := h.symm
    _ = (x + 1) ^ n := by rw [prod_const, card_univ, Fintype.card_fin]

/-- **The Chernoff bound** (Zhao, Theorem 5.0.1).

At most `2 ^ n * exp (-λ² / 2)` of the `2 ^ n` subsets of `Fin n` have sign sum
`2 * #S - n` at least `λ * √n`. Dividing by `2 ^ n` gives the notes'
`P(Sₙ ≥ λ√n) ≤ exp (-λ² / 2)`.

`0 < n` is needed and the notes leave it implicit: at `n = 0` the sum is `0`, the threshold
`λ * √0` is also `0`, so *every* subset qualifies and the left side is `1` while the right
is `exp (-λ²/2) < 1`. -/
theorem card_filter_sign_sum_le {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam) :
    (#((univ : Finset (Fin n)).powerset.filter
        fun S => lam * Real.sqrt n ≤ 2 * (#S : ℝ) - n) : ℝ)
      ≤ 2 ^ n * Real.exp (-(lam ^ 2) / 2) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  set t : ℝ := lam / Real.sqrt n with htdef
  have ht0 : 0 < t := div_pos hlam hsq
  have hsqsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  set F : Finset (Finset (Fin n)) := (univ : Finset (Fin n)).powerset.filter
      (fun S => lam * Real.sqrt n ≤ 2 * (#S : ℝ) - n) with hFdef
  have hthr : t * (lam * Real.sqrt n) = lam ^ 2 := by
    rw [htdef, div_mul_eq_mul_div, mul_comm lam (Real.sqrt n)]
    field_simp
  have hnt : (n : ℝ) * t ^ 2 = lam ^ 2 := by
    rw [htdef, div_pow, hsqsq]
    field_simp
  -- Each qualifying subset contributes at least `exp (lam ^ 2)`.
  have hlow : (#F : ℝ) * Real.exp (lam ^ 2)
      ≤ ∑ S ∈ F, Real.exp (t * (2 * (#S : ℝ) - n)) := by
    calc (#F : ℝ) * Real.exp (lam ^ 2) = ∑ _S ∈ F, Real.exp (lam ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ S ∈ F, Real.exp (t * (2 * (#S : ℝ) - n)) := by
          refine Finset.sum_le_sum fun S hS => ?_
          rw [hFdef, mem_filter] at hS
          rw [← hthr]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hS.2 ht0.le)
  -- The moment generating function.
  have htot : ∑ S ∈ (univ : Finset (Fin n)).powerset,
        Real.exp (t * (2 * (#S : ℝ) - n))
      = (Real.exp (-t) + Real.exp t) ^ n := by
    have hterm : ∀ S : Finset (Fin n), Real.exp (t * (2 * (#S : ℝ) - n))
        = Real.exp (2 * t) ^ (#S) * Real.exp (-(t * n)) := by
      intro S
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [Finset.sum_congr rfl (fun S _ => hterm S), ← Finset.sum_mul, sum_pow_card]
    have h1 : Real.exp (-(t * n)) = Real.exp (-t) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [h1, ← mul_pow]
    congr 1
    rw [add_mul, one_mul, ← Real.exp_add, show (2 : ℝ) * t + -t = t by ring, add_comm]
  -- `cosh t ≤ exp (t ^ 2 / 2)` is Mathlib's; the exponent collapses to `lam ^ 2 / 2`.
  have hcosh : (Real.exp (-t) + Real.exp t) ^ n ≤ 2 ^ n * Real.exp (lam ^ 2 / 2) := by
    have hc : Real.exp (-t) + Real.exp t = 2 * Real.cosh t := by
      rw [Real.cosh_eq]; ring
    rw [hc, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc Real.cosh t ^ n ≤ Real.exp (t ^ 2 / 2) ^ n :=
          pow_le_pow_left₀ (by rw [Real.cosh_eq]; positivity) (Real.cosh_le_exp_half_sq t) n
      _ = Real.exp ((n : ℝ) * (t ^ 2 / 2)) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (lam ^ 2 / 2) := by
          rw [show (n : ℝ) * (t ^ 2 / 2) = (n : ℝ) * t ^ 2 / 2 by ring, hnt]
  have hchain : (#F : ℝ) * Real.exp (lam ^ 2) ≤ 2 ^ n * Real.exp (lam ^ 2 / 2) := by
    calc (#F : ℝ) * Real.exp (lam ^ 2) ≤ ∑ S ∈ F, Real.exp (t * (2 * (#S : ℝ) - n)) := hlow
      _ ≤ ∑ S ∈ (univ : Finset (Fin n)).powerset,
            Real.exp (t * (2 * (#S : ℝ) - n)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun S _ _ => (Real.exp_pos _).le
          rw [hFdef]; exact filter_subset _ _
      _ = (Real.exp (-t) + Real.exp t) ^ n := htot
      _ ≤ 2 ^ n * Real.exp (lam ^ 2 / 2) := hcosh
  have hpos : 0 < Real.exp (lam ^ 2 / 2) := Real.exp_pos _
  have hexp : Real.exp (lam ^ 2) = Real.exp (lam ^ 2 / 2) * Real.exp (lam ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hkey : (#F : ℝ) * Real.exp (lam ^ 2 / 2) ≤ 2 ^ n := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc (#F : ℝ) * Real.exp (lam ^ 2 / 2) * Real.exp (lam ^ 2 / 2)
        = (#F : ℝ) * Real.exp (lam ^ 2) := by rw [hexp]; ring
      _ ≤ 2 ^ n * Real.exp (lam ^ 2 / 2) := hchain
  rw [show -(lam ^ 2) / 2 = -(lam ^ 2 / 2) by ring, Real.exp_neg, ← div_eq_mul_inv,
    le_div_iff₀ hpos]
  exact hkey

/-- **The two-sided Chernoff bound** (Zhao, Corollary 5.0.3).

`#{S : λ√n ≤ |2 #S - n|} ≤ 2 * (2 ^ n * exp (-λ² / 2))`, i.e.
`P(|Sₙ| ≥ λ√n) ≤ 2 exp(-λ²/2)` after dividing by `2 ^ n`.

The lower tail is the upper tail of the complement: `S ↦ Sᶜ` sends `2 #S - n` to its
negation, so the two tails have exactly equal cardinality and one application of
`PMC.card_filter_sign_sum_le` suffices. -/
theorem card_filter_abs_sign_sum_le {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam) :
    (#((univ : Finset (Fin n)).powerset.filter
        fun S => lam * Real.sqrt n ≤ |2 * (#S : ℝ) - n|) : ℝ)
      ≤ 2 * (2 ^ n * Real.exp (-(lam ^ 2) / 2)) := by
  classical
  set P : Finset (Finset (Fin n)) := (univ : Finset (Fin n)).powerset.filter
      (fun S => lam * Real.sqrt n ≤ 2 * (#S : ℝ) - n) with hPdef
  set N : Finset (Finset (Fin n)) := (univ : Finset (Fin n)).powerset.filter
      (fun S => 2 * (#S : ℝ) - n ≤ -(lam * Real.sqrt n)) with hNdef
  -- `S ↦ Sᶜ` matches the lower tail with the upper tail.
  have hcompl : ∀ S : Finset (Fin n), 2 * ((#Sᶜ : ℕ) : ℝ) - n = -(2 * (#S : ℝ) - n) := by
    intro S
    have h : (#Sᶜ : ℕ) = n - #S := by
      rw [card_compl, Fintype.card_fin]
    have hle : #S ≤ n := by
      have := card_le_univ S
      rwa [Fintype.card_fin] at this
    rw [h, Nat.cast_sub hle]
    ring
  have hNP : #N = #P := by
    refine Finset.card_nbij' (fun S => Sᶜ) (fun S => Sᶜ) ?_ ?_ ?_ ?_
    · intro S hS
      rw [hNdef, mem_coe, mem_filter] at hS
      rw [hPdef, mem_coe, mem_filter]
      refine ⟨mem_powerset.mpr (subset_univ _), ?_⟩
      rw [hcompl S]
      linarith [hS.2]
    · intro S hS
      rw [hPdef, mem_coe, mem_filter] at hS
      rw [hNdef, mem_coe, mem_filter]
      refine ⟨mem_powerset.mpr (subset_univ _), ?_⟩
      rw [hcompl S]
      linarith [hS.2]
    · intro S _
      exact compl_compl S
    · intro S _
      exact compl_compl S
  -- The two-sided event is covered by the two tails.
  have hsub : (univ : Finset (Fin n)).powerset.filter
      (fun S => lam * Real.sqrt n ≤ |2 * (#S : ℝ) - n|) ⊆ P ∪ N := by
    intro S hS
    rw [mem_filter] at hS
    rw [mem_union, hPdef, hNdef, mem_filter, mem_filter]
    rcases le_abs.mp hS.2 with h | h
    · exact Or.inl ⟨hS.1, h⟩
    · exact Or.inr ⟨hS.1, by linarith⟩
  have hchern := card_filter_sign_sum_le hn hlam
  rw [← hPdef] at hchern
  calc (#((univ : Finset (Fin n)).powerset.filter
        fun S => lam * Real.sqrt n ≤ |2 * (#S : ℝ) - n|) : ℝ)
      ≤ ((#(P ∪ N) : ℕ) : ℝ) := by
        exact_mod_cast Nat.cast_le.mpr (card_le_card hsub)
    _ ≤ ((#P : ℕ) : ℝ) + ((#N : ℕ) : ℝ) := by
        exact_mod_cast Nat.cast_le.mpr (card_union_le P N)
    _ = 2 * ((#P : ℕ) : ℝ) := by rw [hNP]; ring
    _ ≤ 2 * (2 ^ n * Real.exp (-(lam ^ 2) / 2)) := by linarith [hchern]

end PMC
