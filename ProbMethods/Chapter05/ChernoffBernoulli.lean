import ProbMethods.Weighted
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# §5.0.7 — Chernoff for Bernoulli variables with differing probabilities

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 5.0.7.

`PMC.card_filter_sign_sum_le` (Theorem 5.0.1) handles `±1` variables that are uniform, so
the sample space is counting-uniform. Here each coordinate `i` survives with its own
probability `p i`, so the weight is `PMC.pweight` rather than a count — and the whole point
of `pweight` was that `Finset.prod_add` never needed the factors to be equal.

The upper tail: with `μ = ∑ p i`,

`∑_{#S ≥ (1+ε) μ} pweight p S ≤ exp (-μ ((1+ε) log(1+ε) - ε))`.

The proof is the moment generating function again, but the optimisation is now exact rather
than approximate: `t = log (1+ε)` is the true minimiser, which is where the odd-looking
`(1+ε) log(1+ε) - ε` comes from.
-/

open Finset

namespace PMC

section ChernoffBernoulli

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The moment generating function for differing probabilities.**

`Finset.prod_add` with the two factors `p i · e^t` and `1 - p i`. Nothing here needs the
`p i` to agree, which is exactly why `PMC.pweight` was worth defining. -/
theorem sum_pweight_mul_exp (p : α → ℝ) (t : ℝ) :
    ∑ S ∈ (univ : Finset α).powerset, pweight p S * Real.exp (t * #S)
      = ∏ i : α, (p i * Real.exp t + (1 - p i)) := by
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [pweight, Finset.prod_mul_distrib, Finset.prod_const,
    show Real.exp (t * #S) = Real.exp t ^ #S from by rw [mul_comm, Real.exp_nat_mul]]
  ring

/-- **Theorem 5.0.7 — the upper tail.**

Each coordinate survives independently with its own probability `p i`; with `μ = ∑ p i`,
the weight of the subsets of size at least `(1 + ε) μ` is at most
`exp (-μ ((1+ε) log(1+ε) - ε))`.

Stated with the exact exponent the notes give, not an `O(·)` estimate: `t = log (1 + ε)` is
the true minimiser of the moment generating function bound, so no slack is introduced. -/
theorem sum_pweight_upper_tail (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∑ S ∈ (univ : Finset α).powerset.filter
        (fun S => (1 + ε) * (∑ i, p i) ≤ #S), pweight p S
      ≤ Real.exp (-(∑ i, p i) * ((1 + ε) * Real.log (1 + ε) - ε)) := by
  classical
  set μ := ∑ i, p i with hμdef
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg fun i _ => hp0 i
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  set t := Real.log (1 + ε) with htdef
  have ht0 : 0 ≤ t := Real.log_nonneg (by linarith)
  have hexpt : Real.exp t = 1 + ε := Real.exp_log h1ε
  -- the moment generating function, bounded by `1 + x ≤ exp x` coordinatewise
  have hmgf : ∑ S ∈ (univ : Finset α).powerset, pweight p S * Real.exp (t * #S)
      ≤ Real.exp (μ * (Real.exp t - 1)) := by
    rw [sum_pweight_mul_exp]
    have hfac : ∀ i : α, p i * Real.exp t + (1 - p i)
        ≤ Real.exp (p i * (Real.exp t - 1)) := by
      intro i
      have h := Real.add_one_le_exp (p i * (Real.exp t - 1))
      nlinarith [h]
    have hnn : ∀ i : α, 0 ≤ p i * Real.exp t + (1 - p i) := by
      intro i
      have h1 : (1 : ℝ) ≤ Real.exp t := by rw [hexpt]; linarith
      nlinarith [hp0 i, hp1 i]
    calc ∏ i : α, (p i * Real.exp t + (1 - p i))
        ≤ ∏ i : α, Real.exp (p i * (Real.exp t - 1)) :=
          Finset.prod_le_prod (fun i _ => hnn i) (fun i _ => hfac i)
      _ = Real.exp (∑ i, p i * (Real.exp t - 1)) := (Real.exp_sum ..).symm
      _ = Real.exp (μ * (Real.exp t - 1)) := by rw [← Finset.sum_mul, hμdef]
  -- Markov: every qualifying subset contributes at least `exp (t (1+ε) μ)`
  have hmark : (∑ S ∈ (univ : Finset α).powerset.filter
        (fun S => (1 + ε) * μ ≤ #S), pweight p S) * Real.exp (t * ((1 + ε) * μ))
      ≤ ∑ S ∈ (univ : Finset α).powerset, pweight p S * Real.exp (t * #S) := by
    rw [Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
    · intro S hS
      rw [mem_filter] at hS
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [hS.2, ht0])) (pweight_nonneg hp0 hp1 S)
    · intro S _ _
      exact mul_nonneg (pweight_nonneg hp0 hp1 S) (Real.exp_pos _).le
  -- combine and read off the exponent
  have hfin : (∑ S ∈ (univ : Finset α).powerset.filter
        (fun S => (1 + ε) * μ ≤ #S), pweight p S) * Real.exp (t * ((1 + ε) * μ))
      ≤ Real.exp (μ * ε) := by
    have h := le_trans hmark hmgf
    rwa [hexpt, show (1 : ℝ) + ε - 1 = ε from by ring] at h
  rw [← le_div_iff₀ (Real.exp_pos (t * ((1 + ε) * μ)))] at hfin
  refine hfin.trans (le_of_eq ?_)
  rw [← Real.exp_sub]
  congr 1
  rw [htdef]
  ring

end ChernoffBernoulli

end PMC
