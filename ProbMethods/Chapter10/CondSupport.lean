import ProbMethods.Chapter10.Entropy

/-!
# Conditional entropy is at most the expected log of the conditional support

§10.1's `PMC.wentropy_le_log_card_image` bounds `H(Z)` by the log of the number of values `Z`
attains. Brégman–Minc (§10.2) needs the *conditional* form: if, whenever `X ω = b`, the value
`Y ω` lies in a set `T b`, then

    H(Y | X) ≤ ∑_b P(X = b) · log #(T b),

the expectation of the log of the conditionally available range. In the application `T b` is
the set of columns still free for a row once the earlier rows are known, and this is the step
that turns entropy back into the counting the argument is really about.

Both bounds come from the same distribution-level fact, which is isolated here as
`PMC.sum_negMulLog_le_log_card`: a probability vector supported in a finite set `T` has
entropy at most `log #T`. Stating it for a bare distribution rather than a random variable is
what makes it reusable for conditional distributions, where the "random variable" is
`PMC.wcondDist` and there is no underlying map to speak of.
-/

open Finset

namespace PMC

section CondSupport

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {β : Type*} [Fintype β] [DecidableEq β]
variable {γ : Type*} [Fintype γ] [DecidableEq γ]

/-- **A distribution supported in `T` has entropy at most `log #T`.** Gibbs' inequality
against the uniform distribution on `T`. -/
theorem sum_negMulLog_le_log_card {P : γ → ℝ} (hP0 : ∀ c, 0 ≤ P c) (hPsum : ∑ c, P c = 1)
    {T : Finset γ} (hsupp : ∀ c, c ∉ T → P c = 0) :
    ∑ c, Real.negMulLog (P c) ≤ Real.log #T := by
  classical
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hT
    have hzero : ∑ c, P c = 0 :=
      Finset.sum_eq_zero fun c _ => hsupp c (by rw [hT]; exact Finset.notMem_empty c)
    rw [hzero] at hPsum
    exact zero_ne_one hPsum
  have hm : (0 : ℝ) < #T := by exact_mod_cast Finset.card_pos.mpr hTne
  have hQsum : ∑ c : γ, (if c ∈ T then 1 / (#T : ℝ) else 0) = 1 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one_div,
      div_self (ne_of_gt hm)]
  have hgibbs := sum_mul_log_div_le P (fun c => if c ∈ T then 1 / (#T : ℝ) else 0) hP0
    (fun c => by by_cases hc : c ∈ T <;> simp only [if_pos, if_neg, hc] <;> positivity)
    (fun c hc => by
      have hcT : c ∈ T := by
        by_contra hcon
        exact hc (hsupp c hcon)
      simp only [if_pos hcT]
      positivity)
    hPsum (le_of_eq hQsum)
  have hterm : ∀ c : γ, P c * Real.log ((if c ∈ T then 1 / (#T : ℝ) else 0) / P c)
      = Real.negMulLog (P c) - P c * Real.log #T := by
    intro c
    rcases eq_or_lt_of_le (hP0 c) with h | h
    · rw [← h]
      simp [Real.negMulLog]
    · have hcT : c ∈ T := by
        by_contra hcon
        exact (ne_of_gt h) (hsupp c hcon)
      rw [if_pos hcT, Real.log_div (by positivity) (ne_of_gt h), one_div, Real.log_inv,
        Real.negMulLog]
      ring
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hPsum, one_mul] at hgibbs
  linarith

/-- **Conditional entropy is at most the expected log of the conditional support.**

If `Y ω` always lies in `T (X ω)`, then `H(Y | X) ≤ ∑_b P(X = b) log #(T b)`. The fibres
where `P(X = b) = 0` contribute nothing to either side, so no side condition is needed. -/
theorem wcondEntropy_le_sum_log_card {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (X : Ω → β) (Y : Ω → γ) (T : β → Finset γ) (hT : ∀ ω, Y ω ∈ T (X ω)) :
    wcondEntropy w X Y ≤ ∑ b, wdist w X b * Real.log #(T b) := by
  classical
  rw [wcondEntropy]
  refine Finset.sum_le_sum fun b _ => ?_
  rcases eq_or_lt_of_le (wdist_nonneg hw X b) with h | h
  · rw [← h, zero_mul, zero_mul]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt h)
  refine sum_negMulLog_le_log_card (fun c => wcondDist_nonneg hw X Y b c) ?_ ?_
  · simp only [wcondDist]
    rw [← Finset.sum_div, sum_wdist_pair_right, div_self (ne_of_gt h)]
  · intro c hc
    have hzero : wdist w (fun ω => (X ω, Y ω)) (b, c) = 0 := by
      rw [wdist, wprob, Finset.filter_false_of_mem, Finset.sum_empty]
      intro ω _ hω
      have hX : X ω = b := congrArg Prod.fst hω
      have hY : Y ω = c := congrArg Prod.snd hω
      have := hT ω
      rw [hX, hY] at this
      exact hc this
    rw [wcondDist, hzero, zero_div]

end CondSupport

end PMC
