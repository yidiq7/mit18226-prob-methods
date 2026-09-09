import ProbMethods.Chapter09.Hoeffding
import ProbMethods.Chapter05.ChernoffBernoulli

/-!
# §5.0 — Hoeffding's bound for a sum of Bernoullis (Corollary 5.0.6)

Zhao, *Probabilistic Methods in Combinatorics*, Corollary 5.0.6: if `X` is a sum of `n`
independent Bernoulli variables with means `p i` and `μ = ∑ p i`, then for `λ > 0`

    P(X ≥ μ + λ√n) ≤ e^{-λ²/2}   and   P(X ≤ μ - λ√n) ≤ e^{-λ²/2}.

What is proved here is the sharper `e^{-2t²/n}` at deviation `t` (`PMC.sum_pweight_ge_le`), of
which the notes' form is the case `t = λ√n` — `e^{-2λ²} ≤ e^{-λ²/2}`. Stating the sharp version
and deducing the notes' is the same choice §5.0 already makes for Theorem 5.0.1.

The engine is Hoeffding's lemma at a *single* Bernoulli
(`PMC.bernoulli_mgf_le`: `p e^λ + (1-p) ≤ exp(λp + λ²/8)`), which is `PMC.wmean_exp_le_of_mem_Icc`
on the two-point space. Multiplying those bounds over the coordinates is
`PMC.sum_pweight_mul_exp`, the exact moment generating function from §5.0.7, so the whole
argument is: exact MGF, coordinatewise Hoeffding, Markov, optimise `λ = 4t/n`.

Theorem 5.0.7 in the same chapter is the *multiplicative* form, `exp(-μ((1+ε)log(1+ε) - ε))`,
which is sharper for small `μ` and weaker for large deviations; the two are complementary and
the notes give both.
-/

open Finset

namespace PMC

section HoeffdingBernoulli

/-- **Hoeffding's lemma for a single Bernoulli**: `p e^λ + (1-p) ≤ exp(λ p + λ²/8)`.

`PMC.wmean_exp_le_of_mem_Icc` on `Bool`, at the weight `(1-p, p)` and the centred variable
`(-p, 1-p)`, whose range has length `1`. -/
theorem bernoulli_mgf_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (lam : ℝ) :
    p * Real.exp lam + (1 - p) ≤ Real.exp (lam * p + lam ^ 2 / 8) := by
  classical
  set w : Bool → ℝ := fun e => cond e p (1 - p) with hwdef
  set Z : Bool → ℝ := fun e => cond e (1 - p) (-p) with hZdef
  have hwnn : ∀ e, 0 ≤ w e := by
    intro e
    cases e <;> simp only [hwdef, cond_true, cond_false] <;> linarith
  have hwsum : ∑ e, w e = 1 := by
    rw [Fintype.sum_bool]
    simp only [hwdef, cond_true, cond_false]
    ring
  have hZmem : ∀ e, Z e ∈ Set.Icc (-p) (1 - p) := by
    intro e
    cases e <;> simp only [hZdef, cond_true, cond_false, Set.mem_Icc] <;>
      exact ⟨by linarith, by linarith⟩
  have hZmean : wmean w Z = 0 := by
    rw [wmean, Fintype.sum_bool]
    simp only [hwdef, hZdef, cond_true, cond_false]
    ring
  have h := wmean_exp_le_of_mem_Icc hwnn hwsum Z hZmem hZmean lam
  rw [wmean, Fintype.sum_bool] at h
  simp only [hwdef, hZdef, cond_true, cond_false] at h
  -- `h : p * exp (lam * (1-p)) + (1-p) * exp (lam * (-p)) ≤ exp (lam² ((1-p) - (-p))²/8)`
  have e1 : Real.exp (lam * (1 - p)) * Real.exp (lam * p) = Real.exp lam := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (lam * (-p)) * Real.exp (lam * p) = 1 := by
    rw [← Real.exp_add, show lam * (-p) + lam * p = 0 from by ring, Real.exp_zero]
  have hlen : lam ^ 2 * ((1 - p) - (-p)) ^ 2 / 8 = lam ^ 2 / 8 := by
    rw [show (1 - p) - (-p) = 1 from by ring]
    ring
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (lam * p)).le
  rw [hlen, ← Real.exp_add] at hmul
  calc p * Real.exp lam + (1 - p)
      = (p * Real.exp (lam * (1 - p)) + (1 - p) * Real.exp (lam * (-p)))
          * Real.exp (lam * p) := by
        rw [add_mul, mul_assoc, mul_assoc, e1, e2]
        ring
    _ ≤ Real.exp (lam ^ 2 / 8 + lam * p) := hmul
    _ = Real.exp (lam * p + lam ^ 2 / 8) := by rw [add_comm]


section Sum

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The moment generating function of a sum of independent Bernoullis.**

`PMC.sum_pweight_mul_exp` computes it exactly as `∏ (pᵢe^λ + 1 - pᵢ)`; bounding each factor by
`PMC.bernoulli_mgf_le` gives `exp(λμ + λ²n/8)`. -/
theorem sum_pweight_exp_le (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (lam : ℝ) :
    ∑ S ∈ (univ : Finset α).powerset, pweight p S * Real.exp (lam * #S)
      ≤ Real.exp (lam * (∑ i, p i) + lam ^ 2 * Fintype.card α / 8) := by
  rw [sum_pweight_mul_exp]
  calc ∏ i : α, (p i * Real.exp lam + (1 - p i))
      ≤ ∏ i : α, Real.exp (lam * p i + lam ^ 2 / 8) := by
        refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => bernoulli_mgf_le (hp0 i) (hp1 i) lam)
        have h1 : (0 : ℝ) ≤ p i * Real.exp lam := mul_nonneg (hp0 i) (Real.exp_pos lam).le
        have h2 : (0 : ℝ) ≤ 1 - p i := by linarith [hp1 i]
        linarith
    _ = Real.exp (∑ _i : α, (lam * p _i + lam ^ 2 / 8)) := (Real.exp_sum ..).symm
    _ = Real.exp (lam * (∑ i, p i) + lam ^ 2 * Fintype.card α / 8) := by
        congr 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_univ, nsmul_eq_mul]
        ring

/-- **Corollary 5.0.6, upper tail**, in the sharp form: for a sum of independent Bernoullis
with mean `μ`,

    P(X ≥ μ + t) ≤ exp(-2t²/n).

Markov applied to the moment generating function at the optimal `λ = 4t/n`. -/
theorem sum_pweight_ge_le (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) {t : ℝ}
    (ht : 0 < t) (hn : 0 < Fintype.card α) :
    ∑ S ∈ (univ : Finset α).powerset.filter (fun S => (∑ i, p i) + t ≤ #S), pweight p S
      ≤ Real.exp (-(2 * t ^ 2) / Fintype.card α) := by
  classical
  set n : ℕ := Fintype.card α with hndef
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set μ : ℝ := ∑ i, p i with hμ
  set lam : ℝ := 4 * t / n with hlam
  have hlampos : 0 < lam := by
    rw [hlam]
    positivity
  -- Markov at `λ`
  have hmark : (∑ S ∈ (univ : Finset α).powerset.filter (fun S => μ + t ≤ #S), pweight p S)
      * Real.exp (lam * (μ + t))
      ≤ ∑ S ∈ (univ : Finset α).powerset, pweight p S * Real.exp (lam * #S) := by
    rw [Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
    · intro S hS
      rw [mem_filter] at hS
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pweight_nonneg hp0 hp1 S)
      exact mul_le_mul_of_nonneg_left hS.2 (le_of_lt hlampos)
    · intro S _ _
      exact mul_nonneg (pweight_nonneg hp0 hp1 S) (Real.exp_pos _).le
  have hmgf := sum_pweight_exp_le p hp0 hp1 lam
  rw [← hμ, ← hndef] at hmgf
  -- the exponent collapses to `-2t²/n`
  have hexp : lam * μ + lam ^ 2 * n / 8 - lam * (μ + t) = -(2 * t ^ 2) / n := by
    rw [hlam]
    field_simp
    ring
  have hpos : (0 : ℝ) < Real.exp (lam * (μ + t)) := Real.exp_pos _
  calc (∑ S ∈ (univ : Finset α).powerset.filter (fun S => μ + t ≤ #S), pweight p S)
      ≤ Real.exp (lam * μ + lam ^ 2 * n / 8) / Real.exp (lam * (μ + t)) := by
        rw [le_div_iff₀ hpos]
        exact le_trans hmark hmgf
    _ = Real.exp (-(2 * t ^ 2) / n) := by
        rw [← Real.exp_sub, hexp]

/-- **Corollary 5.0.6**, as the notes write it: `P(X ≥ μ + λ√n) ≤ e^{-λ²/2}`.

The sharp form gives `e^{-2λ²}`, and `2λ² ≥ λ²/2`. -/
theorem sum_pweight_ge_sqrt_le (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) {lam : ℝ}
    (hlam : 0 < lam) (hn : 0 < Fintype.card α) :
    ∑ S ∈ (univ : Finset α).powerset.filter
        (fun S => (∑ i, p i) + lam * Real.sqrt (Fintype.card α) ≤ #S), pweight p S
      ≤ Real.exp (-(lam ^ 2) / 2) := by
  have hnR : (0 : ℝ) < Fintype.card α := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (Fintype.card α) := Real.sqrt_pos.mpr hnR
  have ht : 0 < lam * Real.sqrt (Fintype.card α) := by positivity
  have hmain := sum_pweight_ge_le p hp0 hp1 ht hn
  refine le_trans hmain (Real.exp_le_exp.mpr ?_)
  have hsq : (lam * Real.sqrt (Fintype.card α)) ^ 2 = lam ^ 2 * Fintype.card α := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hnR)]
  rw [hsq]
  rw [div_le_div_iff₀ hnR (by norm_num : (0:ℝ) < 2)]
  nlinarith [sq_nonneg lam, hnR]


/-- Complementation exchanges `p` for `1 - p`. -/
lemma pweight_compl (p : α → ℝ) (S : Finset α) :
    pweight (fun i => 1 - p i) (Sᶜ) = pweight p S := by
  classical
  have h1 : (univ : Finset α) \ Sᶜ = S := by
    ext i
    simp
  have h2 : (Sᶜ : Finset α) = (univ : Finset α) \ S := by
    ext i
    simp
  have h3 : ∏ i ∈ S, (1 - (1 - p i)) = ∏ i ∈ S, p i :=
    Finset.prod_congr rfl fun i _ => by ring
  rw [pweight, pweight, h1, h2, h3, mul_comm]

/-- **Corollary 5.0.6, lower tail**: `P(X ≤ μ - t) ≤ exp(-2t²/n)`.

By complementation: `#S ≤ μ - t` says the complement is at least `t` *above* its mean
`n - μ`, and `PMC.pweight_compl` carries the weight across. -/
theorem sum_pweight_le_le (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) {t : ℝ}
    (ht : 0 < t) (hn : 0 < Fintype.card α) :
    ∑ S ∈ (univ : Finset α).powerset.filter (fun S => (#S : ℝ) ≤ (∑ i, p i) - t), pweight p S
      ≤ Real.exp (-(2 * t ^ 2) / Fintype.card α) := by
  classical
  have hq0 : ∀ i, (0 : ℝ) ≤ 1 - p i := fun i => by linarith [hp1 i]
  have hq1 : ∀ i, (1 : ℝ) - p i ≤ 1 := fun i => by linarith [hp0 i]
  have hmain := sum_pweight_ge_le (fun i => 1 - p i) hq0 hq1 ht hn
  have hqsum : ∑ i, (1 - p i) = (Fintype.card α : ℝ) - ∑ i, p i := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, card_univ, nsmul_eq_mul, mul_one]
  rw [hqsum] at hmain
  refine le_trans (le_of_eq ?_) hmain
  -- the complement is a bijection between the two filtered families
  refine Finset.sum_nbij' (fun S => Sᶜ) (fun S => Sᶜ) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_filter, mem_powerset] at hS
    rw [mem_filter, mem_powerset]
    refine ⟨subset_univ _, ?_⟩
    have hcard : (#(Sᶜ) : ℝ) = (Fintype.card α : ℝ) - #S := by
      rw [Finset.card_compl]
      have : #S ≤ Fintype.card α := by
        rw [← card_univ]
        exact card_le_card (subset_univ _)
      push_cast [this]
      ring
    rw [hcard]
    linarith [hS.2]
  · intro S hS
    rw [mem_filter, mem_powerset] at hS
    rw [mem_filter, mem_powerset]
    refine ⟨subset_univ _, ?_⟩
    have hcard : (#(Sᶜ) : ℝ) = (Fintype.card α : ℝ) - #S := by
      rw [Finset.card_compl]
      have : #S ≤ Fintype.card α := by
        rw [← card_univ]
        exact card_le_card (subset_univ _)
      push_cast [this]
      ring
    rw [hcard]
    linarith [hS.2]
  · intro S _
    simp
  · intro S _
    simp
  · intro S _
    exact (pweight_compl p S).symm

end Sum

end HoeffdingBernoulli

end PMC
