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
variable {δ : Type*} [Fintype δ] [DecidableEq δ]

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

/-- **The Gibbs variational principle.** For a distribution `P` supported in `T` and any
"energy" `a`,

    H(P) + E_P[a] ≤ log ∑_{t ∈ T} exp (a t),

with equality at the Gibbs measure `P ∝ exp a`. Taking `a = 0` recovers
`PMC.sum_negMulLog_le_log_card`; the case that matters below gives one point of `T` a
weight of `2^d` and the rest a weight of `1`, which is how `i(K_{d,d}) = 2^{d+1} - 1`
appears in Kahn–Zhao.

Like the `a = 0` case this is Gibbs' inequality against an explicit comparison
distribution, here `exp (a c) / Z` on `T`. -/
theorem sum_negMulLog_add_le_log_sum_exp {P : γ → ℝ} (hP0 : ∀ c, 0 ≤ P c)
    (hPsum : ∑ c, P c = 1) (a : γ → ℝ) {T : Finset γ} (hsupp : ∀ c, c ∉ T → P c = 0) :
    ∑ c, Real.negMulLog (P c) + ∑ c, P c * a c ≤ Real.log (∑ t ∈ T, Real.exp (a t)) := by
  classical
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hT
    have hzero : ∑ c, P c = 0 :=
      Finset.sum_eq_zero fun c _ => hsupp c (by rw [hT]; exact Finset.notMem_empty c)
    rw [hzero] at hPsum
    exact zero_ne_one hPsum
  set Z := ∑ t ∈ T, Real.exp (a t) with hZ
  have hZpos : 0 < Z := Finset.sum_pos (fun t _ => Real.exp_pos (a t)) hTne
  have hQsum : ∑ c : γ, (if c ∈ T then Real.exp (a c) / Z else 0) = 1 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div, ← hZ,
      div_self (ne_of_gt hZpos)]
  have hgibbs := sum_mul_log_div_le P (fun c => if c ∈ T then Real.exp (a c) / Z else 0) hP0
    (fun c => by by_cases hc : c ∈ T <;> simp only [if_pos, if_neg, hc] <;> positivity)
    (fun c hc => by
      have hcT : c ∈ T := by
        by_contra hcon
        exact hc (hsupp c hcon)
      simp only [if_pos hcT]
      positivity)
    hPsum (le_of_eq hQsum)
  have hterm : ∀ c : γ, P c * Real.log ((if c ∈ T then Real.exp (a c) / Z else 0) / P c)
      = Real.negMulLog (P c) + P c * a c - P c * Real.log Z := by
    intro c
    rcases eq_or_lt_of_le (hP0 c) with h | h
    · rw [← h]
      simp [Real.negMulLog]
    · have hcT : c ∈ T := by
        by_contra hcon
        exact (ne_of_gt h) (hsupp c hcon)
      rw [if_pos hcT, Real.log_div (by positivity) (ne_of_gt h),
        Real.log_div (ne_of_gt (Real.exp_pos (a c))) (ne_of_gt hZpos), Real.log_exp,
        Real.negMulLog]
      ring
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, hPsum, one_mul] at hgibbs
  linarith

/-- The mean of a function of `Y` read off `Y`'s distribution. The bridge between the
`PMC.wmean` the applications average over and the `PMC.wdist` the entropy bounds produce. -/
lemma wmean_comp_eq_sum_wdist (w : Ω → ℝ) (Y : Ω → γ) (f : γ → ℝ) :
    wmean w (fun ω => f (Y ω)) = ∑ c, wdist w Y c * f c := by
  classical
  rw [wmean, ← Finset.sum_fiberwise_of_maps_to (fun ω (_ : ω ∈ (univ : Finset Ω)) =>
    mem_univ (Y ω)) (fun ω => w ω * f (Y ω))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [wdist, wprob, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω hω => ?_
  rw [(mem_filter.mp hω).2]

/-- **The Gibbs variational principle for a random variable.** If `Z` takes values in `T`,

    H(Z) + E[a(Z)] ≤ log ∑_{t ∈ T} exp (a t).

`PMC.sum_negMulLog_add_le_log_sum_exp` transported to `wentropy`/`wmean`; the support
hypothesis becomes the (much easier to supply) pointwise `Z ω ∈ T`. -/
theorem wentropy_add_wmean_le_log_sum_exp {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hsum : ∑ ω, w ω = 1) (Z : Ω → γ) (a : γ → ℝ) {T : Finset γ} (hZ : ∀ ω, Z ω ∈ T) :
    wentropy w Z + wmean w (fun ω => a (Z ω)) ≤ Real.log (∑ t ∈ T, Real.exp (a t)) := by
  classical
  have hsupp : ∀ c, c ∉ T → wdist w Z c = 0 := by
    intro c hc
    rw [wdist, wprob, Finset.filter_false_of_mem, Finset.sum_empty]
    intro ω _ hω
    exact hc (hω ▸ hZ ω)
  have hkey := sum_negMulLog_add_le_log_sum_exp (P := wdist w Z)
    (fun c => wdist_nonneg hw Z c) (by rw [sum_wdist, hsum]) a hsupp
  rw [wmean_comp_eq_sum_wdist]
  exact hkey

/-- **Conditional entropy depends only on the fibres of the conditioning variable.** If `Z`
and `Z'` determine each other along their ranges, then `H(Y | Z) = H(Y | Z')`.

Both `H(Z)` and `H(Z, Y)` are invariant under such a relabelling (`PMC.wentropy_congr`), and
the chain rule writes `H(Y | Z)` as their difference. Needed whenever a conditioning variable
is re-presented in a different type — for instance a tuple `X_S` read as a function on an
enumeration `Fin d → β` of `S` rather than as a mask. -/
theorem wcondEntropy_congr_left {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (Z : Ω → β) (Z' : Ω → δ)
    (Y : Ω → γ) (g : β → δ) (h : δ → β)
    (hg : ∀ ω, g (Z ω) = Z' ω) (hh : ∀ ω, h (Z' ω) = Z ω) :
    wcondEntropy w Z Y = wcondEntropy w Z' Y := by
  have h1 := wentropy_chain hw Z Y
  have h2 := wentropy_chain hw Z' Y
  have h3 : wentropy w Z = wentropy w Z' :=
    wentropy_congr w Z Z' g h (fun ω => (hg ω).symm) (fun ω => (hh ω).symm)
  have h4 : wentropy w (fun ω => (Z ω, Y ω)) = wentropy w (fun ω => (Z' ω, Y ω)) :=
    wentropy_congr w _ _ (fun q => (g q.1, q.2)) (fun q => (h q.1, q.2))
      (fun ω => by rw [Prod.ext_iff]; exact ⟨(hg ω).symm, rfl⟩)
      (fun ω => by rw [Prod.ext_iff]; exact ⟨(hh ω).symm, rfl⟩)
  linarith

/-! ### Conditional independence

The step §10.3's proofs use and this library lacked: **if the conditional distribution of `X`
given `(Y, Z)` depends only on `Y`, then `H(X | Y, Z) = H(X | Y)`.** The notes invoke it as
"[cond indep]" when computing the entropy of a random walk or of two conditionally
independent copies.

The proof is a regrouping, not an inequality: the conditioning fibres of `(Y, Z)` above a
fixed `y` all carry the *same* conditional distribution, so their weights collapse onto the
marginal of `Y` — which is `PMC.sum_wdist_pair_right`. -/

/-- **Conditional independence removes a variable from the conditioning.** If the conditional
distribution of `X` given `(Y, Z)` agrees with the one given `Y` alone on every fibre of
positive weight, the two conditional entropies coincide. -/
theorem wcondEntropy_pair_eq_of_condIndep {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (X : Ω → δ) (Y : Ω → β) (Z : Ω → γ)
    (h : ∀ (b : β) (c : γ), 0 < wdist w (fun ω => (Y ω, Z ω)) (b, c) →
      ∀ d : δ, wcondDist w (fun ω => (Y ω, Z ω)) X (b, c) d = wcondDist w Y X b d) :
    wcondEntropy w (fun ω => (Y ω, Z ω)) X = wcondEntropy w Y X := by
  classical
  simp only [wcondEntropy]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hterm : ∀ c : γ, wdist w (fun ω => (Y ω, Z ω)) (b, c)
        * ∑ d, Real.negMulLog (wcondDist w (fun ω => (Y ω, Z ω)) X (b, c) d)
      = wdist w (fun ω => (Y ω, Z ω)) (b, c)
        * ∑ d, Real.negMulLog (wcondDist w Y X b d) := by
    intro c
    by_cases hpos : 0 < wdist w (fun ω => (Y ω, Z ω)) (b, c)
    · refine congrArg (fun t => wdist w (fun ω => (Y ω, Z ω)) (b, c) * t) ?_
      exact Finset.sum_congr rfl fun d _ => by rw [h b c hpos d]
    · have hz : wdist w (fun ω => (Y ω, Z ω)) (b, c) = 0 :=
        le_antisymm (not_lt.mp hpos) (wdist_nonneg hw _ _)
      rw [hz, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_mul, sum_wdist_pair_right]

end CondSupport

end PMC
