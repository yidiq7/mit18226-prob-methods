import ProbMethods.Weighted
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.BigOperators.Field

/-!
# §10.1 — Entropy of a finite random variable

Zhao, *Probabilistic Methods in Combinatorics*, Chapter 10.

Mathlib has `Real.negMulLog` with its concavity, and binary entropy, but no entropy of a
random variable and none of the inequalities Chapter 10 is built on. This file supplies
that layer inside the finite weighted framework: a random variable is a function
`X : Ω → β` on the weighted sample space, its distribution is `PMC.wdist`, and its entropy
`PMC.wentropy` is `∑ b, negMulLog (P (X = b))`, measured in nats.

Everything here rests on one inequality, `PMC.sum_mul_log_div_le` — Gibbs' inequality,
proved from `Real.log_le_sub_one_of_pos`. Note the hypothesis `hac`: Mathlib's convention
`log 0 = 0` makes the naive statement of Gibbs' inequality **false** (take `P = (½,½)` and
`Q = (1,0)`), so absolute continuity has to be assumed. In both applications below it is
automatic, because a marginal is positive wherever the joint distribution is.
-/

open Finset

namespace PMC

section Entropy

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Gibbs' inequality**: relative entropy is nonnegative.

`hac` is absolute continuity — `Q` cannot vanish where `P` does not. It is genuinely
needed: under Mathlib's `log 0 = 0` convention the inequality fails without it. -/
theorem sum_mul_log_div_le {β : Type*} [Fintype β] (P Q : β → ℝ)
    (hP0 : ∀ b, 0 ≤ P b) (hQ0 : ∀ b, 0 ≤ Q b) (hac : ∀ b, P b ≠ 0 → Q b ≠ 0)
    (hP : ∑ b, P b = 1) (hQ : ∑ b, Q b ≤ 1) :
    ∑ b, P b * Real.log (Q b / P b) ≤ 0 := by
  have key : ∀ b, P b * Real.log (Q b / P b) ≤ Q b - P b := by
    intro b
    rcases eq_or_lt_of_le (hP0 b) with h | h
    · rw [← h]
      simpa using hQ0 b
    · have hQb : 0 < Q b := lt_of_le_of_ne (hQ0 b) (Ne.symm (hac b (ne_of_gt h)))
      have hlog := Real.log_le_sub_one_of_pos (div_pos hQb h)
      calc P b * Real.log (Q b / P b) ≤ P b * (Q b / P b - 1) :=
            mul_le_mul_of_nonneg_left hlog (le_of_lt h)
        _ = Q b - P b := by field_simp
  calc ∑ b, P b * Real.log (Q b / P b) ≤ ∑ b, (Q b - P b) :=
        Finset.sum_le_sum fun b _ => key b
    _ = (∑ b, Q b) - ∑ b, P b := by rw [Finset.sum_sub_distrib]
    _ ≤ 0 := by rw [hP]; linarith

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The distribution of `X` under the weight `w`. -/
def wdist (w : Ω → ℝ) (X : Ω → β) (b : β) : ℝ :=
  wprob w ((univ : Finset Ω).filter fun ω => X ω = b)

lemma wdist_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (b : β) :
    0 ≤ wdist w X b := wprob_nonneg hw _

lemma sum_wdist (w : Ω → ℝ) (X : Ω → β) : ∑ b, wdist w X b = ∑ ω, w ω := by
  simpa [wdist, wprob] using Finset.sum_fiberwise (univ : Finset Ω) X w

lemma wdist_le_one {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1) (X : Ω → β)
    (b : β) : wdist w X b ≤ 1 := by
  rw [wdist, ← hsum, ← wprob_univ]
  exact wprob_mono hw (Finset.filter_subset _ _)

/-- The **Shannon entropy** of `X`, in nats. -/
noncomputable def wentropy (w : Ω → ℝ) (X : Ω → β) : ℝ :=
  ∑ b, Real.negMulLog (wdist w X b)

theorem wentropy_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1) (X : Ω → β) :
    0 ≤ wentropy w X :=
  Finset.sum_nonneg fun b _ =>
    Real.negMulLog_nonneg (wdist_nonneg hw X b) (wdist_le_one hw hsum X b)

/-- **The uniform distribution maximises entropy**: `H(X) ≤ log |β|`. -/
theorem wentropy_le_log_card {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (X : Ω → β) : wentropy w X ≤ Real.log (Fintype.card β) := by
  have hΩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  have hβ : Nonempty β := ⟨X (Classical.arbitrary Ω)⟩
  have hn : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hQsum : ∑ _b : β, (1 / (Fintype.card β : ℝ)) = 1 := by
    rw [Finset.sum_const, card_univ, nsmul_eq_mul, mul_one_div, div_self (ne_of_gt hn)]
  have hgibbs := sum_mul_log_div_le (wdist w X) (fun _ => 1 / (Fintype.card β : ℝ))
    (wdist_nonneg hw X) (fun _ => by positivity) (fun b _ => by positivity)
    (by rw [sum_wdist, hsum]) (le_of_eq hQsum)
  have hterm : ∀ b : β,
      wdist w X b * Real.log ((1 / (Fintype.card β : ℝ)) / wdist w X b)
        = Real.negMulLog (wdist w X b) - wdist w X b * Real.log (Fintype.card β) := by
    intro b
    rcases eq_or_lt_of_le (wdist_nonneg hw X b) with h | h
    · rw [← h]
      simp [Real.negMulLog]
    · rw [Real.log_div (by positivity) (ne_of_gt h), one_div, Real.log_inv, Real.negMulLog]
      ring
  rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_sub_distrib,
    ← Finset.sum_mul, sum_wdist, hsum, one_mul] at hgibbs
  have : wentropy w X = ∑ b, Real.negMulLog (wdist w X b) := rfl
  linarith [hgibbs]

/-- **Sharper: entropy is at most the log of the number of values actually attained.**

`PMC.wentropy_le_log_card` bounds by the size of the whole value type; for the counting
applications what is needed is the number of attained values, since that is the quantity
the combinatorics is about. Gibbs against the uniform distribution *on the image*. -/
theorem wentropy_le_log_card_image {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (Z : Ω → β) : wentropy w Z ≤ Real.log #((univ : Finset Ω).image Z) := by
  classical
  have hΩ : Nonempty Ω := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  have himg : ((univ : Finset Ω).image Z).Nonempty :=
    ⟨Z (Classical.arbitrary Ω), Finset.mem_image_of_mem Z (mem_univ _)⟩
  have hm : (0 : ℝ) < #((univ : Finset Ω).image Z) := by
    exact_mod_cast Finset.card_pos.mpr himg
  -- values off the image have probability zero
  have hoff : ∀ b : β, b ∉ (univ : Finset Ω).image Z → wdist w Z b = 0 := by
    intro b hb
    rw [wdist, wprob, Finset.filter_false_of_mem, Finset.sum_empty]
    intro ω _ hZω
    exact hb (Finset.mem_image.mpr ⟨ω, mem_univ ω, hZω⟩)
  have hQsum : ∑ b : β,
      (if b ∈ (univ : Finset Ω).image Z then 1 / (#((univ : Finset Ω).image Z) : ℝ) else 0)
      = 1 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one_div,
      div_self (ne_of_gt hm)]
  have hgibbs := sum_mul_log_div_le (wdist w Z)
    (fun b => if b ∈ (univ : Finset Ω).image Z then 1 / (#((univ : Finset Ω).image Z) : ℝ)
      else 0)
    (wdist_nonneg hw Z)
    (fun b => by by_cases hb : b ∈ (univ : Finset Ω).image Z <;> simp [hb] <;> positivity)
    (fun b hb => by
      have : b ∈ (univ : Finset Ω).image Z := by
        by_contra hcon
        exact hb (hoff b hcon)
      simp only [if_pos this]
      positivity)
    (by rw [sum_wdist, hsum]) (le_of_eq hQsum)
  have hterm : ∀ b : β, wdist w Z b
        * Real.log ((if b ∈ (univ : Finset Ω).image Z
            then 1 / (#((univ : Finset Ω).image Z) : ℝ) else 0) / wdist w Z b)
      = Real.negMulLog (wdist w Z b)
        - wdist w Z b * Real.log #((univ : Finset Ω).image Z) := by
    intro b
    rcases eq_or_lt_of_le (wdist_nonneg hw Z b) with h | h
    · rw [← h]
      simp [Real.negMulLog]
    · have hb : b ∈ (univ : Finset Ω).image Z := by
        by_contra hcon
        exact (ne_of_gt h) (hoff b hcon)
      rw [if_pos hb, Real.log_div (by positivity) (ne_of_gt h), one_div, Real.log_inv,
        Real.negMulLog]
      ring
  rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_wdist, hsum, one_mul] at hgibbs
  have hj : ∑ b : β, Real.negMulLog (wdist w Z b) = wentropy w Z := rfl
  rw [hj] at hgibbs
  linarith

/-- **An injective random variable under the uniform weight has entropy `log |Ω|`.**

The lower half of every entropy counting argument: it is what turns `H` back into a count.
-/
theorem wentropy_uniform_of_injective {Z : Ω → β} (hZ : Function.Injective Z)
    (hN : 0 < Fintype.card Ω) :
    wentropy (fun _ : Ω => (1 : ℝ) / Fintype.card Ω) Z = Real.log (Fintype.card Ω) := by
  classical
  have hNR : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hN
  have hval : ∀ b : β, wdist (fun _ : Ω => (1 : ℝ) / Fintype.card Ω) Z b
      = if b ∈ (univ : Finset Ω).image Z then 1 / (Fintype.card Ω : ℝ) else 0 := by
    intro b
    by_cases hb : b ∈ (univ : Finset Ω).image Z
    · obtain ⟨ω₀, -, hω₀⟩ := Finset.mem_image.mp hb
      have hfib : ((univ : Finset Ω).filter fun ω => Z ω = b) = {ω₀} := by
        ext ω
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        exact ⟨fun h => hZ (h.trans hω₀.symm), fun h => by rw [h, hω₀]⟩
      rw [wdist, wprob, hfib, Finset.sum_singleton, if_pos hb]
    · have hfib : ((univ : Finset Ω).filter fun ω => Z ω = b) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro ω hω
        simp only [mem_filter, mem_univ, true_and] at hω
        exact hb (Finset.mem_image.mpr ⟨ω, mem_univ ω, hω⟩)
      rw [wdist, wprob, hfib, Finset.sum_empty, if_neg hb]
  have hsummand : ∀ b : β,
      Real.negMulLog (wdist (fun _ : Ω => (1 : ℝ) / Fintype.card Ω) Z b)
        = if b ∈ (univ : Finset Ω).image Z
          then Real.negMulLog ((1 : ℝ) / Fintype.card Ω) else 0 := by
    intro b
    rw [hval b]
    by_cases hb : b ∈ (univ : Finset Ω).image Z <;> simp [hb, Real.negMulLog]
  rw [wentropy, Finset.sum_congr rfl fun b _ => hsummand b, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, Finset.card_image_of_injective univ hZ, card_univ,
    nsmul_eq_mul, Real.negMulLog, one_div, Real.log_inv]
  field_simp

variable {γ : Type*} [Fintype γ] [DecidableEq γ]

lemma filter_pair_eq (X : Ω → β) (Y : Ω → γ) (b : β) (c : γ) :
    (univ : Finset Ω).filter (fun ω => (X ω, Y ω) = (b, c))
      = ((univ : Finset Ω).filter fun ω => X ω = b).filter fun ω => Y ω = c := by
  ext ω
  simp [Prod.ext_iff, and_assoc]

lemma sum_wdist_pair_right (w : Ω → ℝ) (X : Ω → β) (Y : Ω → γ) (b : β) :
    ∑ c, wdist w (fun ω => (X ω, Y ω)) (b, c) = wdist w X b := by
  simp only [wdist, wprob]
  rw [Finset.sum_congr rfl fun c _ => by rw [filter_pair_eq X Y b c]]
  exact Finset.sum_fiberwise _ Y w

lemma sum_wdist_pair_left (w : Ω → ℝ) (X : Ω → β) (Y : Ω → γ) (c : γ) :
    ∑ b, wdist w (fun ω => (X ω, Y ω)) (b, c) = wdist w Y c := by
  simp only [wdist, wprob]
  rw [Finset.sum_congr rfl fun b _ => by
    rw [show (univ : Finset Ω).filter (fun ω => (X ω, Y ω) = (b, c))
        = ((univ : Finset Ω).filter fun ω => Y ω = c).filter fun ω => X ω = b from by
      ext ω; simp [Prod.ext_iff, and_comm, and_assoc]]]
  exact Finset.sum_fiberwise _ X w

lemma wdist_pair_le_left {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (Y : Ω → γ)
    (b : β) (c : γ) : wdist w (fun ω => (X ω, Y ω)) (b, c) ≤ wdist w X b :=
  wprob_mono hw fun ω hω => by
    simp only [mem_filter, mem_univ, true_and] at hω ⊢
    exact congrArg Prod.fst hω

lemma wdist_pair_le_right {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (Y : Ω → γ)
    (b : β) (c : γ) : wdist w (fun ω => (X ω, Y ω)) (b, c) ≤ wdist w Y c :=
  wprob_mono hw fun ω hω => by
    simp only [mem_filter, mem_univ, true_and] at hω ⊢
    exact congrArg Prod.snd hω

/-- **Entropy is subadditive**: `H(X, Y) ≤ H(X) + H(Y)` (Zhao, §10.1).

Gibbs' inequality against the product of the marginals. Absolute continuity is automatic
here: the joint distribution is dominated by each marginal, so a marginal that vanishes
forces the joint to vanish too. -/
theorem wentropy_pair_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (X : Ω → β) (Y : Ω → γ) :
    wentropy w (fun ω => (X ω, Y ω)) ≤ wentropy w X + wentropy w Y := by
  set P : β × γ → ℝ := wdist w fun ω => (X ω, Y ω) with hPdef
  set Q : β × γ → ℝ := fun q => wdist w X q.1 * wdist w Y q.2 with hQdef
  have hPle : ∀ q : β × γ, P q ≤ wdist w X q.1 ∧ P q ≤ wdist w Y q.2 := fun q =>
    ⟨wdist_pair_le_left hw X Y q.1 q.2, wdist_pair_le_right hw X Y q.1 q.2⟩
  have hP0 : ∀ q, 0 ≤ P q := fun q => wdist_nonneg hw _ q
  have hac : ∀ q, P q ≠ 0 → Q q ≠ 0 := by
    intro q hq
    have hX : wdist w X q.1 ≠ 0 := fun h =>
      hq (le_antisymm (by rw [← h]; exact (hPle q).1) (hP0 q))
    have hY : wdist w Y q.2 ≠ 0 := fun h =>
      hq (le_antisymm (by rw [← h]; exact (hPle q).2) (hP0 q))
    exact mul_ne_zero hX hY
  have hPsum : ∑ q, P q = 1 := by rw [hPdef, sum_wdist, hsum]
  have hQsum : ∑ q, Q q = 1 := by
    rw [hQdef, Fintype.sum_prod_type]
    simp only
    rw [← Finset.sum_mul_sum, sum_wdist, sum_wdist, hsum, mul_one]
  have hgibbs := sum_mul_log_div_le P Q hP0
    (fun q => mul_nonneg (wdist_nonneg hw X q.1) (wdist_nonneg hw Y q.2)) hac hPsum
    (le_of_eq hQsum)
  have hterm : ∀ q : β × γ, P q * Real.log (Q q / P q)
      = Real.negMulLog (P q) + P q * Real.log (wdist w X q.1)
        + P q * Real.log (wdist w Y q.2) := by
    intro q
    rcases eq_or_lt_of_le (hP0 q) with h | h
    · rw [← h]
      simp [Real.negMulLog]
    · have hX : wdist w X q.1 ≠ 0 := fun hz =>
        (ne_of_gt h) (le_antisymm (by rw [← hz]; exact (hPle q).1) (hP0 q))
      have hY : wdist w Y q.2 ≠ 0 := fun hz =>
        (ne_of_gt h) (le_antisymm (by rw [← hz]; exact (hPle q).2) (hP0 q))
      rw [Real.log_div (mul_ne_zero hX hY) (ne_of_gt h), Real.log_mul hX hY,
        Real.negMulLog]
      ring
  rw [Finset.sum_congr rfl fun q _ => hterm q] at hgibbs
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hgibbs
  have hXsum : ∑ q : β × γ, P q * Real.log (wdist w X q.1) = -wentropy w X := by
    rw [Fintype.sum_prod_type]
    simp only
    rw [wentropy, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_mul, sum_wdist_pair_right, Real.negMulLog]
    ring
  have hYsum : ∑ q : β × γ, P q * Real.log (wdist w Y q.2) = -wentropy w Y := by
    rw [Fintype.sum_prod_type_right]
    simp only
    rw [wentropy, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul, sum_wdist_pair_left, Real.negMulLog]
    ring
  have hjoint : ∑ q : β × γ, Real.negMulLog (P q) = wentropy w (fun ω => (X ω, Y ω)) := rfl
  rw [hXsum, hYsum, hjoint] at hgibbs
  linarith

/-! ### Conditional entropy and the chain rule -/

/-- The conditional distribution of `Y` given `X = b`. Where `P (X = b) = 0` this is `0`,
which is the convention that makes the chain rule hold without a side condition. -/
noncomputable def wcondDist (w : Ω → ℝ) (X : Ω → β) (Y : Ω → γ) (b : β) (c : γ) : ℝ :=
  wdist w (fun ω => (X ω, Y ω)) (b, c) / wdist w X b

/-- The conditional entropy `H(Y | X)`: the entropy of `Y` within each fibre of `X`,
averaged over the fibres. -/
noncomputable def wcondEntropy (w : Ω → ℝ) (X : Ω → β) (Y : Ω → γ) : ℝ :=
  ∑ b, wdist w X b * ∑ c, Real.negMulLog (wcondDist w X Y b c)

/-- **The chain rule**: `H(X, Y) = H(X) + H(Y | X)` (Zhao, §10.1).

Termwise this is Mathlib's `Real.negMulLog_mul`, applied to the factorisation
`P(X = b, Y = c) = P(X = b) · P(Y = c | X = b)`. The fibres where `P(X = b) = 0` need a
separate look — there the conditional distribution is `0/0 = 0` and does not sum to one —
but both sides vanish on them, so the identity survives with no side condition. -/
theorem wentropy_chain {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (Y : Ω → γ) :
    wentropy w (fun ω => (X ω, Y ω)) = wentropy w X + wcondEntropy w X Y := by
  have hfib : ∀ b : β, ∑ c, Real.negMulLog (wdist w (fun ω => (X ω, Y ω)) (b, c))
      = Real.negMulLog (wdist w X b)
        + wdist w X b * ∑ c, Real.negMulLog (wcondDist w X Y b c) := by
    intro b
    rcases eq_or_lt_of_le (wdist_nonneg hw X b) with h | h
    · -- an empty fibre: every joint probability under it vanishes, and so does every term
      have hz : ∀ c, wdist w (fun ω => (X ω, Y ω)) (b, c) = 0 := fun c =>
        le_antisymm (by rw [h]; exact wdist_pair_le_left hw X Y b c)
          (wdist_nonneg hw _ (b, c))
      simp [hz, ← h, Real.negMulLog]
    · have hfac : ∀ c, wdist w (fun ω => (X ω, Y ω)) (b, c)
          = wdist w X b * wcondDist w X Y b c := fun c => by
        rw [wcondDist, mul_div_cancel₀ _ (ne_of_gt h)]
      have hone : ∑ c, wcondDist w X Y b c = 1 := by
        simp only [wcondDist]
        rw [← Finset.sum_div, sum_wdist_pair_right, div_self (ne_of_gt h)]
      calc ∑ c, Real.negMulLog (wdist w (fun ω => (X ω, Y ω)) (b, c))
          = ∑ c, (wcondDist w X Y b c * Real.negMulLog (wdist w X b)
              + wdist w X b * Real.negMulLog (wcondDist w X Y b c)) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [hfac c, Real.negMulLog_mul]
        _ = (∑ c, wcondDist w X Y b c) * Real.negMulLog (wdist w X b)
              + wdist w X b * ∑ c, Real.negMulLog (wcondDist w X Y b c) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
        _ = Real.negMulLog (wdist w X b)
              + wdist w X b * ∑ c, Real.negMulLog (wcondDist w X Y b c) := by
            rw [hone, one_mul]
  rw [wentropy, Fintype.sum_prod_type,
    Finset.sum_congr rfl fun b _ => hfib b, Finset.sum_add_distrib]
  rfl

/-- **Conditioning reduces entropy**: `H(Y | X) ≤ H(Y)`.

Immediate from the chain rule and subadditivity — the two inequalities are the same fact
read in opposite directions. -/
theorem wcondEntropy_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (X : Ω → β) (Y : Ω → γ) : wcondEntropy w X Y ≤ wentropy w Y := by
  have h1 := wentropy_chain hw X Y
  have h2 := wentropy_pair_le hw hsum X Y
  linarith


/-- **Lemma 10.1.5 (independence).** For independent `X` and `Y`,
`H(X, Y) = H(X) + H(Y)`.

By the chain rule it is enough that conditioning on `X` does nothing: independence makes the
conditional distribution of `Y` equal to its marginal on every fibre of positive weight, and
the fibres of weight zero contribute nothing to either side. -/
theorem wentropy_pair_of_indep {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (X : Ω → β) (Y : Ω → γ)
    (hindep : ∀ b c, wdist w (fun ω => (X ω, Y ω)) (b, c) = wdist w X b * wdist w Y c) :
    wentropy w (fun ω => (X ω, Y ω)) = wentropy w X + wentropy w Y := by
  classical
  rw [wentropy_chain hw X Y]
  congr 1
  rw [wcondEntropy]
  have hterm : ∀ b : β, wdist w X b * ∑ c, Real.negMulLog (wcondDist w X Y b c)
      = wdist w X b * wentropy w Y := by
    intro b
    rcases eq_or_lt_of_le (wdist_nonneg hw X b) with h | h
    · rw [← h, zero_mul, zero_mul]
    · refine congrArg (fun t => wdist w X b * t) ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine congrArg Real.negMulLog ?_
      rw [wcondDist, hindep b c, mul_comm, mul_div_assoc, div_self (ne_of_gt h), mul_one]
  rw [Finset.sum_congr rfl fun b _ => hterm b, ← Finset.sum_mul, sum_wdist, hsum, one_mul]

/-! ### Basic monotonicity, and entropy as a function of the fibres -/

lemma wcondDist_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (Y : Ω → γ) (b : β)
    (c : γ) : 0 ≤ wcondDist w X Y b c :=
  div_nonneg (wdist_nonneg hw _ _) (wdist_nonneg hw X b)

lemma wcondDist_le_one {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (Y : Ω → γ) (b : β)
    (c : γ) : wcondDist w X Y b c ≤ 1 := by
  rw [wcondDist]
  rcases eq_or_lt_of_le (wdist_nonneg hw X b) with h | h
  · rw [← h]; simp
  · rw [div_le_one h]
    exact wdist_pair_le_left hw X Y b c

theorem wcondEntropy_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (Y : Ω → γ) :
    0 ≤ wcondEntropy w X Y :=
  Finset.sum_nonneg fun b _ => mul_nonneg (wdist_nonneg hw X b)
    (Finset.sum_nonneg fun c _ =>
      Real.negMulLog_nonneg (wcondDist_nonneg hw X Y b c) (wcondDist_le_one hw X Y b c))

/-- **Adding a coordinate never decreases entropy.** Chain rule plus
`PMC.wcondEntropy_nonneg`. -/
theorem wentropy_le_pair {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (Y : Ω → γ) :
    wentropy w X ≤ wentropy w (fun ω => (X ω, Y ω)) := by
  have h := wentropy_chain hw X Y
  have h2 := wcondEntropy_nonneg hw X Y
  linarith

/-- A constant random variable carries no information. -/
theorem wentropy_const {w : Ω → ℝ} (hsum : ∑ ω, w ω = 1) (b0 : β) :
    wentropy w (fun _ : Ω => b0) = 0 := by
  rw [wentropy]
  refine Finset.sum_eq_zero fun b _ => ?_
  have hval : wdist w (fun _ : Ω => b0) b = if b0 = b then 1 else 0 := by
    rw [wdist, wprob]
    by_cases h : b0 = b
    · rw [if_pos h, Finset.filter_true_of_mem fun _ _ => h]
      exact hsum
    · rw [if_neg h, Finset.filter_false_of_mem fun _ _ => h, Finset.sum_empty]
  rw [hval]
  by_cases h : b0 = b <;> simp [h, Real.negMulLog]

/-- **Entropy depends only on the fibres.**

If `X` and `Y` determine each other pointwise — `Y = g ∘ X` and `X = h ∘ Y` — then they have
the same entropy. Note that `g` and `h` need *not* be mutually inverse on the whole value
types, only along the ranges of `X` and `Y`; that is exactly what makes this usable for
comparing a masked tuple `X_{T ∪ T'}` with the pair `(X_T, X_{T'})`, whose value types have
no bijection between them at all. -/
theorem wentropy_congr (w : Ω → ℝ) (X : Ω → β) (Y : Ω → γ) (g : β → γ) (h : γ → β)
    (hg : ∀ ω, Y ω = g (X ω)) (hh : ∀ ω, X ω = h (Y ω)) :
    wentropy w X = wentropy w Y := by
  classical
  have hzX : ∀ b : β, (¬ ∃ ω, X ω = b) → Real.negMulLog (wdist w X b) = 0 := by
    intro b hb
    have hemp : ((univ : Finset Ω).filter fun ω => X ω = b) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω
      exact hb ⟨ω, hω⟩
    rw [wdist, wprob, hemp, Finset.sum_empty]
    simp [Real.negMulLog]
  have hzY : ∀ c : γ, (¬ ∃ ω, Y ω = c) → Real.negMulLog (wdist w Y c) = 0 := by
    intro c hc
    have hemp : ((univ : Finset Ω).filter fun ω => Y ω = c) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω
      exact hc ⟨ω, hω⟩
    rw [wdist, wprob, hemp, Finset.sum_empty]
    simp [Real.negMulLog]
  have e1 : ∑ b ∈ (univ : Finset β).filter (fun b => ∃ ω, X ω = b),
      Real.negMulLog (wdist w X b) = wentropy w X :=
    Finset.sum_subset (Finset.filter_subset _ _) fun b _ hb =>
      hzX b fun hex => hb (Finset.mem_filter.mpr ⟨mem_univ b, hex⟩)
  have e2 : ∑ c ∈ (univ : Finset γ).filter (fun c => ∃ ω, Y ω = c),
      Real.negMulLog (wdist w Y c) = wentropy w Y :=
    Finset.sum_subset (Finset.filter_subset _ _) fun c _ hc =>
      hzY c fun hex => hc (Finset.mem_filter.mpr ⟨mem_univ c, hex⟩)
  rw [← e1, ← e2]
  refine Finset.sum_nbij' g h ?_ ?_ ?_ ?_ ?_
  · intro b hb
    obtain ⟨ω₀, hω₀⟩ := (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨mem_univ _, ⟨ω₀, by rw [hg ω₀, hω₀]⟩⟩
  · intro c hc
    obtain ⟨ω₀, hω₀⟩ := (Finset.mem_filter.mp hc).2
    exact Finset.mem_filter.mpr ⟨mem_univ _, ⟨ω₀, by rw [hh ω₀, hω₀]⟩⟩
  · intro b hb
    obtain ⟨ω₀, hω₀⟩ := (Finset.mem_filter.mp hb).2
    rw [← hω₀, ← hg ω₀, ← hh ω₀]
  · intro c hc
    obtain ⟨ω₀, hω₀⟩ := (Finset.mem_filter.mp hc).2
    rw [← hω₀, ← hh ω₀, ← hg ω₀]
  · intro b hb
    obtain ⟨ω₀, hω₀⟩ := (Finset.mem_filter.mp hb).2
    have hgb : g b = Y ω₀ := by rw [← hω₀, ← hg ω₀]
    have hb' : h (g b) = b := by rw [hgb, ← hh ω₀, hω₀]
    congr 1
    rw [wdist, wdist]
    congr 1
    ext ω
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hx; rw [hg ω, hx]
    · intro hy; rw [hh ω, hy, hb']

/-! ### The binomial tail bound (§10.1)

The notes bound the lower tail of a binomial coefficient sum two ways: by the moment
generating function, giving

`∑_{0 ≤ i ≤ k} C(n,i) ≤ (1+x)ⁿ / xᵏ` for every `x ∈ [0,1]`,

and then, taking the infimum over `x`, by `2^(H(k/n) n)`. The explicit-`x` form is the one
this project wants — it is finite, sharp, and carries no `o(1)` — so it is what is proved
here; the entropy form follows from it by substituting the minimising `x`, which is a
real-analysis optimisation rather than a combinatorial step.

Stated multiplicatively (`… * xᵏ ≤ (1+x)ⁿ`) so that `x = 0` needs no special case.
-/

/-- **The binomial tail bound**, in explicit form: for every `x ∈ [0,1]`,
`(∑_{i ≤ k} C(n,i)) · xᵏ ≤ (1+x)ⁿ`.

The whole content is that `xᵏ ≤ xⁱ` for `i ≤ k` when `x ≤ 1`, so the truncated sum, each of
whose terms is weighted by the *smallest* power, is dominated by the full binomial
expansion. -/
theorem sum_choose_mul_pow_le {n k : ℕ} (hk : k ≤ n) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) * x ^ k ≤ (1 + x) ^ n := by
  have hbin : (1 + x) ^ n = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * x ^ i := by
    rw [show (1 : ℝ) + x = x + 1 from add_comm 1 x, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_pow, mul_one]
    ring
  rw [hbin, Finset.sum_mul]
  calc ∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ) * x ^ k
      ≤ ∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ) * x ^ i := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_range] at hi
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hx0 hx1 (by omega)) (by positivity)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * x ^ i := by
        have hsub : Finset.range (k + 1) ⊆ Finset.range (n + 1) := by
          intro i hi
          rw [Finset.mem_range] at hi ⊢
          omega
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity

/-- **The binomial tail bound at its optimal `x`**, which is the entropy bound in algebraic
form: for `0 < k` and `2k ≤ n`,

`∑_{i ≤ k} C(n,i) ≤ (n/k)^k · (n/(n-k))^(n-k)`.

The right-hand side is exactly `2 ^ (H(k/n) · n)` — substituting `p = k/n` into
`p^(-np) (1-p)^(-n(1-p))` gives it — so this *is* the notes' entropy bound, stated without
logarithms. Keeping it algebraic is preferable here: it is sharp, it needs no `Real.log`,
and it makes the `2k ≤ n` hypothesis visible.

That hypothesis is not cosmetic and the notes state it too ("varying over `m ≤ k ≤ n/2`"):
the minimising `x = k/(n-k)` exceeds `1` once `2k > n`, and `PMC.sum_choose_mul_pow_le`
needs `x ≤ 1`. -/
theorem sum_choose_le_pow_mul_pow {n k : ℕ} (hk0 : 0 < k) (hk2 : 2 * k ≤ n) (hkn : k < n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ))
      ≤ ((n : ℝ) / k) ^ k * ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  have hnkR : (0 : ℝ) < (n : ℝ) - k := by linarith
  have h2kR : (2 : ℝ) * k ≤ n := by exact_mod_cast hk2
  set x : ℝ := (k : ℝ) / ((n : ℝ) - k) with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_one hnkR]
    linarith
  have hne : ((n : ℝ) - k) ≠ 0 := ne_of_gt hnkR
  have h1x : 1 + x = (n : ℝ) / ((n : ℝ) - k) := by
    rw [hxdef, eq_div_iff hne, add_mul, one_mul, div_mul_cancel₀ _ hne]
    ring
  have hmain := sum_choose_mul_pow_le (n := n) (k := k) (le_of_lt hkn) hx0 hx1
  rw [h1x] at hmain
  have hxk : (0 : ℝ) < x ^ k := by rw [hxdef]; positivity
  rw [← le_div_iff₀ hxk] at hmain
  refine hmain.trans (le_of_eq ?_)
  have hpow : ((n : ℝ) / ((n : ℝ) - k)) ^ n
      = ((n : ℝ) / ((n : ℝ) - k)) ^ k * ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k) := by
    rw [← pow_add]
    congr 1
    omega
  have hkey : ((n : ℝ) / ((n : ℝ) - k)) / x = (n : ℝ) / k := by
    rw [hxdef, div_div_eq_mul_div, div_mul_cancel₀ _ hne]
  calc ((n : ℝ) / ((n : ℝ) - k)) ^ n / x ^ k
      = ((n : ℝ) / ((n : ℝ) - k)) ^ k * ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k) / x ^ k := by
        rw [hpow]
    _ = (((n : ℝ) / ((n : ℝ) - k)) ^ k / x ^ k)
          * ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k) := by ring
    _ = ((n : ℝ) / k) ^ k * ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k) := by
        rw [← div_pow, hkey]

/-! ### Relabelling, and submodularity

Submodularity, `H(X,Y,Z) + H(X) ≤ H(X,Y) + H(X,Z)`, is the last of the structural entropy
inequalities and the one Shearer's lemma runs on. It is Gibbs' inequality again, now
against `Q(x,y,z) = P(x,y) P(x,z) / P(x)`, whose total mass is `∑ x P(x)² / P(x) = 1` where
`P(x)` is positive and `0` elsewhere — hence `≤ 1`, which is all Gibbs needs.
-/

/-- Entropy depends only on the distribution, so relabelling the values changes nothing.
This is what lets `(β × γ) × δ` and `β × γ × δ` be used interchangeably. -/
lemma wdist_equiv {β' : Type*} [Fintype β'] [DecidableEq β'] (w : Ω → ℝ) (X : Ω → β)
    (e : β ≃ β') (b' : β') : wdist w (fun ω => e (X ω)) b' = wdist w X (e.symm b') := by
  simp only [wdist]
  congr 1
  ext ω
  simp [Equiv.eq_symm_apply]

lemma wentropy_equiv {β' : Type*} [Fintype β'] [DecidableEq β'] (w : Ω → ℝ) (X : Ω → β)
    (e : β ≃ β') : wentropy w (fun ω => e (X ω)) = wentropy w X := by
  rw [wentropy, wentropy, Finset.sum_congr rfl fun b' _ => by rw [wdist_equiv w X e b']]
  exact Equiv.sum_comp e.symm fun b => Real.negMulLog (wdist w X b)

variable {δ : Type*} [Fintype δ] [DecidableEq δ]

/-- Iterated sums over a triple product, with the projections already reduced away. Stated
with `f` in curried form so that `rw` never has to guess a higher-order pattern. -/
private lemma sum_triple {M : Type*} [AddCommMonoid M] (f : β → γ → δ → M) :
    ∑ q : β × γ × δ, f q.1 q.2.1 q.2.2 = ∑ b, ∑ c, ∑ d, f b c d := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun b _ => Fintype.sum_prod_type ..

lemma sum_wdist_triple_right (w : Ω → ℝ) (X : Ω → β) (Y : Ω → γ) (Z : Ω → δ) (b : β) (c : γ) :
    ∑ d, wdist w (fun ω => (X ω, Y ω, Z ω)) (b, c, d)
      = wdist w (fun ω => (X ω, Y ω)) (b, c) := by
  simp only [wdist, wprob]
  rw [Finset.sum_congr rfl fun d _ => by
    rw [show (univ : Finset Ω).filter (fun ω => (X ω, Y ω, Z ω) = (b, c, d))
        = ((univ : Finset Ω).filter fun ω => (X ω, Y ω) = (b, c)).filter fun ω => Z ω = d from by
      ext ω; simp [Prod.ext_iff, and_assoc]]]
  exact Finset.sum_fiberwise _ Z w

lemma sum_wdist_triple_mid (w : Ω → ℝ) (X : Ω → β) (Y : Ω → γ) (Z : Ω → δ) (b : β) (d : δ) :
    ∑ c, wdist w (fun ω => (X ω, Y ω, Z ω)) (b, c, d)
      = wdist w (fun ω => (X ω, Z ω)) (b, d) := by
  simp only [wdist, wprob]
  rw [Finset.sum_congr rfl fun c _ => by
    rw [show (univ : Finset Ω).filter (fun ω => (X ω, Y ω, Z ω) = (b, c, d))
        = ((univ : Finset Ω).filter fun ω => (X ω, Z ω) = (b, d)).filter fun ω => Y ω = c from by
      ext ω
      simp only [mem_filter, mem_univ, true_and, Prod.ext_iff]
      tauto]]
  exact Finset.sum_fiberwise _ Y w

lemma wdist_triple_le_pair_right {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (Y : Ω → γ)
    (Z : Ω → δ) (b : β) (c : γ) (d : δ) :
    wdist w (fun ω => (X ω, Y ω, Z ω)) (b, c, d) ≤ wdist w (fun ω => (X ω, Y ω)) (b, c) :=
  wprob_mono hw fun ω hω => by
    simp only [mem_filter, mem_univ, true_and, Prod.ext_iff] at hω ⊢
    exact ⟨hω.1, hω.2.1⟩

lemma wdist_triple_le_pair_mid {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (Y : Ω → γ)
    (Z : Ω → δ) (b : β) (c : γ) (d : δ) :
    wdist w (fun ω => (X ω, Y ω, Z ω)) (b, c, d) ≤ wdist w (fun ω => (X ω, Z ω)) (b, d) :=
  wprob_mono hw fun ω hω => by
    simp only [mem_filter, mem_univ, true_and, Prod.ext_iff] at hω ⊢
    exact ⟨hω.1, hω.2.2⟩

lemma wdist_triple_le_left {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Ω → β) (Y : Ω → γ)
    (Z : Ω → δ) (b : β) (c : γ) (d : δ) :
    wdist w (fun ω => (X ω, Y ω, Z ω)) (b, c, d) ≤ wdist w X b :=
  wprob_mono hw fun ω hω => by
    simp only [mem_filter, mem_univ, true_and, Prod.ext_iff] at hω ⊢
    exact hω.1

/-- **Entropy is submodular**: `H(X,Y,Z) + H(X) ≤ H(X,Y) + H(X,Z)` (Zhao, §10.1).

Gibbs' inequality against `Q(x,y,z) = P(x,y) P(x,z) / P(x)`. As with subadditivity,
absolute continuity is free: the joint distribution is dominated by each of its marginals,
so every factor of `Q` is positive wherever `P` is. -/
theorem wentropy_submodular {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (X : Ω → β) (Y : Ω → γ) (Z : Ω → δ) :
    wentropy w (fun ω => (X ω, Y ω, Z ω)) + wentropy w X
      ≤ wentropy w (fun ω => (X ω, Y ω)) + wentropy w (fun ω => (X ω, Z ω)) := by
  have hP0 : ∀ q : β × γ × δ, 0 ≤ wdist w (fun ω => (X ω, Y ω, Z ω)) q :=
    fun q => wdist_nonneg hw _ q
  have hforce : ∀ (q : β × γ × δ) (r : ℝ),
      wdist w (fun ω => (X ω, Y ω, Z ω)) q ≤ r → r = 0 →
      wdist w (fun ω => (X ω, Y ω, Z ω)) q = 0 := by
    intro q r hle hr
    exact le_antisymm (by rw [← hr]; exact hle) (hP0 q)
  -- per-fibre bound on the total mass of `Q`
  have hper : ∀ b : β, ∑ c : γ, ∑ d : δ,
      wdist w (fun ω => (X ω, Y ω)) (b, c) * wdist w (fun ω => (X ω, Z ω)) (b, d)
        / wdist w X b ≤ wdist w X b := by
    intro b
    have h1 : ∑ c : γ, ∑ d : δ,
        wdist w (fun ω => (X ω, Y ω)) (b, c) * wdist w (fun ω => (X ω, Z ω)) (b, d)
          / wdist w X b
        = (∑ c, wdist w (fun ω => (X ω, Y ω)) (b, c))
            * (∑ d, wdist w (fun ω => (X ω, Z ω)) (b, d)) / wdist w X b := by
      rw [Finset.sum_mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun c _ => (Finset.sum_div ..).symm
    rw [h1, sum_wdist_pair_right, sum_wdist_pair_right]
    rcases eq_or_lt_of_le (wdist_nonneg hw X b) with h | h
    · rw [← h]; simp
    · rw [mul_div_assoc, div_self (ne_of_gt h), mul_one]
  have hQsum : ∑ q : β × γ × δ,
      wdist w (fun ω => (X ω, Y ω)) (q.1, q.2.1) * wdist w (fun ω => (X ω, Z ω)) (q.1, q.2.2)
        / wdist w X q.1 ≤ 1 := by
    rw [sum_triple fun (b : β) (c : γ) (d : δ) =>
      wdist w (fun ω => (X ω, Y ω)) (b, c) * wdist w (fun ω => (X ω, Z ω)) (b, d)
        / wdist w X b]
    calc ∑ b : β, ∑ c : γ, ∑ d : δ,
          wdist w (fun ω => (X ω, Y ω)) (b, c) * wdist w (fun ω => (X ω, Z ω)) (b, d)
            / wdist w X b
        ≤ ∑ b : β, wdist w X b := Finset.sum_le_sum fun b _ => hper b
      _ = 1 := by rw [sum_wdist, hsum]
  have hgibbs := sum_mul_log_div_le (wdist w fun ω => (X ω, Y ω, Z ω))
    (fun q => wdist w (fun ω => (X ω, Y ω)) (q.1, q.2.1)
      * wdist w (fun ω => (X ω, Z ω)) (q.1, q.2.2) / wdist w X q.1)
    hP0
    (fun q => div_nonneg (mul_nonneg (wdist_nonneg hw _ _) (wdist_nonneg hw _ _))
      (wdist_nonneg hw X q.1))
    (fun q hq => div_ne_zero
      (mul_ne_zero (fun h => hq (hforce q _ (wdist_triple_le_pair_right hw X Y Z _ _ _) h))
        (fun h => hq (hforce q _ (wdist_triple_le_pair_mid hw X Y Z _ _ _) h)))
      (fun h => hq (hforce q _ (wdist_triple_le_left hw X Y Z _ _ _) h)))
    (by rw [sum_wdist, hsum]) hQsum
  -- termwise decomposition of the Gibbs summand
  have hterm : ∀ q : β × γ × δ,
      wdist w (fun ω => (X ω, Y ω, Z ω)) q
          * Real.log (wdist w (fun ω => (X ω, Y ω)) (q.1, q.2.1)
              * wdist w (fun ω => (X ω, Z ω)) (q.1, q.2.2) / wdist w X q.1
              / wdist w (fun ω => (X ω, Y ω, Z ω)) q)
        = Real.negMulLog (wdist w (fun ω => (X ω, Y ω, Z ω)) q)
            + wdist w (fun ω => (X ω, Y ω, Z ω)) q
                * Real.log (wdist w (fun ω => (X ω, Y ω)) (q.1, q.2.1))
            + wdist w (fun ω => (X ω, Y ω, Z ω)) q
                * Real.log (wdist w (fun ω => (X ω, Z ω)) (q.1, q.2.2))
            - wdist w (fun ω => (X ω, Y ω, Z ω)) q * Real.log (wdist w X q.1) := by
    intro q
    rcases eq_or_lt_of_le (hP0 q) with h | h
    · rw [← h]
      simp [Real.negMulLog]
    · have h1 : wdist w (fun ω => (X ω, Y ω)) (q.1, q.2.1) ≠ 0 := fun hz =>
        (ne_of_gt h) (hforce q _ (wdist_triple_le_pair_right hw X Y Z _ _ _) hz)
      have h2 : wdist w (fun ω => (X ω, Z ω)) (q.1, q.2.2) ≠ 0 := fun hz =>
        (ne_of_gt h) (hforce q _ (wdist_triple_le_pair_mid hw X Y Z _ _ _) hz)
      have h3 : wdist w X q.1 ≠ 0 := fun hz =>
        (ne_of_gt h) (hforce q _ (wdist_triple_le_left hw X Y Z _ _ _) hz)
      rw [Real.log_div (div_ne_zero (mul_ne_zero h1 h2) h3) (ne_of_gt h),
        Real.log_div (mul_ne_zero h1 h2) h3, Real.log_mul h1 h2, Real.negMulLog]
      ring
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib] at hgibbs
  -- identify the four sums
  have hXY : ∑ q : β × γ × δ, wdist w (fun ω => (X ω, Y ω, Z ω)) q
        * Real.log (wdist w (fun ω => (X ω, Y ω)) (q.1, q.2.1))
      = -wentropy w (fun ω => (X ω, Y ω)) := by
    rw [sum_triple fun (b : β) (c : γ) (d : δ) => wdist w (fun ω => (X ω, Y ω, Z ω)) (b, c, d)
      * Real.log (wdist w (fun ω => (X ω, Y ω)) (b, c))]
    rw [wentropy, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul, sum_wdist_triple_right, Real.negMulLog]
    ring
  have hXZ : ∑ q : β × γ × δ, wdist w (fun ω => (X ω, Y ω, Z ω)) q
        * Real.log (wdist w (fun ω => (X ω, Z ω)) (q.1, q.2.2))
      = -wentropy w (fun ω => (X ω, Z ω)) := by
    rw [sum_triple fun (b : β) (c : γ) (d : δ) => wdist w (fun ω => (X ω, Y ω, Z ω)) (b, c, d)
      * Real.log (wdist w (fun ω => (X ω, Z ω)) (b, d))]
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm ..]
    rw [wentropy, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_mul, sum_wdist_triple_mid, Real.negMulLog]
    ring
  have hX : ∑ q : β × γ × δ, wdist w (fun ω => (X ω, Y ω, Z ω)) q
        * Real.log (wdist w X q.1) = -wentropy w X := by
    rw [sum_triple fun (b : β) (c : γ) (d : δ) => wdist w (fun ω => (X ω, Y ω, Z ω)) (b, c, d)
      * Real.log (wdist w X b)]
    rw [wentropy, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_congr rfl fun c _ => (Finset.sum_mul ..).symm,
      Finset.sum_congr rfl fun c _ => by rw [sum_wdist_triple_right w X Y Z b c],
      ← Finset.sum_mul, sum_wdist_pair_right, Real.negMulLog]
    ring
  have hjoint : ∑ q : β × γ × δ, Real.negMulLog (wdist w (fun ω => (X ω, Y ω, Z ω)) q)
      = wentropy w (fun ω => (X ω, Y ω, Z ω)) := rfl
  rw [hXY, hXZ, hX, hjoint] at hgibbs
  linarith

/-- **Shearer's lemma, the special case** (Zhao, Theorem 10.4.1):

`2 H(X,Y,Z) ≤ H(X,Y) + H(X,Z) + H(Y,Z)`.

The notes derive it from the chain rule and conditioning-dropping. Here it is two lines:
submodularity gives `H(X,Y,Z) + H(X) ≤ H(X,Y) + H(X,Z)`, subadditivity applied to `X`
against the pair `(Y,Z)` gives `H(X,Y,Z) ≤ H(X) + H(Y,Z)`, and adding the two cancels
`H(X)`. Note this is *not* an instance of `PMC.shearer` — that one needs all coordinates to
share a type, whereas here `X`, `Y` and `Z` may have three different ones. -/
theorem wentropy_shearer_triple {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (X : Ω → β) (Y : Ω → γ) (Z : Ω → δ) :
    2 * wentropy w (fun ω => (X ω, Y ω, Z ω))
      ≤ wentropy w (fun ω => (X ω, Y ω)) + wentropy w (fun ω => (X ω, Z ω))
        + wentropy w (fun ω => (Y ω, Z ω)) := by
  have hsub := wentropy_submodular hw hsum X Y Z
  have hadd := wentropy_pair_le hw hsum X (fun ω => (Y ω, Z ω))
  linarith

/-- **Conditioning on more reduces entropy**: `H(Y | X, Z) ≤ H(Y | X)`.

Submodularity, re-read through the chain rule. This is the step Shearer's induction takes
for each coordinate. -/
theorem wcondEntropy_le_of_pair {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (X : Ω → β) (Y : Ω → γ) (Z : Ω → δ) :
    wcondEntropy w (fun ω => (X ω, Z ω)) Y ≤ wcondEntropy w X Y := by
  have hsub := wentropy_submodular hw hsum X Z Y
  have hc1 := wentropy_chain hw (fun ω => (X ω, Z ω)) Y
  have hc2 := wentropy_chain hw X Y
  have heq : wentropy w (fun ω => ((X ω, Z ω), Y ω))
      = wentropy w (fun ω => (X ω, Z ω, Y ω)) :=
    (wentropy_equiv w (fun ω => ((X ω, Z ω), Y ω)) (Equiv.prodAssoc β δ γ)).symm
  rw [heq] at hc1
  linarith

/-- **Entropy never increases under a function of the variable**: `H(f ∘ Z) ≤ H(Z)`.

Via `PMC.wentropy_congr`: `(f ∘ Z, Z)` and `Z` determine each other, so they have equal
entropy, and dropping the second coordinate can only lose. -/
theorem wentropy_comp_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {β' : Type*} [Fintype β']
    [DecidableEq β'] (Z : Ω → β') (f : β' → β) :
    wentropy w (fun ω => f (Z ω)) ≤ wentropy w Z := by
  have h1 : wentropy w (fun ω => (f (Z ω), Z ω)) = wentropy w Z :=
    (wentropy_congr w Z (fun ω => (f (Z ω), Z ω)) (fun z => (f z, z)) Prod.snd
      (fun _ => rfl) (fun _ => rfl)).symm
  have h2 := wentropy_le_pair hw (fun ω => f (Z ω)) Z
  linarith

end Entropy

/-! ## The entropy of a masked tuple

Shearer's lemma is a statement about the set function `S ↦ H(X_S)` for a tuple of random
variables `X`. Rather than restricting to a subtype — which would make `X_S` and
`X_{S'}` live in different types and force dependent-type bookkeeping at every step — we
represent `X_S` by *masking*: coordinates outside `S` are replaced by `none`. Every
`X_S` then has one and the same type `ι → Option β`, and the identities relating
`(X_S, X_T)` to `X_{S ∪ T}` are all instances of `PMC.wentropy_congr`.

Using `Option β` rather than a default value avoids requiring `Inhabited β` and keeps
"erased" distinguishable from every real value.

The three properties below — normalised at `∅`, monotone, and submodular in
diminishing-returns form — are exactly the hypotheses Shearer's lemma needs; what remains
of Shearer is a statement about set functions with no entropy in it at all.
-/

section Tuple

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {β : Type*} [Fintype β] [DecidableEq β]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The tuple `X` masked to the coordinates in `S`. -/
def masked (X : ι → Ω → β) (S : Finset ι) (ω : Ω) : ι → Option β :=
  fun i => if i ∈ S then some (X i ω) else none

/-- Overlay: the first argument wins wherever it is defined. -/
def overlay (u v : ι → Option β) : ι → Option β := fun i => (u i).orElse fun _ => v i

/-- Erase every coordinate outside `S`. -/
def projMask (S : Finset ι) (u : ι → Option β) : ι → Option β :=
  fun i => if i ∈ S then u i else none

lemma overlay_masked (X : ι → Ω → β) (S T : Finset ι) (ω : Ω) :
    overlay (masked X S ω) (masked X T ω) = masked X (S ∪ T) ω := by
  funext i
  simp only [overlay, masked, Finset.mem_union]
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]

lemma projMask_masked (X : ι → Ω → β) {S T : Finset ι} (hST : S ⊆ T) (ω : Ω) :
    projMask S (masked X T ω) = masked X S ω := by
  funext i
  simp only [projMask, masked]
  by_cases h : i ∈ S
  · simp [h, hST h]
  · simp [h]

/-- The entropy of the masked tuple — the set function Shearer's lemma is about. -/
noncomputable def tupleEntropy (w : Ω → ℝ) (X : ι → Ω → β) (S : Finset ι) : ℝ :=
  wentropy w (masked X S)

/-- Two masked tuples jointly carry exactly the information of the mask of their union. -/
theorem wentropy_masked_pair (w : Ω → ℝ) (X : ι → Ω → β) (S T : Finset ι) :
    wentropy w (fun ω => (masked X S ω, masked X T ω)) = tupleEntropy w X (S ∪ T) := by
  refine (wentropy_congr w (masked X (S ∪ T))
    (fun ω => (masked X S ω, masked X T ω))
    (fun u => (projMask S u, projMask T u)) (fun p => overlay p.1 p.2) ?_ ?_).symm
  · intro ω
    have hS : S ⊆ S ∪ T := Finset.subset_union_left
    have hT : T ⊆ S ∪ T := Finset.subset_union_right
    rw [Prod.ext_iff]
    exact ⟨(projMask_masked X hS ω).symm, (projMask_masked X hT ω).symm⟩
  · intro ω
    exact (overlay_masked X S T ω).symm

theorem wentropy_masked_triple (w : Ω → ℝ) (X : ι → Ω → β) (S T U : Finset ι) :
    wentropy w (fun ω => (masked X S ω, masked X T ω, masked X U ω))
      = tupleEntropy w X (S ∪ T ∪ U) := by
  refine (wentropy_congr w (masked X (S ∪ T ∪ U))
    (fun ω => (masked X S ω, masked X T ω, masked X U ω))
    (fun u => (projMask S u, projMask T u, projMask U u))
    (fun p => overlay p.1 (overlay p.2.1 p.2.2)) ?_ ?_).symm
  · intro ω
    have hS : S ⊆ S ∪ T ∪ U :=
      Finset.subset_union_left.trans Finset.subset_union_left
    have hT : T ⊆ S ∪ T ∪ U :=
      Finset.subset_union_right.trans Finset.subset_union_left
    have hU : U ⊆ S ∪ T ∪ U := Finset.subset_union_right
    rw [Prod.ext_iff, Prod.ext_iff]
    exact ⟨(projMask_masked X hS ω).symm,
      (projMask_masked X hT ω).symm, (projMask_masked X hU ω).symm⟩
  · intro ω
    rw [overlay_masked, overlay_masked, Finset.union_assoc]

/-- `H(X_∅) = 0`: the empty mask carries no information. -/
@[simp] theorem tupleEntropy_empty {w : Ω → ℝ} (hsum : ∑ ω, w ω = 1) (X : ι → Ω → β) :
    tupleEntropy w X ∅ = 0 := by
  have hconst : masked X (∅ : Finset ι) = fun _ : Ω => (fun _ : ι => (none : Option β)) := by
    funext ω i
    simp [masked]
  rw [tupleEntropy, hconst, wentropy_const hsum]

/-- `S ↦ H(X_S)` is monotone: more coordinates, more entropy. -/
theorem tupleEntropy_mono {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : ι → Ω → β) {S T : Finset ι}
    (hST : S ⊆ T) : tupleEntropy w X S ≤ tupleEntropy w X T := by
  have hrw : masked X S = fun ω => projMask S (masked X T ω) := by
    funext ω
    exact (projMask_masked X hST ω).symm
  rw [tupleEntropy, tupleEntropy, hrw]
  exact wentropy_comp_le hw (masked X T) (projMask S)

/-- **`S ↦ H(X_S)` is submodular, in diminishing-returns form.**

Adding the coordinate `i` to a larger set helps no more than adding it to a smaller one.
This is `PMC.wentropy_submodular` applied to the three masks `X_T`, `X_{T' \ T}` and
`X_{\{i\}}`, with `PMC.wentropy_masked_pair` and `PMC.wentropy_masked_triple` used to read
the results back as values of `tupleEntropy`. No hypothesis on `i` is needed. -/
theorem tupleEntropy_submodular {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (X : ι → Ω → β) {T T' : Finset ι} (hT : T ⊆ T') (i : ι) :
    tupleEntropy w X (insert i T') - tupleEntropy w X T'
      ≤ tupleEntropy w X (insert i T) - tupleEntropy w X T := by
  have hsub := wentropy_submodular hw hsum (masked X T) (masked X (T' \ T)) (masked X {i})
  rw [wentropy_masked_triple, wentropy_masked_pair, wentropy_masked_pair] at hsub
  rw [Finset.union_sdiff_of_subset hT] at hsub
  rw [show T' ∪ {i} = insert i T' from by
      rw [Finset.union_comm, ← Finset.insert_eq],
    show T ∪ {i} = insert i T from by
      rw [Finset.union_comm, ← Finset.insert_eq]] at hsub
  have hTe : tupleEntropy w X T = wentropy w (masked X T) := rfl
  linarith

end Tuple

end PMC
