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

end Entropy

end PMC
