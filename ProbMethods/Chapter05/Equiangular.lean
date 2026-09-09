import ProbMethods.Chapter05.HoeffdingBernoulli
import ProbMethods.Chapter02.CaroWei
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# §5.2 — Exponentially many approximately equiangular vectors (Theorem 5.2.1)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 5.2.1: for every `α ∈ (0,1)` and
`ε > 0` there is `c > 0` such that `ℝⁿ` contains at least `2^{cn}` unit vectors whose pairwise
inner products all lie in `[α - ε, α + ε]`.
-/

open Finset
open scoped symmDiff

namespace PMC

section Equiangular

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `pweight` at the constant `1/2` is the uniform weight: every subset gets `(1/2)^n`. -/
lemma pweight_half (S : Finset α) :
    pweight (fun _ : α => (1 / 2 : ℝ)) S = (1 / 2) ^ Fintype.card α := by
  have hS : #S ≤ Fintype.card α := by
    rw [← card_univ]; exact card_le_card (subset_univ _)
  have h : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [← bweight_eq_pweight, bweight, h, ← pow_add]
  congr 1
  omega

/-- The uniform measure of a family of subsets is its cardinality over `2^n`. -/
lemma sum_pweight_half (F : Finset (Finset α)) :
    ∑ S ∈ F, pweight (fun _ : α => (1 / 2 : ℝ)) S = #F * (1 / 2) ^ Fintype.card α := by
  rw [Finset.sum_congr rfl fun S _ => pweight_half S, Finset.sum_const, nsmul_eq_mul]

/-- **Two-sided Chernoff for a uniformly random subset.** At most `2 · 2ⁿ e^{-2t²/n}` of the
`2ⁿ` subsets of an `n`-element set have size deviating from `n/2` by more than `t`.

Both tails are `PMC.sum_pweight_ge_le` / `PMC.sum_pweight_le_le` at the constant `p = 1/2`,
whose mean is `∑ 1/2 = n/2`; `PMC.pweight_half` turns the weighted statement into a count. -/
theorem card_filter_card_dev_le {n : ℕ} (hcard : Fintype.card α = n) (hn : 0 < n)
    {t : ℝ} (ht : 0 < t) :
    (#((univ : Finset α).powerset.filter (fun S => t < |(#S : ℝ) - n / 2|)) : ℝ)
      ≤ 2 * 2 ^ n * Real.exp (-(2 * t ^ 2) / n) := by
  classical
  set p : α → ℝ := fun _ => (1 / 2 : ℝ) with hp
  have hp0 : ∀ i, 0 ≤ p i := fun i => by rw [hp]; norm_num
  have hp1 : ∀ i, p i ≤ 1 := fun i => by rw [hp]; norm_num
  have hmean : ∑ i : α, p i = (n : ℝ) / 2 := by
    rw [hp, Finset.sum_const, card_univ, hcard, nsmul_eq_mul]
    ring
  set E : Finset (Finset α) :=
    (univ : Finset α).powerset.filter (fun S => t < |(#S : ℝ) - n / 2|) with hE
  set Q1 : Finset (Finset α) :=
    (univ : Finset α).powerset.filter (fun S => (∑ i, p i) + t ≤ #S) with hQ1
  set Q2 : Finset (Finset α) :=
    (univ : Finset α).powerset.filter (fun S => (#S : ℝ) ≤ (∑ i, p i) - t) with hQ2
  have hnn : ∀ S : Finset α, 0 ≤ pweight p S := fun S => pweight_nonneg hp0 hp1 S
  -- the deviation event sits inside the union of the two tails
  have hsub : E ⊆ Q1 ∪ Q2 := by
    intro S hS
    rw [hE, mem_filter, mem_powerset] at hS
    rw [Finset.mem_union, hQ1, hQ2, mem_filter, mem_filter, mem_powerset, hmean]
    rcases abs_cases ((#S : ℝ) - (n : ℝ) / 2) with ⟨heq, -⟩ | ⟨heq, -⟩
    · exact Or.inl ⟨subset_univ _, by rw [heq] at hS; linarith [hS.2]⟩
    · exact Or.inr ⟨subset_univ _, by rw [heq] at hS; linarith [hS.2]⟩
  -- the union bound
  have hunion : ∑ S ∈ Q1 ∪ Q2, pweight p S
      ≤ (∑ S ∈ Q1, pweight p S) + ∑ S ∈ Q2, pweight p S := by
    have hdisj : Disjoint Q1 (Q2 \ Q1) :=
      Finset.disjoint_left.mpr fun a ha ha' => (Finset.mem_sdiff.mp ha').2 ha
    rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union hdisj]
    exact add_le_add le_rfl
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun S _ _ => hnn S)
  have hw : ∑ S ∈ E, pweight p S ≤ (∑ S ∈ Q1, pweight p S) + ∑ S ∈ Q2, pweight p S :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun S _ _ => hnn S) hunion
  have ht1 : ∑ S ∈ Q1, pweight p S ≤ Real.exp (-(2 * t ^ 2) / n) := by
    have h := sum_pweight_ge_le p hp0 hp1 ht (by rw [hcard]; exact hn)
    rw [hcard] at h
    exact h
  have ht2 : ∑ S ∈ Q2, pweight p S ≤ Real.exp (-(2 * t ^ 2) / n) := by
    have h := sum_pweight_le_le p hp0 hp1 ht (by rw [hcard]; exact hn)
    rw [hcard] at h
    exact h
  rw [sum_pweight_half, hcard] at hw
  -- clear the `(1/2)^n`
  have hkey : (#E : ℝ) * (1 / 2) ^ n ≤ 2 * Real.exp (-(2 * t ^ 2) / n) := by linarith
  have h2n : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
    rw [div_pow, one_pow]
    field_simp
  calc (#E : ℝ) = (#E : ℝ) * (1 / 2) ^ n * 2 ^ n := by rw [mul_assoc, h2n, mul_one]
    _ ≤ 2 * Real.exp (-(2 * t ^ 2) / n) * 2 ^ n :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 2 * 2 ^ n * Real.exp (-(2 * t ^ 2) / n) := by ring

/-! ### From the tail bound to a large far-apart family -/

/-- The **far-pair graph** on the subsets of `α`: `x ~ y` when the Hamming distance
`#(x ∆ y)` deviates from `n/2` by more than `t`.

Theorem 5.2.1 asks for a large family of subsets *no two* of which are far apart, i.e. a large
independent set in this graph. The notes get one by a union bound over the pairs of an
`m`-tuple of random subsets; here the same Chernoff input is fed to Caro–Wei (§2.3), which
needs only the *degrees* of this graph — and every degree is bounded by the same tail count,
because `y ↦ x ∆ y` is injective. -/
def farGraph (β : Type*) [Fintype β] [DecidableEq β] (t : ℝ) : SimpleGraph (Finset β) where
  Adj x y := x ≠ y ∧ t < |(#(x ∆ y) : ℝ) - Fintype.card β / 2|
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [symmDiff_comm]; exact h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

@[simp] lemma farGraph_adj (t : ℝ) (x y : Finset α) :
    (farGraph α t).Adj x y ↔ x ≠ y ∧ t < |(#(x ∆ y) : ℝ) - Fintype.card α / 2| := Iff.rfl

noncomputable instance (t : ℝ) : DecidableRel (farGraph α t).Adj := fun _ _ => Classical.dec _

/-- Every degree of the far-pair graph is at most the number of subsets whose size deviates
from `n/2` by more than `t`: `y ↦ x ∆ y` maps the neighbours of `x` injectively into them. -/
lemma degree_farGraph_le (t : ℝ) (x : Finset α) :
    (farGraph α t).degree x
      ≤ #((univ : Finset α).powerset.filter
          (fun S => t < |(#S : ℝ) - Fintype.card α / 2|)) := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn (fun y => x ∆ y) ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset, farGraph_adj] at hy
    simp only [Finset.mem_coe, mem_filter, mem_powerset]
    exact ⟨subset_univ _, hy.2⟩
  · intro y₁ _ y₂ _ h
    have h' := congrArg (fun z => x ∆ z) h
    simpa only [symmDiff_symmDiff_cancel_left] using h'

/-- **A large family of subsets at pairwise Hamming distance `n/2 ± t`.**

Caro–Wei (`PMC.exists_isIndepSet_caro_wei`) on `PMC.farGraph`, whose degrees are bounded by
the Chernoff count `PMC.card_filter_card_dev_le`: the `2ⁿ` vertices each have degree at most
`D ≤ 2 · 2ⁿ e^{-2t²/n}`, so there is an independent set of size at least `2ⁿ/(D+1)`. -/
theorem exists_far_family (hn : 0 < Fintype.card α) {t : ℝ} (ht : 0 < t) :
    ∃ F : Finset (Finset α),
      (2 : ℝ) ^ Fintype.card α
          / (2 * 2 ^ Fintype.card α * Real.exp (-(2 * t ^ 2) / Fintype.card α) + 1) ≤ #F ∧
      ∀ x ∈ F, ∀ y ∈ F, x ≠ y → |(#(x ∆ y) : ℝ) - Fintype.card α / 2| ≤ t := by
  classical
  set D : ℕ := #((univ : Finset α).powerset.filter
    (fun S => t < |(#S : ℝ) - Fintype.card α / 2|)) with hDdef
  obtain ⟨F, hind, hsum⟩ := exists_isIndepSet_caro_wei (farGraph α t)
  refine ⟨F, ?_, ?_⟩
  · -- every degree is at most `D`, so the Caro–Wei sum is at least `2ⁿ/(D+1)`
    have hDpos : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    have hlow : (2 : ℝ) ^ Fintype.card α / ((D : ℝ) + 1)
        ≤ ∑ v : Finset α, (1 : ℝ) / ((farGraph α t).degree v + 1) := by
      have hterm : ∀ v : Finset α, (1 : ℝ) / ((D : ℝ) + 1)
          ≤ (1 : ℝ) / ((farGraph α t).degree v + 1) := by
        intro v
        have hd : ((farGraph α t).degree v : ℝ) ≤ (D : ℝ) := by
          exact_mod_cast degree_farGraph_le t v
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      have := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset (Finset α))) => hterm v)
      rw [Finset.sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul] at this
      calc (2 : ℝ) ^ Fintype.card α / ((D : ℝ) + 1)
          = (2 : ℝ) ^ Fintype.card α * (1 / ((D : ℝ) + 1)) := by ring
        _ ≤ _ := by
            refine le_trans (le_of_eq ?_) this
            push_cast
            ring
    -- and `D` is at most the Chernoff bound
    have hD : (D : ℝ)
        ≤ 2 * 2 ^ Fintype.card α * Real.exp (-(2 * t ^ 2) / Fintype.card α) :=
      card_filter_card_dev_le rfl hn ht
    have hmono : (2 : ℝ) ^ Fintype.card α
        / (2 * 2 ^ Fintype.card α * Real.exp (-(2 * t ^ 2) / Fintype.card α) + 1)
        ≤ (2 : ℝ) ^ Fintype.card α / ((D : ℝ) + 1) :=
      div_le_div_of_nonneg_left (by positivity) hDpos (by linarith)
    linarith [le_trans hlow hsum]
  · intro x hx y hy hne
    have hnadj : ¬ (farGraph α t).Adj x y := hind (by simpa using hx) (by simpa using hy) hne
    rw [farGraph_adj, not_and] at hnadj
    exact not_lt.mp (hnadj hne)

/-- The far-family bound in exponential form: for `0 < δ ≤ 1/2` and any ground set large
enough that `log 3 ≤ δ²n`, there are at least `e^{δ²n}` subsets whose pairwise Hamming
distances all lie within `δn` of `n/2`.

The arithmetic: the Chernoff count is `D ≤ 2u` with `u = 2ⁿe^{-2δ²n} = e^{n(log 2 - 2δ²)}`,
and `δ ≤ 1/2` forces `2δ² ≤ 1/2 ≤ log 2`, so `u ≥ 1`, the denominator `2u + 1` is at most
`3u`, and `2ⁿ/(3u) = e^{2δ²n}/3 ≥ e^{δ²n}` once `e^{δ²n} ≥ 3`. -/
theorem exists_far_family_exp {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hbig : Real.log 3 ≤ δ ^ 2 * Fintype.card α) :
    ∃ F : Finset (Finset α),
      Real.exp (δ ^ 2 * Fintype.card α) ≤ #F ∧
      ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
        |(#(x ∆ y) : ℝ) - Fintype.card α / 2| ≤ δ * Fintype.card α := by
  classical
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hNpos : (0 : ℝ) < Fintype.card α := by
    by_contra hcon
    push_neg at hcon
    nlinarith [sq_nonneg δ]
  have hcardpos : 0 < Fintype.card α := Nat.cast_pos.mp hNpos
  have ht : 0 < δ * (Fintype.card α : ℝ) := by positivity
  obtain ⟨F, hcard, hfar⟩ := exists_far_family (α := α) hcardpos ht
  refine ⟨F, le_trans ?_ hcard, hfar⟩
  set N : ℝ := (Fintype.card α : ℝ) with hN
  -- `2ⁿ = e^{n log 2}`
  have h2n : (2 : ℝ) ^ Fintype.card α = Real.exp (Real.log 2 * N) := by
    rw [← Real.rpow_natCast (2 : ℝ) (Fintype.card α), Real.rpow_def_of_pos (by norm_num), hN]
  have hexp : Real.exp (-(2 * (δ * N) ^ 2) / N) = Real.exp (Real.log 2 * N + -(2 * δ ^ 2) * N)
      / Real.exp (Real.log 2 * N) := by
    rw [← Real.exp_sub]
    congr 1
    field_simp
    ring
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  -- `u := 2ⁿ e^{-2δ²n} = e^{n(log 2 - 2δ²)} ≥ 1`
  set u : ℝ := Real.exp (Real.log 2 * N + -(2 * δ ^ 2) * N) with hu
  have hu1 : 1 ≤ u := by
    have hstep : (0 : ℝ) ≤ Real.log 2 * N + -(2 * δ ^ 2) * N := by nlinarith [sq_nonneg δ]
    have h := Real.exp_le_exp.mpr hstep
    rwa [Real.exp_zero] at h
  have hupos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hfac : (2 : ℝ) ^ Fintype.card α * Real.exp (-(2 * (δ * N) ^ 2) / N) = u := by
    rw [hexp, h2n]
    field_simp
  -- the denominator is at most `3u`
  have hden : 2 * (2 : ℝ) ^ Fintype.card α * Real.exp (-(2 * (δ * N) ^ 2) / N) + 1 ≤ 3 * u := by
    have : 2 * (2 : ℝ) ^ Fintype.card α * Real.exp (-(2 * (δ * N) ^ 2) / N) = 2 * u := by
      rw [← hfac]; ring
    rw [this]
    linarith
  have hdenpos : (0 : ℝ) < 2 * (2 : ℝ) ^ Fintype.card α
      * Real.exp (-(2 * (δ * N) ^ 2) / N) + 1 := by positivity
  refine le_trans ?_ (div_le_div_of_nonneg_left (by positivity) hdenpos hden)
  -- `2ⁿ/(3u) = e^{2δ²n}/3 ≥ e^{δ²n}`
  rw [h2n, le_div_iff₀ (by positivity)]
  have e1 : Real.exp (δ ^ 2 * N) * (3 * u) = 3 * Real.exp (Real.log 2 * N - δ ^ 2 * N) := by
    rw [hu, mul_comm, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have e2 : Real.exp (Real.log 2 * N - δ ^ 2 * N) * Real.exp (δ ^ 2 * N)
      = Real.exp (Real.log 2 * N) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : (3 : ℝ) ≤ Real.exp (δ ^ 2 * N) := by
    rw [← Real.exp_log (show (0 : ℝ) < 3 by norm_num)]
    exact Real.exp_le_exp.mpr hbig
  rw [e1]
  nlinarith [Real.exp_pos (Real.log 2 * N - δ ^ 2 * N)]

/-! ### From a far-apart family to nearly equiangular unit vectors -/

/-- The product of the two sign patterns is the sign pattern of the symmetric difference. -/
lemma sign_mul_sign {n : ℕ} (x y : Finset (Fin n)) (i : Fin n) :
    (if i ∈ x then (-1 : ℝ) else 1) * (if i ∈ y then (-1 : ℝ) else 1)
      = if i ∈ x ∆ y then (-1 : ℝ) else 1 := by
  by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;> simp [Finset.mem_symmDiff, hx, hy]

/-- A `±1` sign pattern sums to `n - 2#S`. -/
lemma sum_sign {n : ℕ} (S : Finset (Fin n)) :
    ∑ i : Fin n, (if i ∈ S then (-1 : ℝ) else 1) = (n : ℝ) - 2 * #S := by
  have h : ∀ i : Fin n, (if i ∈ S then (-1 : ℝ) else 1)
      = 1 - 2 * (if i ∈ S then (1 : ℝ) else 0) := by
    intro i; split <;> ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Finset.sum_boole, Finset.filter_univ_mem]

/-- The unit vector attached to a subset `x ⊆ [n]`: a constant first coordinate `√a` followed
by the `±√((1-a)/n)` sign pattern of `x`.

Its squared norm is `a + n · (1-a)/n = 1`, and two of them have inner product
`a + (1-a)(1 - 2#(x ∆ y)/n)`, so a Hamming distance close to `n/2` is exactly an inner
product close to `a`. The constant coordinate is where the extra dimension goes: `n` signs
plus one constant coordinate live in `ℝ^{n+1}`. -/
noncomputable def eqVec (n : ℕ) (a : ℝ) (x : Finset (Fin n)) : Fin (n + 1) → ℝ :=
  Fin.cons (Real.sqrt a) fun i => Real.sqrt ((1 - a) / n) * (if i ∈ x then -1 else 1)

/-- `PMC.eqVec` is a unit vector. -/
lemma sum_eqVec_sq {n : ℕ} (hn : 0 < n) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (x : Finset (Fin n)) : ∑ k, eqVec n a x k ^ 2 = 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn : (0 : ℝ) ≤ (1 - a) / n := div_nonneg (by linarith) hnR.le
  rw [Fin.sum_univ_succ]
  simp only [eqVec, Fin.cons_zero, Fin.cons_succ]
  have h2 : ∀ i : Fin n,
      (Real.sqrt ((1 - a) / n) * (if i ∈ x then (-1 : ℝ) else 1)) ^ 2 = (1 - a) / n := by
    intro i
    rw [mul_pow, Real.sq_sqrt hnn]
    split <;> norm_num
  rw [Real.sq_sqrt ha0, Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The inner product of two `PMC.eqVec`s in terms of the Hamming distance. -/
lemma sum_eqVec_mul {n : ℕ} (hn : 0 < n) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (x y : Finset (Fin n)) :
    ∑ k, eqVec n a x k * eqVec n a y k = a + (1 - a) * (1 - 2 * #(x ∆ y) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn : (0 : ℝ) ≤ (1 - a) / n := div_nonneg (by linarith) hnR.le
  rw [Fin.sum_univ_succ]
  simp only [eqVec, Fin.cons_zero, Fin.cons_succ]
  have hterm : ∀ i : Fin n,
      Real.sqrt ((1 - a) / n) * (if i ∈ x then (-1 : ℝ) else 1) *
        (Real.sqrt ((1 - a) / n) * (if i ∈ y then (-1 : ℝ) else 1))
        = (1 - a) / n * (if i ∈ x ∆ y then (-1 : ℝ) else 1) := by
    intro i
    calc Real.sqrt ((1 - a) / n) * (if i ∈ x then (-1 : ℝ) else 1) *
        (Real.sqrt ((1 - a) / n) * (if i ∈ y then (-1 : ℝ) else 1))
        = Real.sqrt ((1 - a) / n) * Real.sqrt ((1 - a) / n) *
            ((if i ∈ x then (-1 : ℝ) else 1) * (if i ∈ y then (-1 : ℝ) else 1)) := by ring
      _ = (1 - a) / n * (if i ∈ x ∆ y then (-1 : ℝ) else 1) := by
          rw [Real.mul_self_sqrt hnn, sign_mul_sign]
  rw [Real.mul_self_sqrt ha0, Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum,
    sum_sign]
  field_simp

/-- Distinct subsets give distinct vectors. -/
lemma eqVec_injective {n : ℕ} (hn : 0 < n) {a : ℝ} (ha1 : a < 1) :
    Function.Injective (eqVec n a) := by
  intro x y h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < Real.sqrt ((1 - a) / n) :=
    Real.sqrt_pos.mpr (div_pos (by linarith) hnR)
  ext i
  have hi := congrFun h i.succ
  simp only [eqVec, Fin.cons_succ] at hi
  have h' := mul_left_cancel₀ (ne_of_gt hpos) hi
  constructor
  · intro hx
    by_contra hy
    rw [if_pos hx, if_neg hy] at h'
    norm_num at h'
  · intro hy
    by_contra hx
    rw [if_neg hx, if_pos hy] at h'
    norm_num at h'

/-- **Theorem 5.2.1** (exponentially many approximately equiangular vectors).

For every `a ∈ (0,1)` and every `ε > 0` there is `c > 0` such that for all large `N` the space
`ℝ^N` contains at least `2^{cN}` unit vectors whose pairwise inner products all lie in
`[a - ε, a + ε]`.

The notes say "for every `n`", which is false at small `n`: the only unit vectors in `ℝ¹` are
`±1`, with inner products `±1`, so for `a = 1/2` and `ε = 1/100` every admissible family has
one element, while `2^{c·1} > 1`. The `∀ N ≥ N₀` form is what the argument gives.

The construction is the notes': biased `±1` coordinates, rescaled. Here the bias is moved into
a single constant coordinate — `PMC.eqVec` — which leaves the remaining `n` coordinates
*unbiased*, so the whole probabilistic content is the balanced two-sided Chernoff bound
`PMC.card_filter_card_dev_le` and the pairwise structure is handled by
`PMC.exists_far_family_exp`. -/
theorem exists_nearly_equiangular {a ε : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ F : Finset (Fin N → ℝ),
      (2 : ℝ) ^ (c * (N : ℝ)) ≤ #F ∧
      (∀ v ∈ F, ∑ k, v k ^ 2 = 1) ∧
      ∀ v ∈ F, ∀ w ∈ F, v ≠ w → |(∑ k, v k * w k) - a| ≤ ε := by
  classical
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set δ : ℝ := min (1 / 2) (ε / (2 * (1 - a))) with hδdef
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδeps : δ ≤ ε / (2 * (1 - a)) := min_le_right _ _
  refine ⟨δ ^ 2 / (2 * Real.log 2), div_pos (pow_pos hδpos 2) (by linarith),
    ⌈Real.log 3 / δ ^ 2⌉₊ + 2, ?_⟩
  intro N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hnceil : ⌈Real.log 3 / δ ^ 2⌉₊ ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hbig : Real.log 3 ≤ δ ^ 2 * n := by
    have hceil : (⌈Real.log 3 / δ ^ 2⌉₊ : ℝ) ≤ n := by exact_mod_cast hnceil
    have hle : Real.log 3 / δ ^ 2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) hceil
    rw [div_le_iff₀ (by positivity)] at hle
    linarith
  obtain ⟨F₀, hcard, hfar⟩ :=
    exists_far_family_exp (α := Fin n) hδpos hδhalf (by rwa [Fintype.card_fin])
  rw [Fintype.card_fin] at hcard hfar
  refine ⟨F₀.image (eqVec n a), ?_, ?_, ?_⟩
  · -- `2^{c(n+1)} = e^{δ²(n+1)/2} ≤ e^{δ²n} ≤ #F₀`
    rw [Finset.card_image_of_injective _ (eqVec_injective hn1 ha1)]
    refine le_trans ?_ hcard
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.exp_le_exp]
    have hid : Real.log 2 * (δ ^ 2 / (2 * Real.log 2) * ((n : ℝ) + 1))
        = δ ^ 2 * ((n : ℝ) + 1) / 2 := by
      field_simp
    push_cast
    rw [hid]
    nlinarith [mul_nonneg (sq_nonneg δ) (by linarith : (0 : ℝ) ≤ (n : ℝ) - 1)]
  · intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨x, -, rfl⟩ := hv
    exact sum_eqVec_sq hn1 ha0.le ha1.le x
  · intro v hv w hw hne
    rw [Finset.mem_image] at hv hw
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨y, hy, rfl⟩ := hw
    have hxy : x ≠ y := fun h => hne (by rw [h])
    rw [sum_eqVec_mul hn1 ha0.le ha1.le]
    have hd := hfar x hx y hy hxy
    have hsimp : a + (1 - a) * (1 - 2 * (#(x ∆ y) : ℝ) / n) - a
        = (1 - a) * (1 - 2 * (#(x ∆ y) : ℝ) / n) := by ring
    rw [hsimp, abs_mul, abs_of_pos h1a]
    -- `|1 - 2D/n| = (2/n)|D - n/2| ≤ 2δ`
    have hrw : 1 - 2 * (#(x ∆ y) : ℝ) / n = (-2 / n) * ((#(x ∆ y) : ℝ) - n / 2) := by
      field_simp
      ring
    have habs : |(-2 : ℝ) / n| = 2 / n := by
      rw [abs_div, abs_of_pos hnR]
      norm_num
    have hkey : |1 - 2 * (#(x ∆ y) : ℝ) / n| ≤ 2 * δ := by
      rw [hrw, abs_mul, habs]
      calc 2 / (n : ℝ) * |(#(x ∆ y) : ℝ) - n / 2| ≤ 2 / (n : ℝ) * (δ * n) :=
            mul_le_mul_of_nonneg_left hd (by positivity)
        _ = 2 * δ := by field_simp
    have hfin : δ * (2 * (1 - a)) ≤ ε := (le_div_iff₀ (by positivity)).mp hδeps
    calc (1 - a) * |1 - 2 * (#(x ∆ y) : ℝ) / n| ≤ (1 - a) * (2 * δ) :=
          mul_le_mul_of_nonneg_left hkey h1a.le
      _ ≤ ε := by linarith

end Equiangular




end PMC
