import ProbMethods.Chapter09.Hoeffding
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# §9.1 — the bounded differences inequality

Theorem 9.1.1 (McDiarmid): if `f` on a product of finite sets changes by at most `cᵢ` when
coordinate `i` alone is changed, then `f` concentrates around its mean,

    P(f ≥ E f + t) ≤ exp (-2t² / ∑ cᵢ²).

**This is the one part of Chapter 9 that lives naturally in the finite framework.** The
martingale is concrete: `PMC.avgLast` averages out the last coordinate, and the Doob
increments are the successive differences. No filtration, no conditional expectation
operator, no `MeasureTheory` — the induction is on the number of coordinates, with
`Fin.snoc` splitting the product.

Hoeffding's lemma (task #47, `PMC.wmean_exp_le_of_mem_Icc`) enters as an explicit hypothesis
`hoeffdingUnif_holds`, in exactly the shape needed: its instance at the uniform weight on one coordinate.
So everything here is `sorry`-free, and the single missing input is visible in the statements.
-/

open Finset

namespace PMC

section BoundedDifferences

variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]

/-- The average of `f` over the uniform product measure on `Fin N → β`. -/
noncomputable def pAvg {N : ℕ} (f : (Fin N → β) → ℝ) : ℝ :=
  (∑ x : Fin N → β, f x) / (Fintype.card β : ℝ) ^ N

/-- Averaging out the last coordinate: the Doob martingale's step. -/
noncomputable def avgLast {N : ℕ} (f : (Fin (N + 1) → β) → ℝ) : (Fin N → β) → ℝ :=
  fun y => (∑ a : β, f (Fin.snoc y a)) / (Fintype.card β : ℝ)

/-- `Fin.snoc` splits the product off its last coordinate. -/
def snocEquiv (N : ℕ) (β : Type*) : ((Fin N → β) × β) ≃ (Fin (N + 1) → β) where
  toFun p := Fin.snoc p.1 p.2
  invFun x := (fun i => x i.castSucc, x (Fin.last N))
  left_inv := by
    intro p
    ext
    · simp only [Fin.snoc_castSucc]
    · simp only [Fin.snoc_last]
  right_inv := by
    intro x
    exact Fin.snoc_init_self x

lemma sum_snoc {N : ℕ} (F : (Fin (N + 1) → β) → ℝ) :
    ∑ x : Fin (N + 1) → β, F x = ∑ y : Fin N → β, ∑ a : β, F (Fin.snoc y a) := by
  rw [← Fintype.sum_equiv (snocEquiv N β) (fun p => F (Fin.snoc p.1 p.2)) F (fun p => rfl),
    Fintype.sum_prod_type]

lemma card_pos_pow (N : ℕ) : (0 : ℝ) < (Fintype.card β : ℝ) ^ N := by
  have : (0 : ℝ) < Fintype.card β := by
    have := Fintype.card_pos (α := β)
    exact_mod_cast this
  positivity

/-- **Averaging out the last coordinate preserves the mean.** -/
lemma pAvg_avgLast {N : ℕ} (f : (Fin (N + 1) → β) → ℝ) : pAvg (avgLast f) = pAvg f := by
  have hc : (0 : ℝ) < Fintype.card β := by
    have := Fintype.card_pos (α := β); exact_mod_cast this
  simp only [pAvg, avgLast]
  rw [sum_snoc f, ← Finset.sum_div, div_div, pow_succ]
  ring_nf

/-- The average over the product, split off its last coordinate. -/
lemma pAvg_succ {N : ℕ} (F : (Fin (N + 1) → β) → ℝ) :
    pAvg F = (∑ y : Fin N → β, (∑ a : β, F (Fin.snoc y a)) / Fintype.card β)
      / (Fintype.card β : ℝ) ^ N := by
  simp only [pAvg]
  rw [sum_snoc F, ← Finset.sum_div, div_div, pow_succ]
  ring_nf

/-! ### Bounded differences -/

/-- `f` has bounded differences with constants `c`: changing coordinate `i` alone moves `f`
by at most `c i`. -/
def BddDiff {N : ℕ} (f : (Fin N → β) → ℝ) (c : Fin N → ℝ) : Prop :=
  ∀ (i : Fin N) (x y : Fin N → β), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i

lemma BddDiff.nonneg {N : ℕ} {f : (Fin N → β) → ℝ} {c : Fin N → ℝ} (hf : BddDiff f c)
    (i : Fin N) : 0 ≤ c i := by
  have := hf i (fun _ => Classical.arbitrary β) (fun _ => Classical.arbitrary β) (fun _ _ => rfl)
  simpa using this

/-- **Averaging out the last coordinate preserves bounded differences**, with the same
constants — the property the Doob induction needs in order to recurse. -/
lemma BddDiff.avgLast {N : ℕ} {f : (Fin (N + 1) → β) → ℝ} {c : Fin (N + 1) → ℝ}
    (hf : BddDiff f c) : BddDiff (PMC.avgLast f) (fun i => c i.castSucc) := by
  intro i y y' hyy'
  have hc : (0 : ℝ) < Fintype.card β := by
    have := Fintype.card_pos (α := β); exact_mod_cast this
  have hsnoc : ∀ a : β, |f (Fin.snoc y a) - f (Fin.snoc y' a)| ≤ c i.castSucc := by
    intro a
    refine hf i.castSucc _ _ ?_
    intro j hj
    revert hj
    refine Fin.lastCases ?_ ?_ j
    · intro _
      simp only [Fin.snoc_last]
    · intro j' hj'
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      refine hyy' j' ?_
      intro hcon
      exact hj' (by rw [hcon])
  have hdiff : PMC.avgLast f y - PMC.avgLast f y'
      = (∑ a : β, (f (Fin.snoc y a) - f (Fin.snoc y' a))) / Fintype.card β := by
    simp only [PMC.avgLast]
    rw [div_sub_div_same, ← Finset.sum_sub_distrib]
  rw [hdiff, abs_div, abs_of_pos hc]
  rw [div_le_iff₀ hc]
  calc |∑ a : β, (f (Fin.snoc y a) - f (Fin.snoc y' a))|
      ≤ ∑ a : β, |f (Fin.snoc y a) - f (Fin.snoc y' a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : β, c i.castSucc := Finset.sum_le_sum fun a _ => hsnoc a
    _ = c i.castSucc * Fintype.card β := by
        rw [Finset.sum_const, card_univ, nsmul_eq_mul]
        ring

/-- The last-coordinate increment is centred and confined to an interval of length at most
`c (last N)` — exactly Hoeffding's lemma's hypotheses. -/
lemma exists_bounds_last {N : ℕ} (f : (Fin (N + 1) → β) → ℝ) {c : Fin (N + 1) → ℝ}
    (hf : BddDiff f c) (y : Fin N → β) :
    ∃ a b : ℝ, (∀ e : β, f (Fin.snoc y e) - PMC.avgLast f y ∈ Set.Icc a b) ∧
      b - a ≤ c (Fin.last N) := by
  classical
  have hne : (univ : Finset β).Nonempty := Finset.univ_nonempty
  set lo : ℝ := (univ : Finset β).inf' hne (fun e => f (Fin.snoc y e)) with hlo
  set hi : ℝ := (univ : Finset β).sup' hne (fun e => f (Fin.snoc y e)) with hhi
  refine ⟨lo - PMC.avgLast f y, hi - PMC.avgLast f y, ?_, ?_⟩
  · intro e
    refine ⟨?_, ?_⟩
    · have := Finset.inf'_le (fun e => f (Fin.snoc y e)) (mem_univ e)
      rw [← hlo] at this
      linarith
    · have := Finset.le_sup' (fun e => f (Fin.snoc y e)) (mem_univ e)
      rw [← hhi] at this
      linarith
  · -- the spread is attained, and any two last coordinates differ by at most `c (last N)`
    obtain ⟨e₁, -, he₁⟩ := Finset.exists_mem_eq_inf' hne (fun e => f (Fin.snoc y e))
    obtain ⟨e₂, -, he₂⟩ := Finset.exists_mem_eq_sup' hne (fun e => f (Fin.snoc y e))
    have hbd : |f (Fin.snoc y e₂) - f (Fin.snoc y e₁)| ≤ c (Fin.last N) := by
      refine hf (Fin.last N) _ _ ?_
      intro j hj
      revert hj
      refine Fin.lastCases ?_ ?_ j
      · intro hcon
        exact absurd rfl hcon
      · intro j' _
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    have : hi - lo = f (Fin.snoc y e₂) - f (Fin.snoc y e₁) := by rw [← he₁, ← he₂]
    rw [show hi - PMC.avgLast f y - (lo - PMC.avgLast f y) = hi - lo from by ring, this]
    exact le_trans (le_abs_self _) hbd


/-! ### The moment generating function -/

/-- Hoeffding's lemma at the uniform weight on one coordinate — the instance of task #47
(`PMC.wmean_exp_le_of_mem_Icc`) that the Doob induction consumes. -/
def HoeffdingUnif (β : Type*) [Fintype β] [DecidableEq β] : Prop :=
  ∀ (Z : β → ℝ) (a b : ℝ), (∀ e, Z e ∈ Set.Icc a b) → (∑ e, Z e) = 0 → ∀ lam : ℝ,
    (∑ e, Real.exp (lam * Z e)) / Fintype.card β ≤ Real.exp (lam ^ 2 * (b - a) ^ 2 / 8)

/-- Hoeffding's lemma for an arbitrary finite weight, at the uniform weight on one coordinate,
is exactly `PMC.HoeffdingUnif`. -/
lemma hoeffdingUnif_of_hoeffding
    (h : ∀ (w : β → ℝ), (∀ e, 0 ≤ w e) → (∑ e, w e) = 1 → ∀ (Z : β → ℝ) (a b : ℝ),
      (∀ e, Z e ∈ Set.Icc a b) → wmean w Z = 0 → ∀ lam : ℝ,
      wmean w (fun e => Real.exp (lam * Z e)) ≤ Real.exp (lam ^ 2 * (b - a) ^ 2 / 8)) :
    HoeffdingUnif β := by
  intro Z a b hmem hzero lam
  have hc : (0 : ℝ) < Fintype.card β := by
    have := Fintype.card_pos (α := β); exact_mod_cast this
  have hw : ∀ e : β, (0 : ℝ) ≤ 1 / Fintype.card β := fun _ => by positivity
  have hsum : ∑ _e : β, (1 : ℝ) / Fintype.card β = 1 := by
    rw [Finset.sum_const, card_univ, nsmul_eq_mul, mul_one_div, div_self (ne_of_gt hc)]
  have hmean : wmean (fun _ : β => (1 : ℝ) / Fintype.card β) Z = 0 := by
    rw [wmean, ← Finset.mul_sum, hzero, mul_zero]
  have hres := h (fun _ : β => 1 / Fintype.card β) hw hsum Z a b hmem hmean lam
  rw [wmean, ← Finset.mul_sum] at hres
  calc (∑ e, Real.exp (lam * Z e)) / Fintype.card β
      = 1 / (Fintype.card β : ℝ) * ∑ e, Real.exp (lam * Z e) := by ring
    _ ≤ Real.exp (lam ^ 2 * (b - a) ^ 2 / 8) := hres


/-- **`PMC.HoeffdingUnif` holds.** `PMC.wmean_exp_le_of_mem_Icc` — Hoeffding's lemma in the
finite framework, itself the measure bridge applied to Mathlib's sub-Gaussian machinery —
specialises to the uniform weight on one coordinate.

This is why nothing below carries a Hoeffding hypothesis: §9.1's and §9.3's theorems are
unconditional, as the notes state them. -/
theorem hoeffdingUnif_holds : HoeffdingUnif β :=
  hoeffdingUnif_of_hoeffding fun w hw hsum Z a b hmem hmean lam =>
    wmean_exp_le_of_mem_Icc hw hsum Z hmem hmean lam


/-- **The sub-Gaussian moment bound for a function with bounded differences.**

`E[exp (λ (f - E f))] ≤ exp (λ² ∑ cᵢ² / 8)`, by induction on the number of coordinates: peel
the last one, apply Hoeffding's lemma to its centred increment, and recurse on the average
`PMC.avgLast f`, which has the same bounded-difference constants. -/
theorem pAvg_exp_le {N : ℕ} (f : (Fin N → β) → ℝ) (c : Fin N → ℝ)
    (hf : BddDiff f c) (lam : ℝ) :
    pAvg (fun x => Real.exp (lam * (f x - pAvg f)))
      ≤ Real.exp (lam ^ 2 * (∑ i, c i ^ 2) / 8) := by
  classical
  induction N with
  | zero =>
      -- one point: `f` equals its own mean
      have hone : (univ : Finset (Fin 0 → β)) = {fun i => Fin.elim0 i} := by
        ext x
        simp only [mem_univ, Finset.mem_singleton, true_iff]
        funext i
        exact Fin.elim0 i
      have hmean : pAvg f = f (fun i => Fin.elim0 i) := by
        rw [pAvg, hone, Finset.sum_singleton, pow_zero, div_one]
      rw [pAvg, hone, Finset.sum_singleton, pow_zero, div_one, hmean, sub_self, mul_zero,
        Real.exp_zero]
      simp
  | succ N ih =>
      have hc : (0 : ℝ) < Fintype.card β := by
        have := Fintype.card_pos (α := β); exact_mod_cast this
      set g : (Fin N → β) → ℝ := PMC.avgLast f with hgdef
      have hg : BddDiff g (fun i => c i.castSucc) := hf.avgLast
      have hgmean : pAvg g = pAvg f := pAvg_avgLast f
      -- the inner average over the last coordinate, for each prefix
      have hinner : ∀ y : Fin N → β,
          (∑ a : β, Real.exp (lam * (f (Fin.snoc y a) - pAvg f))) / Fintype.card β
            ≤ Real.exp (lam ^ 2 * c (Fin.last N) ^ 2 / 8)
              * Real.exp (lam * (g y - pAvg f)) := by
        intro y
        obtain ⟨a₀, b₀, hmem, hspread⟩ := exists_bounds_last f hf y
        have hzero : (∑ e : β, (f (Fin.snoc y e) - g y)) = 0 := by
          simp only [hgdef, PMC.avgLast]
          rw [Finset.sum_sub_distrib, Finset.sum_const, card_univ, nsmul_eq_mul]
          field_simp
          ring
        have hH := hoeffdingUnif_holds (fun e => f (Fin.snoc y e) - g y) a₀ b₀ hmem hzero lam
        -- split the exponent at `g y`
        have hsplit : ∀ a : β, Real.exp (lam * (f (Fin.snoc y a) - pAvg f))
            = Real.exp (lam * (f (Fin.snoc y a) - g y)) * Real.exp (lam * (g y - pAvg f)) := by
          intro a
          rw [← Real.exp_add]
          congr 1
          ring
        rw [Finset.sum_congr rfl fun a _ => hsplit a, ← Finset.sum_mul,
          show (∑ a : β, Real.exp (lam * (f (Fin.snoc y a) - g y)))
              * Real.exp (lam * (g y - pAvg f)) / Fintype.card β
            = Real.exp (lam * (g y - pAvg f))
              * ((∑ a : β, Real.exp (lam * (f (Fin.snoc y a) - g y))) / Fintype.card β) from by
            ring,
          show Real.exp (lam ^ 2 * c (Fin.last N) ^ 2 / 8) * Real.exp (lam * (g y - pAvg f))
            = Real.exp (lam * (g y - pAvg f))
              * Real.exp (lam ^ 2 * c (Fin.last N) ^ 2 / 8) from by ring]
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
        refine le_trans hH ?_
        refine Real.exp_le_exp.mpr ?_
        have hsq : (b₀ - a₀) ^ 2 ≤ c (Fin.last N) ^ 2 := by
          have h0 : 0 ≤ b₀ - a₀ := by
            have := hmem (Classical.arbitrary β)
            rw [Set.mem_Icc] at this
            linarith [this.1, this.2]
          exact pow_le_pow_left₀ h0 hspread 2
        have hlam2 : 0 ≤ lam ^ 2 := sq_nonneg lam
        have : lam ^ 2 * (b₀ - a₀) ^ 2 ≤ lam ^ 2 * c (Fin.last N) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hlam2
        linarith
      -- assemble the two factors
      rw [pAvg_succ (fun x : Fin (N + 1) → β => Real.exp (lam * (f x - pAvg f)))]
      have hstep : (∑ y : Fin N → β,
            (∑ a : β, Real.exp (lam * (f (Fin.snoc y a) - pAvg f))) / Fintype.card β)
          / (Fintype.card β : ℝ) ^ N
          ≤ Real.exp (lam ^ 2 * c (Fin.last N) ^ 2 / 8)
            * pAvg (fun y => Real.exp (lam * (g y - pAvg g))) := by
        rw [hgmean]
        have h1 : (∑ y : Fin N → β,
              (∑ a : β, Real.exp (lam * (f (Fin.snoc y a) - pAvg f))) / Fintype.card β)
            ≤ ∑ y : Fin N → β, Real.exp (lam ^ 2 * c (Fin.last N) ^ 2 / 8)
              * Real.exp (lam * (g y - pAvg f)) :=
          Finset.sum_le_sum fun y _ => hinner y
        have h2 : (∑ y : Fin N → β, Real.exp (lam ^ 2 * c (Fin.last N) ^ 2 / 8)
              * Real.exp (lam * (g y - pAvg f))) / (Fintype.card β : ℝ) ^ N
            = Real.exp (lam ^ 2 * c (Fin.last N) ^ 2 / 8)
              * pAvg (fun y => Real.exp (lam * (g y - pAvg f))) := by
          rw [← Finset.mul_sum,
            show pAvg (fun y : Fin N → β => Real.exp (lam * (g y - pAvg f)))
              = (∑ y : Fin N → β, Real.exp (lam * (g y - pAvg f)))
                / (Fintype.card β : ℝ) ^ N from rfl,
            mul_div_assoc]
        rw [← h2]
        exact div_le_div_of_nonneg_right h1 (le_of_lt (card_pos_pow N))
      refine le_trans hstep ?_
      have hih := ih g (fun i => c i.castSucc) hg
      calc Real.exp (lam ^ 2 * c (Fin.last N) ^ 2 / 8)
            * pAvg (fun y => Real.exp (lam * (g y - pAvg g)))
          ≤ Real.exp (lam ^ 2 * c (Fin.last N) ^ 2 / 8)
            * Real.exp (lam ^ 2 * (∑ i : Fin N, c i.castSucc ^ 2) / 8) :=
            mul_le_mul_of_nonneg_left hih (le_of_lt (Real.exp_pos _))
        _ = Real.exp (lam ^ 2 * (∑ i : Fin (N + 1), c i ^ 2) / 8) := by
            rw [← Real.exp_add, Fin.sum_univ_castSucc]
            congr 1
            ring


/-! ### Theorem 9.1.1 -/

/-- **The bounded differences inequality** (Zhao, Theorem 9.1.1; McDiarmid). If changing one
coordinate `i` moves `f` by at most `cᵢ`, then at most an `exp(-2t²/∑cᵢ²)` fraction of the
product exceeds the mean by `t`:

    #{x : f x ≥ E f + t} ≤ |β|ᴺ · exp (-2t² / ∑ cᵢ²).

Dividing by `|β|ᴺ` gives the notes' `P(f ≥ E f + t) ≤ exp(-2t²/∑cᵢ²)`.

Markov applied to the moment generating function of `PMC.pAvg_exp_le`, at the optimal
`λ = 4t/∑cᵢ²`. Hoeffding's lemma enters through `PMC.hoeffdingUnif_holds`, so the statement
is unconditional. -/
theorem card_filter_ge_le {N : ℕ} (f : (Fin N → β) → ℝ)
    (c : Fin N → ℝ) (hf : BddDiff f c) {t : ℝ} (ht : 0 < t) (hS : 0 < ∑ i, c i ^ 2) :
    (#((univ : Finset (Fin N → β)).filter fun x => pAvg f + t ≤ f x) : ℝ)
      ≤ (Fintype.card β : ℝ) ^ N * Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2) := by
  classical
  set S : ℝ := ∑ i, c i ^ 2 with hSdef
  set lam : ℝ := 4 * t / S with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hcard : (0 : ℝ) < (Fintype.card β : ℝ) ^ N := card_pos_pow N
  -- Markov: every point of the bad set contributes at least `exp (λ t)`
  have hmarkov : (#((univ : Finset (Fin N → β)).filter fun x => pAvg f + t ≤ f x) : ℝ)
      * Real.exp (lam * t)
      ≤ ∑ x : Fin N → β, Real.exp (lam * (f x - pAvg f)) := by
    calc (#((univ : Finset (Fin N → β)).filter fun x => pAvg f + t ≤ f x) : ℝ)
          * Real.exp (lam * t)
        = ∑ _x ∈ (univ : Finset (Fin N → β)).filter fun x => pAvg f + t ≤ f x,
            Real.exp (lam * t) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ (univ : Finset (Fin N → β)).filter fun x => pAvg f + t ≤ f x,
            Real.exp (lam * (f x - pAvg f)) := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [mem_filter] at hx
          refine Real.exp_le_exp.mpr ?_
          have := hx.2
          nlinarith [hlam.le]
      _ ≤ ∑ x : Fin N → β, Real.exp (lam * (f x - pAvg f)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun x _ _ => le_of_lt (Real.exp_pos _))
  -- the total is the average times the size of the product
  have htotal : ∑ x : Fin N → β, Real.exp (lam * (f x - pAvg f))
      = (Fintype.card β : ℝ) ^ N * pAvg (fun x => Real.exp (lam * (f x - pAvg f))) := by
    rw [show pAvg (fun x : Fin N → β => Real.exp (lam * (f x - pAvg f)))
        = (∑ x : Fin N → β, Real.exp (lam * (f x - pAvg f)))
          / (Fintype.card β : ℝ) ^ N from rfl]
    field_simp
  have hmgf := pAvg_exp_le f c hf lam
  -- combine, then read off the optimal exponent
  have hchain : (#((univ : Finset (Fin N → β)).filter fun x => pAvg f + t ≤ f x) : ℝ)
      * Real.exp (lam * t)
      ≤ (Fintype.card β : ℝ) ^ N * Real.exp (lam ^ 2 * S / 8) := by
    calc (#((univ : Finset (Fin N → β)).filter fun x => pAvg f + t ≤ f x) : ℝ)
          * Real.exp (lam * t)
        ≤ ∑ x : Fin N → β, Real.exp (lam * (f x - pAvg f)) := hmarkov
      _ = (Fintype.card β : ℝ) ^ N * pAvg (fun x => Real.exp (lam * (f x - pAvg f))) := htotal
      _ ≤ (Fintype.card β : ℝ) ^ N * Real.exp (lam ^ 2 * S / 8) :=
          mul_le_mul_of_nonneg_left hmgf (le_of_lt hcard)
  have hexp : Real.exp (lam ^ 2 * S / 8) / Real.exp (lam * t)
      = Real.exp (-(2 * t ^ 2) / S) := by
    rw [← Real.exp_sub]
    congr 1
    rw [hlamdef]
    field_simp
    ring
  rw [← le_div_iff₀ (Real.exp_pos _)] at hchain
  calc (#((univ : Finset (Fin N → β)).filter fun x => pAvg f + t ≤ f x) : ℝ)
      ≤ (Fintype.card β : ℝ) ^ N * Real.exp (lam ^ 2 * S / 8) / Real.exp (lam * t) := hchain
    _ = (Fintype.card β : ℝ) ^ N * Real.exp (-(2 * t ^ 2) / S) := by
        rw [mul_div_assoc, hexp]


lemma pAvg_neg {N : ℕ} (f : (Fin N → β) → ℝ) : pAvg (fun x => -f x) = -pAvg f := by
  simp only [pAvg]
  rw [Finset.sum_neg_distrib, neg_div]

lemma BddDiff.neg {N : ℕ} {f : (Fin N → β) → ℝ} {c : Fin N → ℝ} (hf : BddDiff f c) :
    BddDiff (fun x => -f x) c := by
  intro i x y hxy
  have := hf i x y hxy
  rw [show -f x - -f y = -(f x - f y) from by ring, abs_neg]
  exact this

/-- **The lower tail**, by applying the upper tail to `-f`. The notes state both. -/
theorem card_filter_le_le {N : ℕ} (f : (Fin N → β) → ℝ)
    (c : Fin N → ℝ) (hf : BddDiff f c) {t : ℝ} (ht : 0 < t) (hS : 0 < ∑ i, c i ^ 2) :
    (#((univ : Finset (Fin N → β)).filter fun x => f x ≤ pAvg f - t) : ℝ)
      ≤ (Fintype.card β : ℝ) ^ N * Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2) := by
  classical
  have hmain := card_filter_ge_le (fun x => -f x) c hf.neg ht hS
  rw [pAvg_neg] at hmain
  have hfilter : ((univ : Finset (Fin N → β)).filter fun x => f x ≤ pAvg f - t)
      = (univ : Finset (Fin N → β)).filter fun x => -pAvg f + t ≤ -f x := by
    refine Finset.filter_congr fun x _ => ?_
    constructor <;> intro h <;> linarith
  rw [hfilter]
  exact hmain

/-- **Theorem 9.1.1**: the bounded differences inequality with all constants `1`, where the
bound reads `exp(-2t²/N)`. Both tails. -/
theorem card_filter_ge_le_one {N : ℕ} (hN : 0 < N)
    (f : (Fin N → β) → ℝ)
    (hf : ∀ (i : Fin N) (x y : Fin N → β), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    (#((univ : Finset (Fin N → β)).filter fun x => pAvg f + t ≤ f x) : ℝ)
        ≤ (Fintype.card β : ℝ) ^ N * Real.exp (-(2 * t ^ 2) / N)
      ∧ (#((univ : Finset (Fin N → β)).filter fun x => f x ≤ pAvg f - t) : ℝ)
        ≤ (Fintype.card β : ℝ) ^ N * Real.exp (-(2 * t ^ 2) / N) := by
  have hsum : ∑ _i : Fin N, (1 : ℝ) ^ 2 = N := by
    rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hS : 0 < ∑ _i : Fin N, (1 : ℝ) ^ 2 := by
    rw [hsum]
    exact_mod_cast hN
  have hup := card_filter_ge_le f (fun _ => 1) hf ht hS
  have hlo := card_filter_le_le f (fun _ => 1) hf ht hS
  rw [hsum] at hup hlo
  exact ⟨hup, hlo⟩


/-! ### Example 9.1.2 — the coupon collector

`s : Fin n → Fin n` draws `n` coupons uniformly, and `Z` counts the coupon types never drawn.
Changing one draw changes `Z` by at most one, so Theorem 9.1.1 applies with all constants `1`,
and the mean is `n(1 - 1/n)ⁿ` exactly. -/

/-- The number of coupon types that `s` misses. -/
def missing {n : ℕ} (s : Fin n → Fin n) : ℝ :=
  #((univ : Finset (Fin n)).filter fun v => ∀ i, s i ≠ v)

/-- Changing one draw changes the number of missed types by at most one: the two images
differ by at most the one replaced coupon on either side. -/
lemma bddDiff_missing {n : ℕ} : BddDiff (missing (n := n)) (fun _ => 1) := by
  classical
  intro i s s' hss'
  set M : Finset (Fin n) := (univ : Finset (Fin n)).filter fun v => ∀ j, s j ≠ v with hM
  set M' : Finset (Fin n) := (univ : Finset (Fin n)).filter fun v => ∀ j, s' j ≠ v with hM'
  -- a type missed by `s'` but not by `s` must be the one `s` puts at `i`
  have hsub : M' ⊆ insert (s i) M := by
    intro v hv
    rw [hM', mem_filter] at hv
    rw [Finset.mem_insert]
    by_cases hvi : v = s i
    · exact Or.inl hvi
    · refine Or.inr ?_
      rw [hM, mem_filter]
      refine ⟨mem_univ _, fun j => ?_⟩
      by_cases hji : j = i
      · subst hji
        exact fun hcon => hvi hcon.symm
      · rw [hss' j hji]
        exact hv.2 j
  have hsub' : M ⊆ insert (s' i) M' := by
    intro v hv
    rw [hM, mem_filter] at hv
    rw [Finset.mem_insert]
    by_cases hvi : v = s' i
    · exact Or.inl hvi
    · refine Or.inr ?_
      rw [hM', mem_filter]
      refine ⟨mem_univ _, fun j => ?_⟩
      by_cases hji : j = i
      · subst hji
        exact fun hcon => hvi hcon.symm
      · rw [← hss' j hji]
        exact hv.2 j
  have h1 : #M' ≤ #M + 1 :=
    le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_insert_le _ _) (by omega))
  have h2 : #M ≤ #M' + 1 :=
    le_trans (Finset.card_le_card hsub') (le_trans (Finset.card_insert_le _ _) (by omega))
  have hmiss : missing s = #M := by rw [missing, hM]
  have hmiss' : missing s' = #M' := by rw [missing, hM']
  have h1R : (#M' : ℝ) ≤ #M + 1 := by exact_mod_cast h1
  have h2R : (#M : ℝ) ≤ #M' + 1 := by exact_mod_cast h2
  rw [hmiss, hmiss', show ((fun _ => (1 : ℝ)) i) = 1 from rfl, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **The expected number of missed coupon types is `n(1 - 1/n)ⁿ`.** Each type is missed by
exactly `(n-1)ⁿ` of the `nⁿ` draws. -/
theorem pAvg_missing {n : ℕ} (hn : 0 < n) :
    pAvg (missing (n := n)) = n * (1 - 1 / (n : ℝ)) ^ n := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- count the draws missing a fixed type
  have hfib : ∀ v : Fin n,
      #((univ : Finset (Fin n → Fin n)).filter fun s => ∀ i, s i ≠ v) = (n - 1) ^ n := by
    intro v
    have hcard : #((univ : Finset (Fin n)).erase v) = n - 1 := by
      rw [Finset.card_erase_of_mem (mem_univ v), card_univ, Fintype.card_fin]
    rw [← hcard, ← Fintype.card_piFinset_const ((univ : Finset (Fin n)).erase v) n]
    refine Finset.card_bij (fun s _ => s) ?_ ?_ ?_
    · intro s hs
      rw [mem_filter] at hs
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_erase]
      exact ⟨hs.2 i, mem_univ _⟩
    · intro s _ s' _ h
      exact h
    · intro s hs
      rw [Fintype.mem_piFinset] at hs
      refine ⟨s, ?_, rfl⟩
      rw [mem_filter]
      exact ⟨mem_univ _, fun i => (Finset.mem_erase.mp (hs i)).1⟩
  -- double count
  have hsum : ∑ s : Fin n → Fin n, missing s = (n : ℝ) * (n - 1) ^ n := by
    have hswap : ∑ s : Fin n → Fin n, missing s
        = ∑ v : Fin n, (#((univ : Finset (Fin n → Fin n)).filter fun s => ∀ i, s i ≠ v) : ℝ) := by
      simp only [missing, Finset.card_filter]
      push_cast
      exact Finset.sum_comm
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ n := hn
      push_cast [h1]
      ring
    rw [hswap, Finset.sum_congr rfl fun v _ => by rw [hfib v], Finset.sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast [hcast]
    ring
  rw [pAvg, hsum, Fintype.card_fin]
  rw [show (1 : ℝ) - 1 / n = (n - 1) / n from by field_simp, div_pow]
  field_simp

/-- **Example 9.1.2 (coupon collector).** The number of missed coupon types is concentrated:
at most a `2 exp(-2t²/n)` fraction of the `nⁿ` draws miss it from its mean by `t` or more. -/
theorem card_filter_missing_le {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : 0 < t) :
    (#((univ : Finset (Fin n → Fin n)).filter fun s =>
        t ≤ |missing s - n * (1 - 1 / (n : ℝ)) ^ n|) : ℝ)
      ≤ 2 * ((n : ℝ) ^ n * Real.exp (-(2 * t ^ 2) / n)) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨hup, hlo⟩ := card_filter_ge_le_one hn (missing (n := n)) bddDiff_missing ht
  rw [pAvg_missing hn] at hup hlo
  have hsub : ((univ : Finset (Fin n → Fin n)).filter fun s =>
        t ≤ |missing s - n * (1 - 1 / (n : ℝ)) ^ n|)
      ⊆ ((univ : Finset (Fin n → Fin n)).filter fun s =>
          n * (1 - 1 / (n : ℝ)) ^ n + t ≤ missing s)
        ∪ ((univ : Finset (Fin n → Fin n)).filter fun s =>
          missing s ≤ n * (1 - 1 / (n : ℝ)) ^ n - t) := by
    intro s hs
    rw [mem_filter] at hs
    rw [mem_union, mem_filter, mem_filter]
    rcases le_abs.mp hs.2 with h | h
    · exact Or.inl ⟨mem_univ _, by linarith⟩
    · exact Or.inr ⟨mem_univ _, by linarith⟩
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    ((univ : Finset (Fin n → Fin n)).filter fun s =>
      n * (1 - 1 / (n : ℝ)) ^ n + t ≤ missing s)
    ((univ : Finset (Fin n → Fin n)).filter fun s =>
      missing s ≤ n * (1 - 1 / (n : ℝ)) ^ n - t)
  have hle : (#((univ : Finset (Fin n → Fin n)).filter fun s =>
        t ≤ |missing s - n * (1 - 1 / (n : ℝ)) ^ n|) : ℝ)
      ≤ #((univ : Finset (Fin n → Fin n)).filter fun s =>
          n * (1 - 1 / (n : ℝ)) ^ n + t ≤ missing s)
        + #((univ : Finset (Fin n → Fin n)).filter fun s =>
          missing s ≤ n * (1 - 1 / (n : ℝ)) ^ n - t) := by
    have := le_trans hcard hunion
    exact_mod_cast this
  rw [Fintype.card_fin] at hup hlo
  linarith


end BoundedDifferences

end PMC
