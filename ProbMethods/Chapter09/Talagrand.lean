import ProbMethods.Chapter09.BoundedDifferences
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# §9.5 — Talagrand's inequality: the convex distance

Theorem 9.5.11: for `A ⊆ Ω₁ × ⋯ × Ωₙ` with a product probability measure,

    P(x ∈ A) · P(d_T(x, A) ≥ t) ≤ e^{-t²/4},

where `d_T` is Talagrand's **convex distance**. Its combinatorial applications are the reason
the inequality matters: unlike the bounded differences inequality, whose bound degrades as
`e^{-t²/n}`, this one has no `n` in the exponent.

This file sets up the distance and its basic properties, and states the inequality. **The
definitions are where the design choices are**, so they are recorded here rather than left to
whoever proves the analytic core:

* the sample space is the uniform product `Fin n → β`, as in §9.1 — not the fully general
  product of distinct factors with an arbitrary product measure. The notes' applications
  reach that generality by padding coordinates, the same device `Chapter09/
  ChromaticConcentration.lean` uses for graphs;
* `PMC.wHamDist` is the weighted Hamming distance and `PMC.wDistToSet` its distance to a set,
  defined to be `0` on the empty set so that it is total;
* `PMC.convexDist` is the supremum of `PMC.wDistToSet α` over the unit sphere of nonnegative
  weights, as a `sSup` — the set is nonempty and bounded above by `√n`
  (`PMC.wDistToSet_le_sqrt`), so the supremum is a genuine real number.

The inequality itself (`PMC.card_mul_card_filter_convexDist_le`) is published as a task. Its
proof is an induction on the number of coordinates using Hölder's inequality, together with
the elementary but delicate fact that `inf_{0≤λ≤1} e^{(1-λ)²/4} r^{-λ} ≤ 2 - r` for
`r ∈ (0,1]`; the notes do not prove it either.
-/

open Finset

namespace PMC

section Talagrand

variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β] {n : ℕ}

/-- The weighted Hamming distance: the total weight of the coordinates where `x` and `y`
differ. -/
def wHamDist (α : Fin n → ℝ) (x y : Fin n → β) : ℝ :=
  ∑ i ∈ (univ : Finset (Fin n)).filter fun i => x i ≠ y i, α i

lemma wHamDist_self (α : Fin n → ℝ) (x : Fin n → β) : wHamDist α x x = 0 := by
  rw [wHamDist, Finset.filter_false_of_mem, Finset.sum_empty]
  intro i _
  simp

lemma wHamDist_nonneg {α : Fin n → ℝ} (hα : ∀ i, 0 ≤ α i) (x y : Fin n → β) :
    0 ≤ wHamDist α x y :=
  Finset.sum_nonneg fun i _ => hα i

/-- The weighted distance from `x` to a set, taken to be `0` on the empty set. -/
noncomputable def wDistToSet (α : Fin n → ℝ) (A : Finset (Fin n → β)) (x : Fin n → β) : ℝ :=
  if h : A.Nonempty then A.inf' h (fun y => wHamDist α x y) else 0

lemma wDistToSet_nonneg {α : Fin n → ℝ} (hα : ∀ i, 0 ≤ α i) (A : Finset (Fin n → β))
    (x : Fin n → β) : 0 ≤ wDistToSet α A x := by
  rw [wDistToSet]
  by_cases h : A.Nonempty
  · rw [dif_pos h]
    obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_inf' h (fun y => wHamDist α x y)
    rw [hy]
    exact wHamDist_nonneg hα x y
  · rw [dif_neg h]

lemma wDistToSet_eq_zero_of_mem {α : Fin n → ℝ} (hα : ∀ i, 0 ≤ α i)
    {A : Finset (Fin n → β)} {x : Fin n → β} (hx : x ∈ A) : wDistToSet α A x = 0 := by
  have h : A.Nonempty := ⟨x, hx⟩
  rw [wDistToSet, dif_pos h]
  refine le_antisymm ?_ ?_
  · have := Finset.inf'_le (fun y => wHamDist α x y) hx
    rwa [wHamDist_self] at this
  · obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_inf' h (fun y => wHamDist α x y)
    rw [hy]
    exact wHamDist_nonneg hα x y

/-- **The weighted distance is at most `√n`** for a unit weight vector, by Cauchy–Schwarz on
the coordinates where the two points differ. This is what makes the supremum defining the
convex distance a real number. -/
lemma wDistToSet_le_sqrt {α : Fin n → ℝ} (hα : ∀ i, 0 ≤ α i) (hnorm : ∑ i, α i ^ 2 = 1)
    (A : Finset (Fin n → β)) (x : Fin n → β) : wDistToSet α A x ≤ Real.sqrt n := by
  classical
  have hbound : ∀ y : Fin n → β, wHamDist α x y ≤ Real.sqrt n := by
    intro y
    set D : Finset (Fin n) := (univ : Finset (Fin n)).filter fun i => x i ≠ y i with hD
    have hcs : (∑ i ∈ D, α i) ^ 2 ≤ #D * ∑ i ∈ D, α i ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hle : ∑ i ∈ D, α i ^ 2 ≤ 1 := by
      rw [← hnorm]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => sq_nonneg _)
    have hcard : (#D : ℝ) ≤ n := by
      have := Finset.card_le_card (Finset.filter_subset (fun i => x i ≠ y i)
        (univ : Finset (Fin n)))
      rw [card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    have hsq : (∑ i ∈ D, α i) ^ 2 ≤ (n : ℝ) := by
      calc (∑ i ∈ D, α i) ^ 2 ≤ #D * ∑ i ∈ D, α i ^ 2 := hcs
        _ ≤ (n : ℝ) * 1 := by
            refine mul_le_mul hcard hle (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
            positivity
        _ = (n : ℝ) := by ring
    have hnn : 0 ≤ ∑ i ∈ D, α i := Finset.sum_nonneg fun i _ => hα i
    rw [wHamDist, ← hD]
    calc ∑ i ∈ D, α i = Real.sqrt ((∑ i ∈ D, α i) ^ 2) := by
          rw [Real.sqrt_sq hnn]
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hsq
  rw [wDistToSet]
  by_cases h : A.Nonempty
  · rw [dif_pos h]
    obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_inf' h (fun y => wHamDist α x y)
    rw [hy]
    exact hbound y
  · rw [dif_neg h]
    positivity

/-- The nonnegative unit weight vectors. -/
def unitWeights (n : ℕ) : Set (Fin n → ℝ) :=
  {α | (∀ i, 0 ≤ α i) ∧ (∑ i, α i ^ 2) = 1}

/-- **Talagrand's convex distance**: the largest weighted Hamming distance from `x` to `A`
over all nonnegative unit weight vectors. -/
noncomputable def convexDist (A : Finset (Fin n → β)) (x : Fin n → β) : ℝ :=
  sSup ((fun α => wDistToSet α A x) '' unitWeights n)

lemma unitWeights_nonempty (hn : 0 < n) : (unitWeights n).Nonempty := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨fun i => if i = (0 : Fin n) then 1 else 0, fun i => by positivity, ?_⟩
  have hterm : ∀ i : Fin n, (if i = (0 : Fin n) then (1 : ℝ) else 0) ^ 2
      = if i = (0 : Fin n) then (1 : ℝ) else 0 := by
    intro i
    by_cases h : i = 0 <;> simp [h]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp

lemma bddAbove_convexDist_image (A : Finset (Fin n → β)) (x : Fin n → β) :
    BddAbove ((fun α => wDistToSet α A x) '' unitWeights n) := by
  refine ⟨Real.sqrt n, ?_⟩
  rintro r ⟨α', hα', rfl⟩
  exact wDistToSet_le_sqrt hα'.1 hα'.2 A x

lemma convexDist_nonneg (hn : 0 < n) (A : Finset (Fin n → β)) (x : Fin n → β) :
    0 ≤ convexDist A x := by
  obtain ⟨α, hα⟩ := unitWeights_nonempty hn
  have hmem : wDistToSet α A x ∈ (fun α => wDistToSet α A x) '' unitWeights n := ⟨α, hα, rfl⟩
  exact le_trans (wDistToSet_nonneg hα.1 A x)
    (le_csSup (bddAbove_convexDist_image A x) hmem)

/-- The convex distance vanishes on `A`. -/
lemma convexDist_eq_zero_of_mem (hn : 0 < n) {A : Finset (Fin n → β)} {x : Fin n → β}
    (hx : x ∈ A) : convexDist A x = 0 := by
  refine le_antisymm ?_ (convexDist_nonneg hn A x)
  obtain ⟨α₀, hα₀⟩ := unitWeights_nonempty hn
  refine csSup_le ⟨_, ⟨α₀, hα₀, rfl⟩⟩ ?_
  rintro r ⟨α, hα, rfl⟩
  exact le_of_eq (wDistToSet_eq_zero_of_mem hα.1 hx)

/-- **Theorem 9.5.11 (Talagrand's inequality, general form).** In counting form:

    #A · #{x : d_T(x, A) ≥ t} ≤ |β|^{2n} · e^{-t²/4},

which is `P(x ∈ A) P(d_T(x,A) ≥ t) ≤ e^{-t²/4}` after dividing by `|β|^{2n}`. -/
theorem card_mul_card_filter_convexDist_le (hn : 0 < n) (A : Finset (Fin n → β)) {t : ℝ}
    (ht : 0 ≤ t) :
    (#A : ℝ) * #((univ : Finset (Fin n → β)).filter fun x => t ≤ convexDist A x)
      ≤ ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t ^ 2) / 4) := by
  sorry

/-! ### Theorem 9.5.21 — certifiable functions

The combinatorial half of §9.5. Everything below the convex distance is counting: given a
certificate for `f ≥ r` at `y`, the normalised indicator of the certificate is a unit weight
vector witnessing `d_T(y, A) ≥ t/√s`, and Talagrand's inequality does the rest. No convex
geometry is needed, which is why this part can be proved here while the inequality itself is
out as task #49. -/

/-- `f` is `1`-Lipschitz for the Hamming distance. -/
def HammingLipschitz (f : (Fin n → β) → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ #((univ : Finset (Fin n)).filter fun i => x i ≠ y i)

/-- A predicate is `s`-certifiable if membership is always witnessed by at most `s`
coordinates: any point agreeing with `y` there also satisfies it. -/
def Certifiable (P : (Fin n → β) → Prop) (s : ℕ) : Prop :=
  ∀ y, P y → ∃ I : Finset (Fin n), #I ≤ s ∧ ∀ z, (∀ i ∈ I, z i = y i) → P z

/-- **A point far below `r` must disagree with a certificate on at least `t` coordinates.**
Otherwise splicing the certificate's coordinates in would move `f` by less than `t` and land
above `r`. -/
lemma card_disagree_ge {f : (Fin n → β) → ℝ} (hf : HammingLipschitz f) {r t : ℝ}
    {y : Fin n → β} {I : Finset (Fin n)} (hI : ∀ z, (∀ i ∈ I, z i = y i) → r ≤ f z)
    {x : Fin n → β} (hx : f x ≤ r - t) :
    t ≤ #(I.filter fun i => x i ≠ y i) := by
  classical
  set z : Fin n → β := fun i => if i ∈ I then y i else x i with hzdef
  have hzI : ∀ i ∈ I, z i = y i := fun i hi => by rw [hzdef]; exact if_pos hi
  have hfz : r ≤ f z := hI z hzI
  have hdiff : ((univ : Finset (Fin n)).filter fun i => z i ≠ x i)
      = I.filter fun i => x i ≠ y i := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    by_cases hiI : i ∈ I
    · have hzi : z i = y i := hzI i hiI
      rw [hzi]
      exact ⟨fun h => ⟨hiI, fun hcon => h hcon.symm⟩, fun h hcon => h.2 hcon.symm⟩
    · have hzi : z i = x i := if_neg hiI
      rw [hzi]
      exact ⟨fun h => absurd rfl h, fun h => absurd h.1 hiI⟩
  have hlip := hf z x
  rw [hdiff] at hlip
  have hle : f z - f x ≤ #(I.filter fun i => x i ≠ y i) :=
    le_trans (le_abs_self _) hlip
  linarith

/-- The normalised indicator of a nonempty coordinate set is a unit weight vector. -/
lemma unitWeights_indicator {I : Finset (Fin n)} (hI : I.Nonempty) :
    (fun i => if i ∈ I then 1 / Real.sqrt #I else 0) ∈ unitWeights n := by
  classical
  have hcard : (0 : ℝ) < #I := by exact_mod_cast Finset.card_pos.mpr hI
  refine ⟨fun i => by by_cases h : i ∈ I <;> simp only [if_pos, if_neg, h] <;> positivity, ?_⟩
  have hterm : ∀ i : Fin n, (if i ∈ I then 1 / Real.sqrt #I else 0) ^ 2
      = if i ∈ I then 1 / (#I : ℝ) else 0 := by
    intro i
    by_cases h : i ∈ I
    · simp only [if_pos h]
      rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hcard)]
    · simp only [if_neg h]
      ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul, mul_one_div, div_self (ne_of_gt hcard)]


/-- The weighted distance under a normalised certificate indicator: the disagreements inside
the certificate, divided by `√#I`. -/
lemma wHamDist_indicator {I : Finset (Fin n)} (hI : I.Nonempty) (y x : Fin n → β) :
    wHamDist (fun i => if i ∈ I then 1 / Real.sqrt #I else 0) y x
      = #(I.filter fun i => y i ≠ x i) / Real.sqrt #I := by
  classical
  rw [wHamDist, Finset.sum_ite_mem]
  have hset : ((univ : Finset (Fin n)).filter fun i => y i ≠ x i) ∩ I
      = I.filter fun i => y i ≠ x i := by
    ext i
    simp only [mem_inter, mem_filter, mem_univ, true_and]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- **Theorem 9.5.21 (Talagrand's inequality for certifiable functions).** If `f` is
`1`-Lipschitz for the Hamming distance and `{f ≥ r}` is `s`-certifiable, then

    P(f ≤ r - t) P(f ≥ r) ≤ e^{-t²/(4s)}.

Talagrand's inequality enters as the hypothesis `talagrand`, in exactly the form task #49
proves, so this derivation is `sorry`-free. Everything else is counting: the normalised
indicator of a certificate is a unit weight vector witnessing `d_T(y, A) ≥ t/√s`. -/
theorem card_mul_card_certifiable_le
    (talagrand : ∀ (A : Finset (Fin n → β)) (t' : ℝ), 0 ≤ t' →
      (#A : ℝ) * #((univ : Finset (Fin n → β)).filter fun x => t' ≤ convexDist A x)
        ≤ ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t' ^ 2) / 4))
    (hn : 0 < n) {f : (Fin n → β) → ℝ} (hf : HammingLipschitz f) {r t : ℝ} (ht : 0 < t)
    {s : ℕ} (hs : 0 < s) (hcert : Certifiable (fun y => r ≤ f y) s) :
    (#((univ : Finset (Fin n → β)).filter fun x => f x ≤ r - t) : ℝ)
        * #((univ : Finset (Fin n → β)).filter fun y => r ≤ f y)
      ≤ ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t ^ 2) / (4 * s)) := by
  classical
  set A : Finset (Fin n → β) := (univ : Finset (Fin n → β)).filter fun x => f x ≤ r - t
    with hAdef
  set B : Finset (Fin n → β) := (univ : Finset (Fin n → β)).filter fun y => r ≤ f y with hBdef
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsqs : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr hsR
  set t' : ℝ := t / Real.sqrt s with htdef
  have ht' : 0 < t' := by rw [htdef]; positivity
  have hexp : -(t' ^ 2) / 4 = -(t ^ 2) / (4 * s) := by
    rw [htdef, div_pow, Real.sq_sqrt (le_of_lt hsR)]
    field_simp
  by_cases hAne : A.Nonempty
  swap
  · -- no point lies that far below `r`
    rw [Finset.not_nonempty_iff_eq_empty] at hAne
    rw [hAne, Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  -- every point of `B` is far from `A` in convex distance
  have hBsub : B ⊆ (univ : Finset (Fin n → β)).filter fun y => t' ≤ convexDist A y := by
    intro y hy
    rw [hBdef, mem_filter] at hy
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    obtain ⟨I, hIcard, hIext⟩ := hcert y hy.2
    -- the certificate is nonempty, else every point would be above `r`
    have hIne : I.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hIempty
      obtain ⟨x, hx⟩ := hAne
      rw [hAdef, mem_filter] at hx
      have := hIext x (by rw [hIempty]; intro i hi; exact absurd hi (Finset.notMem_empty i))
      linarith [hx.2]
    have hIcardR : (0 : ℝ) < #I := by exact_mod_cast Finset.card_pos.mpr hIne
    set α : Fin n → ℝ := fun i => if i ∈ I then 1 / Real.sqrt #I else 0 with hαdef
    have hαunit : α ∈ unitWeights n := unitWeights_indicator hIne
    -- the certificate's indicator already witnesses the bound
    have hfar : ∀ x ∈ A, t' ≤ wHamDist α y x := by
      intro x hx
      rw [hAdef, mem_filter] at hx
      have hdis : t ≤ #(I.filter fun i => x i ≠ y i) := card_disagree_ge hf hIext hx.2
      have hsym : (I.filter fun i => y i ≠ x i) = I.filter fun i => x i ≠ y i := by
        refine Finset.filter_congr fun i _ => ?_
        exact ⟨fun h hcon => h hcon.symm, fun h hcon => h hcon.symm⟩
      have hsq1 : Real.sqrt #I ≤ Real.sqrt s := Real.sqrt_le_sqrt (by exact_mod_cast hIcard)
      have hsq2 : (0 : ℝ) < Real.sqrt #I := Real.sqrt_pos.mpr hIcardR
      have hnum : (0 : ℝ) ≤ #(I.filter fun i => x i ≠ y i) := by positivity
      rw [hαdef, wHamDist_indicator hIne, hsym, htdef]
      calc t / Real.sqrt s
          ≤ (#(I.filter fun i => x i ≠ y i) : ℝ) / Real.sqrt s :=
            div_le_div_of_nonneg_right hdis (le_of_lt hsqs)
        _ ≤ (#(I.filter fun i => x i ≠ y i) : ℝ) / Real.sqrt #I := by
            gcongr
    have hdist : t' ≤ wDistToSet α A y := by
      rw [wDistToSet, dif_pos hAne]
      exact Finset.le_inf' hAne _ hfar
    refine le_trans hdist (le_csSup (bddAbove_convexDist_image A y) ⟨α, hαunit, rfl⟩)
  -- Talagrand, at `t/√s`
  calc (#A : ℝ) * #B
      ≤ (#A : ℝ) * #((univ : Finset (Fin n → β)).filter fun y => t' ≤ convexDist A y) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact_mod_cast Finset.card_le_card hBsub
    _ ≤ ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t' ^ 2) / 4) :=
        talagrand A t' (le_of_lt ht')
    _ = ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t ^ 2) / (4 * s)) := by rw [hexp]


end Talagrand

end PMC
