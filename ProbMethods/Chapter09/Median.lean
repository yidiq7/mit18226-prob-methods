import ProbMethods.Chapter09.Talagrand

/-!
# §9.5 — medians, and Talagrand's inequality around one (Corollary 9.5.22)

Zhao, *Probabilistic Methods in Combinatorics*, Corollary 9.5.22: for `f` that is
`1`-Lipschitz in Hamming distance with `{f ≥ r}` certifiable,

    P(f ≤ M f - t) ≤ 2 exp(-t²/(4s)),

where `M f` is a **median** of `f`. The concentration statements of §9.5 are all around the
median rather than the mean — that is what Talagrand's inequality gives directly, since it
bounds a *product* `P(f ≤ r - t) P(f ≥ r)`, and a median is exactly what makes the second
factor at least `1/2`.

So the content here is the median: `PMC.exists_isMedian` builds one for any real-valued
function on a nonempty finite type, and `PMC.card_filter_le_median_le` feeds it to
`PMC.card_mul_card_certifiable_le`.

**The median exists by a counting argument, not by compactness.** Take the *least* value `M`
attained by `f` with at least half the points below it. Then half the points are below `M` by
that choice, and at least half are at or above `M` because otherwise the largest attained
value strictly below `M` would also have half the points below it, contradicting minimality.
Nothing here needs an ordering of the whole space or a sort.

This file is separate from `Chapter09/Talagrand.lean` deliberately: that file holds task #49's
target declaration, so it is left byte-for-byte as published.
-/

open Finset

namespace PMC

section Median

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `M` is a median of `f`: at least half the points lie at or above it, and at least half at
or below. Stated multiplicatively (`2 * count ≥ card`) to stay in `ℕ`. -/
def IsMedian (f : α → ℝ) (M : ℝ) : Prop :=
  Fintype.card α ≤ 2 * #((univ : Finset α).filter fun x => M ≤ f x) ∧
    Fintype.card α ≤ 2 * #((univ : Finset α).filter fun x => f x ≤ M)

/-- **Every real-valued function on a nonempty finite type has a median.** -/
theorem exists_isMedian [Nonempty α] (f : α → ℝ) : ∃ M : ℝ, IsMedian f M := by
  classical
  set N := Fintype.card α with hN
  have hNpos : 0 < N := Fintype.card_pos
  set S : Finset ℝ := (univ : Finset α).image f with hS
  have hSne : S.Nonempty := (univ_nonempty (α := α)).image f
  set T : Finset ℝ := S.filter fun v => N ≤ 2 * #((univ : Finset α).filter fun x => f x ≤ v)
    with hT
  have hmemT : ∀ v : ℝ, v ∈ T ↔
      (v ∈ S ∧ N ≤ 2 * #((univ : Finset α).filter fun x => f x ≤ v)) := by
    intro v
    rw [hT, mem_filter]
  have hmaxT : S.max' hSne ∈ T := by
    rw [hmemT]
    refine ⟨S.max'_mem hSne, ?_⟩
    have hall : ((univ : Finset α).filter fun x => f x ≤ S.max' hSne) = univ := by
      refine Finset.filter_true_of_mem fun x _ => ?_
      exact S.le_max' (f x) (mem_image.mpr ⟨x, mem_univ _, rfl⟩)
    rw [hall, card_univ, ← hN]
    omega
  have hTne : T.Nonempty := ⟨S.max' hSne, hmaxT⟩
  refine ⟨T.min' hTne, ?_, ?_⟩
  · -- at least half the points are at or above the median: fewer than half lie strictly below
    have hstrict : 2 * #((univ : Finset α).filter fun x => f x < T.min' hTne) < N := by
      by_contra hcon
      push_neg at hcon
      set B : Finset α := (univ : Finset α).filter fun x => f x < T.min' hTne with hB
      have hBne : B.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hBempty
        rw [hB] at hBempty
        rw [hB, hBempty, Finset.card_empty] at hcon
        omega
      obtain ⟨x₀, hx₀⟩ := hBne
      rw [hB, mem_filter] at hx₀
      -- the largest value strictly below the median
      set S' : Finset ℝ := S.filter fun v => v < T.min' hTne with hS'
      have hmemS' : ∀ v : ℝ, v ∈ S' ↔ (v ∈ S ∧ v < T.min' hTne) := by
        intro v
        rw [hS', mem_filter]
      have hS'ne : S'.Nonempty :=
        ⟨f x₀, (hmemS' _).mpr ⟨mem_image.mpr ⟨x₀, mem_univ _, rfl⟩, hx₀.2⟩⟩
      have hv := (hmemS' _).mp (S'.max'_mem hS'ne)
      have hsets : ((univ : Finset α).filter fun x => f x ≤ S'.max' hS'ne) = B := by
        ext x
        rw [mem_filter, hB, mem_filter]
        refine ⟨fun h => ⟨mem_univ _, lt_of_le_of_lt h.2 hv.2⟩, fun h => ⟨mem_univ _, ?_⟩⟩
        exact S'.le_max' (f x)
          ((hmemS' _).mpr ⟨mem_image.mpr ⟨x, mem_univ _, rfl⟩, h.2⟩)
      have hvT : S'.max' hS'ne ∈ T := by
        rw [hmemT]
        refine ⟨hv.1, ?_⟩
        rw [hsets]
        exact hcon
      exact absurd (T.min'_le _ hvT) (not_le_of_gt hv.2)
    have hneg : ((univ : Finset α).filter fun x => T.min' hTne ≤ f x)
        = (univ : Finset α).filter fun x => ¬ (f x < T.min' hTne) := by
      refine Finset.filter_congr fun x _ => ?_
      rw [not_lt]
    have hsplit : #((univ : Finset α).filter fun x => f x < T.min' hTne)
        + #((univ : Finset α).filter fun x => T.min' hTne ≤ f x) = N := by
      rw [hneg, Finset.card_filter_add_card_filter_not, card_univ, ← hN]
    omega
  · -- and at least half at or below, by the defining property of `T`
    exact ((hmemT _).mp (T.min'_mem hTne)).2


/-! ### Talagrand's inequality around the median -/

section AroundMedian

variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β] {n : ℕ}

/-- **Corollary 9.5.22.** If `f` is `1`-Lipschitz for the Hamming distance, `M` is a median of
`f`, and `{f ≥ M}` is `s`-certifiable, then

    P(f ≤ M - t) ≤ 2 exp(-t²/(4s)),

in counting form. This is `PMC.card_mul_card_certifiable_le` at `r = M`, where being a median
is exactly what makes the second factor of Talagrand's product at least half the space.

The notes write the exponent as `-t²/(4 M f)`, taking `s = r` from "`{f ≥ r}` is
`r`-certifiable for every `r`"; keeping `s` explicit avoids having to round a real median to a
certificate size, and the notes' form is the instance `s = ⌈M⌉`.

`talagrand` is task #49's statement, threaded through as a hypothesis exactly as in
`PMC.card_mul_card_certifiable_le`. -/
theorem card_filter_le_median_le
    (talagrand : ∀ (A : Finset (Fin n → β)) (t' : ℝ), 0 ≤ t' →
      (#A : ℝ) * #((univ : Finset (Fin n → β)).filter fun x => t' ≤ convexDist A x)
        ≤ ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t' ^ 2) / 4))
    (hn : 0 < n) {f : (Fin n → β) → ℝ} (hf : HammingLipschitz f) {M t : ℝ}
    (hM : IsMedian f M) (ht : 0 < t) {s : ℕ} (hs : 0 < s)
    (hcert : Certifiable (fun y => M ≤ f y) s) :
    (#((univ : Finset (Fin n → β)).filter fun x => f x ≤ M - t) : ℝ)
      ≤ 2 * (Fintype.card β : ℝ) ^ n * Real.exp (-(t ^ 2) / (4 * s)) := by
  classical
  have hkey := card_mul_card_certifiable_le talagrand hn hf ht hs hcert
  -- the median gives at least half the space above `M`
  have hhalf : ((Fintype.card β : ℝ) ^ n)
      ≤ 2 * #((univ : Finset (Fin n → β)).filter fun y => M ≤ f y) := by
    have h := hM.1
    rw [Fintype.card_fun, Fintype.card_fin] at h
    exact_mod_cast h
  have hcpos : (0 : ℝ) < (Fintype.card β : ℝ) ^ n := by
    have : 0 < Fintype.card β := Fintype.card_pos
    positivity
  have hAnn : (0 : ℝ) ≤ #((univ : Finset (Fin n → β)).filter fun x => f x ≤ M - t) :=
    Nat.cast_nonneg _
  -- `#A · |β|ⁿ ≤ #A · 2#B ≤ 2 (|β|ⁿ)² exp(…)`, then divide by `|β|ⁿ`
  have hmul : (#((univ : Finset (Fin n → β)).filter fun x => f x ≤ M - t) : ℝ)
      * ((Fintype.card β : ℝ) ^ n)
      ≤ 2 * ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t ^ 2) / (4 * s)) := by
    calc (#((univ : Finset (Fin n → β)).filter fun x => f x ≤ M - t) : ℝ)
          * ((Fintype.card β : ℝ) ^ n)
        ≤ (#((univ : Finset (Fin n → β)).filter fun x => f x ≤ M - t) : ℝ)
            * (2 * #((univ : Finset (Fin n → β)).filter fun y => M ≤ f y)) :=
          mul_le_mul_of_nonneg_left hhalf hAnn
      _ = 2 * ((#((univ : Finset (Fin n → β)).filter fun x => f x ≤ M - t) : ℝ)
            * #((univ : Finset (Fin n → β)).filter fun y => M ≤ f y)) := by ring
      _ ≤ 2 * (((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t ^ 2) / (4 * s))) := by
          exact mul_le_mul_of_nonneg_left hkey (by norm_num)
      _ = 2 * ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t ^ 2) / (4 * s)) := by ring
  refine le_of_mul_le_mul_right ?_ hcpos
  calc (#((univ : Finset (Fin n → β)).filter fun x => f x ≤ M - t) : ℝ)
        * ((Fintype.card β : ℝ) ^ n)
      ≤ 2 * ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t ^ 2) / (4 * s)) := hmul
    _ = 2 * (Fintype.card β : ℝ) ^ n * Real.exp (-(t ^ 2) / (4 * s))
          * ((Fintype.card β : ℝ) ^ n) := by ring

end AroundMedian

end Median

end PMC
