import ProbMethods.Weighted

/-!
# §4.3 — monotone properties and the satisfying probability

§4.3's *threshold* results are asymptotic and stay deferred, but **Theorem 4.3.5 is not**: for
a non-trivial monotone property `F`, the map `p ↦ P(Ω_p ∈ F)` is strictly increasing on
`[0,1]`. That is a finite statement about a polynomial in `p`, and it is the fact every later
threshold argument silently uses.

In this project's encoding, `P(Ω_p ∈ F) = ∑_{S ∈ F} bweight p S` — the `G(n,p)` weight of
`Weighted.lean` summed over the family. *Monotone* means upward-closed, and *non-trivial*
means `F` is neither empty nor everything; note that upward-closure makes those equivalent to
`∅ ∉ F` and `univ ∈ F`.

Route for a prover. The clean argument changes one coordinate at a time. With independent
coordinate probabilities, the weight of `F` is **linear** in each `p_j`:

    P = p_j · P(F | j ∈ S) + (1 - p_j) · P(F | j ∉ S),

and upward-closure gives `P(F | j ∈ S) ≥ P(F | j ∉ S)` by the injection `S ↦ S ∪ {j}`, so `P`
is nondecreasing in every coordinate. Strictness needs one *pivotal* coordinate, which
non-triviality supplies: a minimal member of `F` is nonempty, and deleting one of its
elements leaves a non-member.
-/

open Finset

namespace PMC

section Threshold

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A family of subsets is **monotone** if it is upward-closed. -/
def IsMonotoneFamily (F : Finset (Finset α)) : Prop :=
  ∀ S ∈ F, ∀ T : Finset α, S ⊆ T → T ∈ F

/-- Upward-closure turns non-triviality into the two endpoint facts. -/
lemma notMem_empty_of_monotone {F : Finset (Finset α)} (hF : IsMonotoneFamily F)
    (hnotall : F ≠ (univ : Finset (Finset α))) : (∅ : Finset α) ∉ F := by
  intro hmem
  refine hnotall (Finset.eq_univ_of_forall fun S => ?_)
  exact hF ∅ hmem S (Finset.empty_subset S)

lemma mem_univ_of_monotone {F : Finset (Finset α)} (hF : IsMonotoneFamily F)
    (hne : F.Nonempty) : (univ : Finset α) ∈ F := by
  obtain ⟨S, hS⟩ := hne
  exact hF S hS univ (Finset.subset_univ S)

/-- **Theorem 4.3.5 (monotonicity of the satisfying probability).** For a non-trivial monotone
family `F`, the weight `p ↦ ∑_{S ∈ F} bweight p S` is strictly increasing on `[0,1]`. -/
theorem strictMonoOn_sum_bweight (F : Finset (Finset α)) (hF : IsMonotoneFamily F)
    (hne : F.Nonempty) (hnotall : F ≠ (univ : Finset (Finset α))) :
    StrictMonoOn (fun p : ℝ => ∑ S ∈ F, bweight p S) (Set.Icc (0 : ℝ) 1) := by
  set N : Finset (Finset α) := (univ : Finset α).powerset.filter (fun X => X ∉ F)
  have hN_sub : ∀ {X Z : Finset α}, Z ∈ N → X ⊆ Z → X ∈ N := by
    intro X Z hZ hXZ
    rw [mem_filter, mem_powerset] at hZ ⊢
    exact ⟨subset_univ X, fun hXF => hZ.2 (hF X hXF Z hXZ)⟩
  have hcompl : ∀ p : ℝ, (∑ S ∈ F, bweight p S) + (∑ X ∈ N, bweight p X) = 1 := by
    intro p
    have hF_eq : (univ : Finset α).powerset.filter (fun X => X ∈ F) = F := by
      ext X
      simp
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not (univ : Finset α).powerset (fun X => X ∈ F) (bweight p)
    rw [hF_eq, sum_bweight (α := α) p] at hsplit
    exact hsplit
  have hpair : ∀ {a b : ℝ}, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      ∑ Z ∈ N, bweight (1 - (1 - a) * (1 - b)) Z
        ≤ (∑ X ∈ N, bweight a X) * (∑ Y ∈ N, bweight b Y) := by
    intro a b ha0 ha1 hb0 hb1
    have hZ_eq : ∀ Z ∈ N, bweight (1 - (1 - a) * (1 - b)) Z
        = ∑ q ∈ (N ×ˢ N).filter (fun q => q.1 ∪ q.2 = Z), bweight a q.1 * bweight b q.2 := by
      intro Z hZ
      have hZle : #Z ≤ Fintype.card α := by rw [← card_univ]; exact card_le_univ Z
      have hbij : ∑ q ∈ (N ×ˢ N).filter (fun q => q.1 ∪ q.2 = Z), bweight a q.1 * bweight b q.2
          = ∑ x ∈ Z.powerset.sigma (fun X => X.powerset),
              bweight a x.1 * bweight b ((Z \ x.1) ∪ x.2) := by
        refine Finset.sum_nbij' (fun q => ⟨q.1, q.1 ∩ q.2⟩)
          (fun x => (x.1, (Z \ x.1) ∪ x.2)) ?_ ?_ ?_ ?_ ?_
        · intro q hq
          rw [mem_filter] at hq
          rw [mem_sigma, mem_powerset, mem_powerset]
          exact ⟨hq.2 ▸ subset_union_left, inter_subset_left⟩
        · intro x hx
          rw [mem_sigma, mem_powerset, mem_powerset] at hx
          have h1 := hx.1; have h2 := hx.2
          have hunion : x.1 ∪ ((Z \ x.1) ∪ x.2) = Z := by
            ext u; simp only [mem_union, mem_sdiff]; have := @h1 u; have := @h2 u; tauto
          rw [mem_filter, mem_product]
          exact ⟨⟨hN_sub hZ h1, hN_sub hZ (union_subset sdiff_subset (h2.trans h1))⟩, hunion⟩
        · intro q hq
          rw [mem_filter] at hq
          refine Prod.ext rfl ?_
          rw [← hq.2]; ext u; simp only [mem_union, mem_sdiff, mem_inter]; tauto
        · intro x hx
          rw [mem_sigma, mem_powerset, mem_powerset] at hx
          have h2 := hx.2
          refine Sigma.ext rfl (heq_of_eq ?_)
          ext u; simp only [mem_inter, mem_union, mem_sdiff]; have := @h2 u; tauto
        · intro q hq
          rw [mem_filter] at hq
          congr 2; rw [← hq.2]; ext u; simp only [mem_union, mem_sdiff, mem_inter]; tauto
      rw [hbij, Finset.sum_sigma]
      have hinner : ∀ X ∈ Z.powerset,
          ∑ W ∈ X.powerset, bweight a X * bweight b ((Z \ X) ∪ W)
            = (a ^ #X * ((1 - a) * b) ^ (#Z - #X))
              * ((1 - a) * (1 - b)) ^ (Fintype.card α - #Z) := by
        intro X hX
        rw [mem_powerset] at hX
        have hXle : #X ≤ #Z := card_le_card hX
        have hW_rewrite : ∀ W ∈ X.powerset,
            bweight a X * bweight b ((Z \ X) ∪ W)
              = (bweight a X * (b ^ (#Z - #X) * (1 - b) ^ (Fintype.card α - #Z)))
                * (b ^ #W * (1 - b) ^ (#X - #W)) := by
          intro W hW
          rw [mem_powerset] at hW
          have hWle : #W ≤ #X := card_le_card hW
          have hdisj : Disjoint (Z \ X) W := by
            rw [Finset.disjoint_left]
            intro u hu huW
            exact (mem_sdiff.mp hu).2 (hW huW)
          have hcardU : #((Z \ X) ∪ W) = (#Z - #X) + #W := by
            rw [card_union_of_disjoint hdisj, card_sdiff_of_subset hX]
          have hcardC : Fintype.card α - #((Z \ X) ∪ W)
              = (Fintype.card α - #Z) + (#X - #W) := by omega
          rw [bweight, bweight, hcardC, hcardU, pow_add, pow_add]
          ring
        rw [Finset.sum_congr rfl hW_rewrite, ← Finset.mul_sum, sum_bernoulli_on, mul_one]
        have hcardX : Fintype.card α - #X = (#Z - #X) + (Fintype.card α - #Z) := by omega
        rw [bweight, hcardX, pow_add, mul_pow, mul_pow]
        ring
      rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
      have hbinom : ∑ X ∈ Z.powerset, a ^ #X * ((1 - a) * b) ^ (#Z - #X)
          = (1 - (1 - a) * (1 - b)) ^ #Z := by
        have hprod := Finset.prod_add (fun _ : α => a) (fun _ : α => (1 - a) * b) Z
        calc ∑ X ∈ Z.powerset, a ^ #X * ((1 - a) * b) ^ (#Z - #X)
            = ∑ X ∈ Z.powerset, (∏ _i ∈ X, a) * ∏ _i ∈ Z \ X, ((1 - a) * b) := by
              refine Finset.sum_congr rfl fun X hX => ?_
              rw [mem_powerset] at hX
              rw [prod_const, prod_const, card_sdiff_of_subset hX]
          _ = ∏ _i ∈ Z, (a + (1 - a) * b) := hprod.symm
          _ = (1 - (1 - a) * (1 - b)) ^ #Z := by
              rw [prod_const]
              congr 1
              ring
      rw [hbinom, bweight]
      congr 2
      ring
    have hdisj : (N : Set (Finset α)).PairwiseDisjoint
        (fun Z => (N ×ˢ N).filter (fun q => q.1 ∪ q.2 = Z)) := by
      intro Z₁ _ Z₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro q hq1 hq2
      rw [mem_filter] at hq1 hq2
      exact hne (hq1.2.symm.trans hq2.2)
    have hsub : N.biUnion (fun Z => (N ×ˢ N).filter (fun q => q.1 ∪ q.2 = Z)) ⊆ N ×ˢ N := by
      intro q hq
      rw [mem_biUnion] at hq
      obtain ⟨Z, -, hq⟩ := hq
      exact (mem_filter.mp hq).1
    calc ∑ Z ∈ N, bweight (1 - (1 - a) * (1 - b)) Z
        = ∑ Z ∈ N, ∑ q ∈ (N ×ˢ N).filter (fun q => q.1 ∪ q.2 = Z),
            bweight a q.1 * bweight b q.2 := Finset.sum_congr rfl hZ_eq
      _ = ∑ q ∈ N.biUnion (fun Z => (N ×ˢ N).filter (fun q => q.1 ∪ q.2 = Z)),
            bweight a q.1 * bweight b q.2 := (Finset.sum_biUnion hdisj).symm
      _ ≤ ∑ q ∈ N ×ˢ N, bweight a q.1 * bweight b q.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ =>
            mul_nonneg (bweight_nonneg ha0 ha1 q.1) (bweight_nonneg hb0 hb1 q.2)
      _ = (∑ X ∈ N, bweight a X) * (∑ Y ∈ N, bweight b Y) := by
          rw [Finset.sum_mul_sum, ← Finset.sum_product']
  intro a ha c hc hac
  have ha0 : 0 ≤ a := ha.1
  have hc1 : c ≤ 1 := hc.2
  have ha1 : a < 1 := hac.trans_le hc1
  set b : ℝ := (c - a) / (1 - a)
  have ha_pos : 0 < 1 - a := sub_pos.mpr ha1
  have hb0 : 0 < b := div_pos (sub_pos.mpr hac) ha_pos
  have hb1 : b ≤ 1 := (div_le_one ha_pos).mpr (by linarith)
  have hab : 1 - (1 - a) * (1 - b) = c := by
    dsimp [b]
    rw [mul_sub, mul_one, mul_div_cancel₀ (c - a) ha_pos.ne']
    ring
  have hempty_N : (∅ : Finset α) ∈ N := by
    rw [mem_filter, mem_powerset]
    exact ⟨empty_subset _, notMem_empty_of_monotone hF hnotall⟩
  have hbweight_empty : 0 < bweight a (∅ : Finset α) := by
    rw [bweight, card_empty, pow_zero, one_mul, Nat.sub_zero]
    exact pow_pos ha_pos _
  have hN_pos : 0 < ∑ X ∈ N, bweight a X :=
    lt_of_lt_of_le hbweight_empty
      (Finset.single_le_sum (fun X _ => bweight_nonneg ha0 ha1.le X) hempty_N)
  have huniv_F : (univ : Finset α) ∈ F := mem_univ_of_monotone hF hne
  have hbweight_univ : 0 < bweight b (univ : Finset α) := by
    rw [bweight, card_univ, Nat.sub_self, pow_zero, mul_one]
    exact pow_pos hb0 _
  have hF_pos : 0 < ∑ S ∈ F, bweight b S :=
    lt_of_lt_of_le hbweight_univ
      (Finset.single_le_sum (fun S _ => bweight_nonneg hb0.le hb1 S) huniv_F)
  have hN_lt_one : ∑ Y ∈ N, bweight b Y < 1 := by
    linarith [hcompl b]
  have hlt : ∑ Z ∈ N, bweight c Z < ∑ X ∈ N, bweight a X := by
    calc ∑ Z ∈ N, bweight c Z
        = ∑ Z ∈ N, bweight (1 - (1 - a) * (1 - b)) Z := by rw [hab]
      _ ≤ (∑ X ∈ N, bweight a X) * (∑ Y ∈ N, bweight b Y) :=
          hpair ha0 ha1.le hb0.le hb1
      _ < (∑ X ∈ N, bweight a X) * 1 :=
          mul_lt_mul_of_pos_left hN_lt_one hN_pos
      _ = ∑ X ∈ N, bweight a X := mul_one _
  linarith [hcompl a, hcompl c]

end Threshold

end PMC
