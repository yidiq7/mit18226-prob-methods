import ProbMethods.Chapter04.Threshold

/-!
# §4.3 — Lemma 4.3.7, the Bollobás–Thomason inequality

Zhao, *Probabilistic Methods in Combinatorics*, Lemma 4.3.7: for a monotone property `F` and
any `m ≥ 1`,

    P(Ω_p ∉ F) ≤ P(Ω_{p/m} ∉ F) ^ m.

This is the non-asymptotic engine behind Theorem 4.3.6 ("every sequence of non-trivial monotone
properties has a threshold"), which the notes derive from it — so it is the piece worth having,
and the asymptotic statement follows without any further probability.

## The route

Two steps, and only the first is a coupling.

1. **`m` independent copies.** Let `q = 1 - (1 - p/m)^m`. Sampling `Ω_{p/m}` independently `m`
   times and taking the union gives exactly `Ω_q`, because an element is absent from the union
   iff it is absent from all `m` copies. Since `F` is *upward closed*, the union lies outside
   `F` only if every copy does, and the copies are independent, so

       P(Ω_q ∉ F) ≤ P(Ω_{p/m} ∉ F) ^ m.

   In this framework the `m` copies are `Fin m → Finset α` with the product weight, and the
   union is `fun X => Finset.univ.biUnion X`; `PMC.pweight` and the product machinery in
   `ProbMethods/Product.lean` are what make "independent" mechanical rather than a definition
   to re-establish.

2. **`q ≤ p`.** Bernoulli's inequality gives `(1 - p/m)^m ≥ 1 - p`, i.e. `q ≤ p`, and for a
   monotone `F` the map `p ↦ P(Ω_p ∉ F)` is *antitone*: more edges can only help a monotone
   property. That antitonicity is the non-strict form of task #50
   (`PMC.strictMonoOn_sum_bweight`); it can be taken from there once #50 lands, or proved
   directly by the same one-coordinate coupling, which is the easier half.

Stated without the notes' non-triviality hypothesis on `F`, which the inequality does not need:
at `F = ∅` both sides are `1`, and at `F = univ` the left side is `0`.
-/

open Finset

namespace PMC

section BollobasThomason

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Lemma 4.3.7 (Bollobás–Thomason).** For an upward-closed family `F` and `m ≥ 1`,

    P(Ω_p ∉ F) ≤ P(Ω_{p/m} ∉ F) ^ m,

where `Ω_p` is the random subset including each element independently with probability `p`. -/
theorem sum_bweight_notMem_le_pow {F : Finset (Finset α)} (hF : IsMonotoneFamily F)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    (∑ X ∈ (univ : Finset α).powerset.filter (fun X => X ∉ F), bweight p X)
      ≤ (∑ X ∈ (univ : Finset α).powerset.filter (fun X => X ∉ F),
          bweight (p / m) X) ^ m := by
  set N : Finset (Finset α) := (univ : Finset α).powerset.filter (fun X => X ∉ F)
  have hN_sub : ∀ {X Z : Finset α}, Z ∈ N → X ⊆ Z → X ∈ N := by
    intro X Z hZ hXZ
    rw [mem_filter, mem_powerset] at hZ ⊢
    exact ⟨ subset_univ X, fun hXF => hZ.2 (hF X hXF Z hXZ) ⟩
  have hN_le_one : ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 → ∑ X ∈ N, bweight r X ≤ 1 := by
    intro r hr0 hr1
    rw [← sum_bweight (α := α) r]
    exact Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun X _ _ => bweight_nonneg hr0 hr1 X
  have hN_nonneg : ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 → 0 ≤ ∑ X ∈ N, bweight r X := by
    intro r hr0 hr1
    exact Finset.sum_nonneg fun X _ => bweight_nonneg hr0 hr1 X
  -- Two independent samples: the union of `Ω_a` and `Ω_b` has distribution `Ω_{1 - (1-a)(1-b)}`.
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
  -- Step 1: `m` independent copies of `Ω_{p/m}`.
  set r : ℝ := p / m
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast ( Nat.lt_of_lt_of_le Nat.zero_lt_one hm )
  have hm_ge1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr0 : 0 ≤ r := div_nonneg hp0 hm_pos.le
  have hr1 : r ≤ 1 := div_le_one_of_le₀ (hp1.trans hm_ge1) hm_pos.le
  have hpow : ∀ k : ℕ,
      ∑ Z ∈ N, bweight (1 - (1 - r) ^ k) Z ≤ (∑ X ∈ N, bweight r X) ^ k := by
    intro k
    induction k with
    | zero =>
        simp only [pow_zero, sub_self]
        exact hN_le_one le_rfl zero_le_one
    | succ k ih =>
        have hk0 : 0 ≤ 1 - (1 - r) ^ k := by
          have : (1 - r) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
          linarith
        have hk1 : 1 - (1 - r) ^ k ≤ 1 := by
          have : 0 ≤ (1 - r) ^ k := pow_nonneg (by linarith) k
          linarith
        have hstep := hpair hk0 hk1 hr0 hr1
        have hrw : 1 - (1 - (1 - (1 - r) ^ k)) * (1 - r) = 1 - (1 - r) ^ (k + 1) := by
          rw [pow_succ]
          ring
        rw [hrw] at hstep
        calc ∑ Z ∈ N, bweight (1 - (1 - r) ^ (k + 1)) Z
            ≤ (∑ X ∈ N, bweight (1 - (1 - r) ^ k) X) * (∑ Y ∈ N, bweight r Y) := hstep
          _ ≤ (∑ X ∈ N, bweight r X) ^ k * (∑ Y ∈ N, bweight r Y) :=
              mul_le_mul_of_nonneg_right ih (hN_nonneg hr0 hr1)
          _ = (∑ X ∈ N, bweight r X) ^ (k + 1) := (pow_succ _ k).symm
  -- Step 2: `q = 1 - (1 - p/m)^m ≤ p` by Bernoulli, and `p ↦ P(Ω_p ∉ F)` is antitone.
  set q : ℝ := 1 - (1 - r) ^ m
  have hq0 : 0 ≤ q := by
    have : (1 - r) ^ m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    linarith
  have hqp : q ≤ p := by
    have hbern : ∀ k : ℕ, 1 - (k : ℝ) * r ≤ (1 - r) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          push_cast
          rw [pow_succ]
          have h1 : (1 - (k : ℝ) * r) * (1 - r) ≤ (1 - r) ^ k * (1 - r) :=
            mul_le_mul_of_nonneg_right ih (by linarith)
          have h2 : 0 ≤ (k : ℝ) * r ^ 2 := mul_nonneg (Nat.cast_nonneg k) (sq_nonneg r)
          linarith
    have hbm := hbern m
    have hmr : (m : ℝ) * r = p := mul_div_cancel₀ p hm_pos.ne'
    linarith
  have hanti : ∑ Z ∈ N, bweight p Z ≤ ∑ X ∈ N, bweight q X := by
    rcases eq_or_lt_of_le (hqp.trans hp1) with hq1 | hq1
    · have hpq : p = q := le_antisymm (hp1.trans hq1.symm.le) hqp
      rw [hpq]
    · set b : ℝ := (p - q) / (1 - q)
      have hq_pos : 0 < 1 - q := sub_pos.mpr hq1
      have hb0 : 0 ≤ b := div_nonneg (sub_nonneg.mpr hqp) hq_pos.le
      have hb1 : b ≤ 1 := (div_le_one hq_pos).mpr (by linarith)
      have hqb : 1 - (1 - q) * (1 - b) = p := by
        dsimp [b]
        rw [mul_sub, mul_one, mul_div_cancel₀ (p - q) hq_pos.ne']
        ring
      calc ∑ Z ∈ N, bweight p Z
          = ∑ Z ∈ N, bweight (1 - (1 - q) * (1 - b)) Z := by rw [hqb]
        _ ≤ (∑ X ∈ N, bweight q X) * (∑ Y ∈ N, bweight b Y) :=
            hpair hq0 hq1.le hb0 hb1
        _ ≤ (∑ X ∈ N, bweight q X) * 1 :=
            mul_le_mul_of_nonneg_left (hN_le_one hb0 hb1) (hN_nonneg hq0 hq1.le)
        _ = ∑ X ∈ N, bweight q X := mul_one _
  exact hanti.trans (hpow m)

end BollobasThomason

end PMC
