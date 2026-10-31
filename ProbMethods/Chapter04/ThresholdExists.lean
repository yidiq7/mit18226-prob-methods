import ProbMethods.Chapter04.BollobasThomason
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# §4.3 — Theorem 4.3.6, every non-trivial monotone property has a threshold

Zhao, *Probabilistic Methods in Combinatorics*, Definition 4.3.1 and Theorem 4.3.6
(Bollobás–Thomason 1987). `q` is a *threshold* for a sequence of monotone properties when

    P(Ω_{p_n} ∈ F) → 0  whenever  p_n / q_n → 0,      P(Ω_{p_n} ∈ F) → 1  whenever  p_n / q_n → ∞,

and the theorem is that a threshold always exists. The notes single this out as the reason
Lemma 4.3.7 is worth having ("The theorem follows from the next non-asymptotic claim"), so
this file is the asymptotic half of that pair; `PMC.sum_bweight_notMem_le_pow` is the other.

## The route

Take `q n` to be the `p` at which the property has probability exactly `1/2`.

* **It exists.** `p ↦ ∑_{X ∈ F n} bweight p X` is a polynomial in `p`, hence continuous, it is
  `0` at `p = 0` and `1` at `p = 1` — those two endpoint facts are exactly
  `PMC.notMem_empty_of_monotone` and `PMC.mem_univ_of_monotone`, which is what non-triviality
  is for — so the intermediate value theorem supplies `q n ∈ (0,1)` with value `1/2`.
* **Below the threshold.** Fix `m`. Once `p n ≤ q n / m`, antitonicity and Lemma 4.3.7 give

      P(Ω_{p n} ∉ F) ≥ P(Ω_{q n / m} ∉ F) ≥ P(Ω_{q n} ∉ F)^{1/m} = (1/2)^{1/m},

  so `P(Ω_{p n} ∈ F) ≤ 1 - (1/2)^{1/m}`. Letting `m → ∞` after `n → ∞` gives the limit `0`.
* **Above the threshold.** Once `p n ≥ m · q n`, the same lemma read forwards gives

      P(Ω_{p n} ∉ F) ≤ P(Ω_{p n / m} ∉ F)^m ≤ P(Ω_{q n} ∉ F)^m = (1/2)^m,

  so `P(Ω_{p n} ∈ F) ≥ 1 - 2^{-m}`, and again `m → ∞`.

Both directions need `p ↦ P(Ω_p ∉ F)` to be antitone, which is the non-strict form of task
#50, and Lemma 4.3.7, which is task #57. Nothing else.

Remark 4.3.3 in the notes — two thresholds differ by a bounded factor — is not part of this
statement; it is why the notes say "the" threshold.
-/

open Finset

namespace PMC

section ThresholdExists

variable {Ω : ℕ → Type} [∀ n, Fintype (Ω n)] [∀ n, DecidableEq (Ω n)]

/-- **Definition 4.3.1.** `q` is a threshold for the sequence of properties `F`. -/
def IsThreshold (F : ∀ n, Finset (Finset (Ω n))) (q : ℕ → ℝ) : Prop :=
  ∀ p : ℕ → ℝ, (∀ n, p n ∈ Set.Icc (0 : ℝ) 1) →
    (Filter.Tendsto (fun n => p n / q n) Filter.atTop (nhds 0) →
        Filter.Tendsto (fun n => ∑ X ∈ F n, bweight (p n) X) Filter.atTop (nhds 0)) ∧
      (Filter.Tendsto (fun n => p n / q n) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun n => ∑ X ∈ F n, bweight (p n) X) Filter.atTop (nhds 1))

/-! ### One property: the point where the probability is `1/2` -/

/-- `P(Ω_p ∈ F) + P(Ω_p ∉ F) = 1`. -/
private lemma sum_bweight_add_sum_bweight_notMem {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (p : ℝ) :
    (∑ X ∈ F, bweight p X)
      + ∑ X ∈ (univ : Finset α).powerset.filter (fun X => X ∉ F), bweight p X = 1 := by
  have hset : (univ : Finset α).powerset.filter (fun X => X ∈ F) = F := by
    ext X
    simp
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset α).powerset
    (fun X => X ∈ F) (bweight p)
  rwa [hset, sum_bweight] at hsplit

/-- `P(Ω_p ∈ F)` is a polynomial in `p`, hence continuous. -/
private lemma continuous_sum_bweight {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) : Continuous fun p : ℝ => ∑ X ∈ F, bweight p X := by
  refine continuous_finsetSum _ fun X _ => ?_
  unfold bweight
  fun_prop

/-- A family avoiding `∅` has probability `0` at `p = 0`. -/
private lemma sum_bweight_zero_of_empty_notMem {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} (hF : (∅ : Finset α) ∉ F) : ∑ X ∈ F, bweight (0 : ℝ) X = 0 := by
  refine Finset.sum_eq_zero fun X hX => ?_
  have hne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun h => hF (h ▸ hX)
  rw [bweight, zero_pow (Finset.card_ne_zero.mpr hne), zero_mul]

/-- A family containing `univ` has probability `1` at `p = 1`. -/
private lemma sum_bweight_one_of_univ_mem {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} (hF : (univ : Finset α) ∈ F) : ∑ X ∈ F, bweight (1 : ℝ) X = 1 := by
  rw [Finset.sum_eq_single_of_mem univ hF]
  · simp [bweight]
  · intro X _ hX
    have hlt : #X < Fintype.card α := by
      rw [← Finset.card_univ]
      exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hX)
    rw [bweight, sub_self, zero_pow (by omega), mul_zero]

/-- A non-trivial monotone family has probability exactly `1/2` at some `q ∈ (0,1)`. -/
private lemma exists_sum_bweight_eq_half {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} (hF : IsMonotoneFamily F) (hne : F.Nonempty)
    (hnotall : F ≠ (univ : Finset (Finset α))) :
    ∃ q ∈ Set.Ioo (0 : ℝ) 1, ∑ X ∈ F, bweight q X = 1 / 2 := by
  have h0 := sum_bweight_zero_of_empty_notMem (notMem_empty_of_monotone hF hnotall)
  have h1 := sum_bweight_one_of_univ_mem (mem_univ_of_monotone hF hne)
  have hhalf : (1 / 2 : ℝ) ∈ (fun p : ℝ => ∑ X ∈ F, bweight p X) '' Set.Icc 0 1 := by
    refine intermediate_value_Icc zero_le_one (continuous_sum_bweight F).continuousOn ?_
    simp only [Set.mem_Icc, h0, h1]
    norm_num
  obtain ⟨q, ⟨hq0, hq1⟩, hval⟩ := hhalf
  have hval' : ∑ X ∈ F, bweight q X = 1 / 2 := hval
  refine ⟨q, ⟨lt_of_le_of_ne hq0 ?_, lt_of_le_of_ne hq1 ?_⟩, hval'⟩
  · rintro rfl
    rw [h0] at hval'
    norm_num at hval'
  · rintro rfl
    rw [h1] at hval'
    norm_num at hval'

/-! ### One property: the two estimates

`g` below stands for `p ↦ P(Ω_p ∉ F)`, of which only nonnegativity, antitonicity and
Lemma 4.3.7 are used, together with `g q = 1/2`. -/

/-- Below the threshold: if `c ^ m < 1/2` and `p ≤ q / m`, then `c < g p`. -/
private lemma lt_of_le_div_of_pow_lt_half {g : ℝ → ℝ}
    (hg0 : ∀ p, 0 ≤ p → p ≤ 1 → 0 ≤ g p) (hanti : AntitoneOn g (Set.Icc 0 1))
    (hbt : ∀ p, 0 ≤ p → p ≤ 1 → ∀ m : ℕ, 1 ≤ m → g p ≤ g (p / m) ^ m)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hgq : g q = 1 / 2)
    {c : ℝ} {m : ℕ} (hm : 1 ≤ m) (hcm : c ^ m < 1 / 2)
    {p : ℝ} (hp0 : 0 ≤ p) (hpq : p ≤ q / m) : c < g p := by
  by_contra hle
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hqm0 : 0 ≤ q / m := div_nonneg hq0 (by linarith)
  have hqm1 : q / m ≤ 1 := (div_le_self hq0 hm').trans hq1
  have h1 : g (q / m) ≤ g p := hanti ⟨hp0, hpq.trans hqm1⟩ ⟨hqm0, hqm1⟩ hpq
  have h2 : g (q / m) ^ m ≤ c ^ m :=
    pow_le_pow_left₀ (hg0 _ hqm0 hqm1) (h1.trans (not_lt.mp hle)) m
  have h3 := hbt q hq0 hq1 m hm
  linarith

/-- Above the threshold: if `q ≤ p / m`, then `g p ≤ (1/2) ^ m`. -/
private lemma le_half_pow_of_le_div {g : ℝ → ℝ}
    (hg0 : ∀ p, 0 ≤ p → p ≤ 1 → 0 ≤ g p) (hanti : AntitoneOn g (Set.Icc 0 1))
    (hbt : ∀ p, 0 ≤ p → p ≤ 1 → ∀ m : ℕ, 1 ≤ m → g p ≤ g (p / m) ^ m)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hgq : g q = 1 / 2)
    {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hqp : q ≤ p / m) :
    g p ≤ (1 / 2) ^ m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpm0 : 0 ≤ p / m := div_nonneg hp0 (by linarith)
  have hpm1 : p / m ≤ 1 := (div_le_self hp0 hm').trans hp1
  calc g p ≤ g (p / m) ^ m := hbt p hp0 hp1 m hm
    _ ≤ g q ^ m := pow_le_pow_left₀ (hg0 _ hpm0 hpm1) (hanti ⟨hq0, hq1⟩ ⟨hpm0, hpm1⟩ hqp) m
    _ = (1 / 2) ^ m := by rw [hgq]

/-! ### Lemma 4.3.7, carried

`PMC.sum_bweight_notMem_le_pow` (task #57, open PR #65) is still a placeholder at this task's
pinned commit, and this project's gate refuses a proof that inherits one, so its argument is
carried here to keep the theorem unconditional. It also gives the antitonicity, so the strict
monotonicity of task #50 is not needed. Once #65 lands, `sum_bweight_notMem_le_pow_aux` can give
way to that lemma. -/

/-- Two independent samples: the union of `Ω_a` and `Ω_b` has distribution
`Ω_{1 - (1-a)(1-b)}`, and it avoids an upward-closed `F` only if both samples do. -/
private lemma sum_bweight_union_notMem_le {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} (hF : IsMonotoneFamily F) {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∑ Z ∈ (univ : Finset α).powerset.filter (fun X => X ∉ F), bweight (1 - (1 - a) * (1 - b)) Z
      ≤ (∑ X ∈ (univ : Finset α).powerset.filter (fun X => X ∉ F), bweight a X)
        * ∑ Y ∈ (univ : Finset α).powerset.filter (fun X => X ∉ F), bweight b Y := by
  set N : Finset (Finset α) := (univ : Finset α).powerset.filter (fun X => X ∉ F)
  have hN_sub : ∀ {X Z : Finset α}, Z ∈ N → X ⊆ Z → X ∈ N := by
    intro X Z hZ hXZ
    rw [mem_filter, mem_powerset] at hZ ⊢
    exact ⟨ subset_univ X, fun hXF => hZ.2 (hF X hXF Z hXZ) ⟩
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

/-- More elements can only help an upward-closed property: `p ↦ P(Ω_p ∉ F)` is antitone. Writing
`Ω_p` as the union of `Ω_q` and an independent sample, it avoids `F` only if `Ω_q` does. -/
private lemma antitoneOn_sum_bweight_notMem {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} (hF : IsMonotoneFamily F) :
    AntitoneOn (fun p : ℝ => ∑ X ∈ (univ : Finset α).powerset.filter (fun X => X ∉ F), bweight p X)
      (Set.Icc (0 : ℝ) 1) := by
  intro q hq p hp hqp
  beta_reduce
  set N : Finset (Finset α) := (univ : Finset α).powerset.filter (fun X => X ∉ F)
  have hN_le_one : ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 → ∑ X ∈ N, bweight r X ≤ 1 := by
    intro r hr0 hr1
    rw [← sum_bweight (α := α) r]
    exact Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun X _ _ => bweight_nonneg hr0 hr1 X
  have hN_nonneg : ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 → 0 ≤ ∑ X ∈ N, bweight r X := by
    intro r hr0 hr1
    exact Finset.sum_nonneg fun X _ => bweight_nonneg hr0 hr1 X
  rcases eq_or_lt_of_le hq.2 with hq1 | hq1
  · rw [le_antisymm (hp.2.trans hq1.symm.le) hqp]
  · set b : ℝ := (p - q) / (1 - q)
    have hq_pos : 0 < 1 - q := sub_pos.mpr hq1
    have hb0 : 0 ≤ b := div_nonneg (sub_nonneg.mpr hqp) hq_pos.le
    have hb1 : b ≤ 1 := (div_le_one hq_pos).mpr (by linarith [hp.2])
    have hqb : 1 - (1 - q) * (1 - b) = p := by
      dsimp [b]
      rw [mul_sub, mul_one, mul_div_cancel₀ (p - q) hq_pos.ne']
      ring
    calc ∑ Z ∈ N, bweight p Z
        = ∑ Z ∈ N, bweight (1 - (1 - q) * (1 - b)) Z := by rw [hqb]
      _ ≤ (∑ X ∈ N, bweight q X) * (∑ Y ∈ N, bweight b Y) :=
          sum_bweight_union_notMem_le hF hq.1 hq1.le hb0 hb1
      _ ≤ (∑ X ∈ N, bweight q X) * 1 :=
          mul_le_mul_of_nonneg_left (hN_le_one hb0 hb1) (hN_nonneg hq.1 hq1.le)
      _ = ∑ X ∈ N, bweight q X := mul_one _

/-- **Lemma 4.3.7**, with the proof from task #57: `P(Ω_p ∉ F) ≤ P(Ω_{p/m} ∉ F) ^ m`. -/
private theorem sum_bweight_notMem_le_pow_aux {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} (hF : IsMonotoneFamily F)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    (∑ X ∈ (univ : Finset α).powerset.filter (fun X => X ∉ F), bweight p X)
      ≤ (∑ X ∈ (univ : Finset α).powerset.filter (fun X => X ∉ F), bweight (p / m) X) ^ m := by
  set N : Finset (Finset α) := (univ : Finset α).powerset.filter (fun X => X ∉ F)
  have hN_le_one : ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 → ∑ X ∈ N, bweight r X ≤ 1 := by
    intro r hr0 hr1
    rw [← sum_bweight (α := α) r]
    exact Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun X _ _ => bweight_nonneg hr0 hr1 X
  have hN_nonneg : ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 → 0 ≤ ∑ X ∈ N, bweight r X := by
    intro r hr0 hr1
    exact Finset.sum_nonneg fun X _ => bweight_nonneg hr0 hr1 X
  have hpair : ∀ {a b : ℝ}, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      ∑ Z ∈ N, bweight (1 - (1 - a) * (1 - b)) Z
        ≤ (∑ X ∈ N, bweight a X) * (∑ Y ∈ N, bweight b Y) :=
    fun ha0 ha1 hb0 hb1 => sum_bweight_union_notMem_le hF ha0 ha1 hb0 hb1
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
  have hanti : ∑ Z ∈ N, bweight p Z ≤ ∑ X ∈ N, bweight q X :=
    antitoneOn_sum_bweight_notMem hF ⟨hq0, hqp.trans hp1⟩ ⟨hp0, hp1⟩ hqp
  exact hanti.trans (hpow m)

/-! ### The sequence of properties -/

/-- If `p n / q n → 0` then `g n (p n) → 1`. -/
private lemma tendsto_one_of_div_tendsto_zero {g : ℕ → ℝ → ℝ}
    (hg0 : ∀ n p, 0 ≤ p → p ≤ 1 → 0 ≤ g n p) (hg1 : ∀ n p, 0 ≤ p → p ≤ 1 → g n p ≤ 1)
    (hanti : ∀ n, AntitoneOn (g n) (Set.Icc 0 1))
    (hbt : ∀ n p, 0 ≤ p → p ≤ 1 → ∀ m : ℕ, 1 ≤ m → g n p ≤ g n (p / m) ^ m)
    {q : ℕ → ℝ} (hq : ∀ n, q n ∈ Set.Ioo (0 : ℝ) 1) (hgq : ∀ n, g n (q n) = 1 / 2)
    {p : ℕ → ℝ} (hp : ∀ n, p n ∈ Set.Icc (0 : ℝ) 1)
    (h : Filter.Tendsto (fun n => p n / q n) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => g n (p n)) Filter.atTop (nhds 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => Filter.Eventually.of_forall fun n =>
    (hg1 n _ (hp n).1 (hp n).2).trans_lt ha⟩
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (one_half_pos (α := ℝ))
    (max_lt ha one_pos : max a 0 < 1)
  have hm1 : 1 ≤ m := by
    refine Nat.one_le_iff_ne_zero.mpr ?_
    rintro rfl
    norm_num at hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  filter_upwards [h.eventually_lt_const (show (0 : ℝ) < 1 / m by positivity)] with n hn
  have hlt : p n < 1 / m * q n := (div_lt_iff₀ (hq n).1).1 hn
  have hle : p n ≤ q n / m := by
    have e : q n / m = 1 / m * q n := by ring
    linarith
  exact (le_max_left a 0).trans_lt <| lt_of_le_div_of_pow_lt_half (hg0 n) (hanti n) (hbt n)
    (hq n).1.le (hq n).2.le (hgq n) hm1 hm (hp n).1 hle

/-- If `p n / q n → ∞` then `g n (p n) → 0`. -/
private lemma tendsto_zero_of_div_tendsto_atTop {g : ℕ → ℝ → ℝ}
    (hg0 : ∀ n p, 0 ≤ p → p ≤ 1 → 0 ≤ g n p)
    (hanti : ∀ n, AntitoneOn (g n) (Set.Icc 0 1))
    (hbt : ∀ n p, 0 ≤ p → p ≤ 1 → ∀ m : ℕ, 1 ≤ m → g n p ≤ g n (p / m) ^ m)
    {q : ℕ → ℝ} (hq : ∀ n, q n ∈ Set.Ioo (0 : ℝ) 1) (hgq : ∀ n, g n (q n) = 1 / 2)
    {p : ℕ → ℝ} (hp : ∀ n, p n ∈ Set.Icc (0 : ℝ) 1)
    (h : Filter.Tendsto (fun n => p n / q n) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => g n (p n)) Filter.atTop (nhds 0) := by
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n =>
    ha.trans_le (hg0 n _ (hp n).1 (hp n).2), fun a ha => ?_⟩
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one ha (one_half_lt_one (α := ℝ))
  have hmpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  filter_upwards [h.eventually_ge_atTop ((m + 1 : ℕ) : ℝ)] with n hn
  have hmul : ((m + 1 : ℕ) : ℝ) * q n ≤ p n := (le_div_iff₀ (hq n).1).1 hn
  have hle : q n ≤ p n / (m + 1 : ℕ) := (le_div_iff₀ hmpos).2 (by linarith)
  calc g n (p n) ≤ (1 / 2) ^ (m + 1) :=
        le_half_pow_of_le_div (hg0 n) (hanti n) (hbt n) (hq n).1.le (hq n).2.le (hgq n)
          (Nat.le_add_left 1 m) (hp n).1 (hp n).2 hle
    _ ≤ (1 / 2) ^ m := pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ m)
    _ < a := hm

/-- Theorem 4.3.6 with its two inputs as hypotheses: antitonicity of
`p ↦ P(Ω_p ∉ F n)` and the bound `P(Ω_p ∉ F n) ≤ P(Ω_{p/m} ∉ F n) ^ m`
(Lemma 4.3.7). -/
theorem exists_isThreshold_of_monotone_of_pow_bound (F : ∀ n, Finset (Finset (Ω n)))
    (hmono : ∀ n, IsMonotoneFamily (F n)) (hne : ∀ n, (F n).Nonempty)
    (hnotall : ∀ n, F n ≠ (univ : Finset (Finset (Ω n))))
    (hanti : ∀ n, AntitoneOn (fun p : ℝ =>
        ∑ X ∈ (univ : Finset (Ω n)).powerset.filter (fun X => X ∉ F n), bweight p X)
      (Set.Icc (0 : ℝ) 1))
    (hbt : ∀ n (p : ℝ), 0 ≤ p → p ≤ 1 → ∀ m : ℕ, 1 ≤ m →
      (∑ X ∈ (univ : Finset (Ω n)).powerset.filter (fun X => X ∉ F n), bweight p X)
        ≤ (∑ X ∈ (univ : Finset (Ω n)).powerset.filter (fun X => X ∉ F n),
            bweight (p / m) X) ^ m) :
    ∃ q : ℕ → ℝ, (∀ n, q n ∈ Set.Ioo (0 : ℝ) 1) ∧ IsThreshold F q := by
  choose q hq hqval using fun n => exists_sum_bweight_eq_half (hmono n) (hne n) (hnotall n)
  let g : ℕ → ℝ → ℝ := fun n p =>
    ∑ X ∈ (univ : Finset (Ω n)).powerset.filter (fun X => X ∉ F n), bweight p X
  have hadd : ∀ n p, (∑ X ∈ F n, bweight p X) + g n p = 1 := fun n p =>
    sum_bweight_add_sum_bweight_notMem (F n) p
  have hf0 : ∀ n (p : ℝ), 0 ≤ p → p ≤ 1 → 0 ≤ ∑ X ∈ F n, bweight p X := fun n _ hp0 hp1 =>
    Finset.sum_nonneg fun X _ => bweight_nonneg hp0 hp1 X
  have hg0 : ∀ n p, 0 ≤ p → p ≤ 1 → 0 ≤ g n p := fun n _ hp0 hp1 =>
    Finset.sum_nonneg fun X _ => bweight_nonneg hp0 hp1 X
  have hg1 : ∀ n p, 0 ≤ p → p ≤ 1 → g n p ≤ 1 := fun n p hp0 hp1 => by
    linarith [hadd n p, hf0 n p hp0 hp1]
  have hgq : ∀ n, g n (q n) = 1 / 2 := fun n => by
    linarith [hadd n (q n), hqval n]
  refine ⟨q, hq, fun p hp => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hlim := (tendsto_one_of_div_tendsto_zero hg0 hg1 hanti hbt hq hgq hp h).const_sub 1
    rw [sub_self] at hlim
    exact hlim.congr fun n => by linarith [hadd n (p n)]
  · have hlim := (tendsto_zero_of_div_tendsto_atTop hg0 hanti hbt hq hgq hp h).const_sub 1
    rw [sub_zero] at hlim
    exact hlim.congr fun n => by linarith [hadd n (p n)]

/-- **Theorem 4.3.6 (Bollobás–Thomason 1987).** Every sequence of non-trivial monotone
properties has a threshold. -/
theorem exists_isThreshold (F : ∀ n, Finset (Finset (Ω n)))
    (hmono : ∀ n, IsMonotoneFamily (F n)) (hne : ∀ n, (F n).Nonempty)
    (hnotall : ∀ n, F n ≠ (univ : Finset (Finset (Ω n)))) :
    ∃ q : ℕ → ℝ, (∀ n, q n ∈ Set.Ioo (0 : ℝ) 1) ∧ IsThreshold F q := by
  exact exists_isThreshold_of_monotone_of_pow_bound F hmono hne hnotall
    (fun n => antitoneOn_sum_bweight_notMem (hmono n))
    (fun n _ hp0 hp1 _ hm => sum_bweight_notMem_le_pow_aux (hmono n) hp0 hp1 hm)

end ThresholdExists

end PMC
