import ProbMethods.Chapter08.Janson

/-!
# §8.1 — Janson's inequality II

Theorem 8.1.8: if `Δ ≥ μ` then `P(X = 0) ≤ e^{-μ²/(2Δ)}`.

Janson I (Theorem 8.1.2, `PMC.janson_upper`) is strong only when `Δ = o(μ)`. The second
inequality covers the other regime, and the notes' proof is a **sampling** argument: apply
Janson I not to the whole family but to a random subfamily `T`, keeping each index with
probability `q`. Then `E[μ_T] = qμ` and `E[Δ_T] = q²Δ`, so some `T` has
`-μ_T + Δ_T/2 ≤ -qμ + q²Δ/2`, and `q = μ/Δ` — legitimate exactly because `Δ ≥ μ` — makes that
`-μ²/(2Δ)`.

Both ingredients were already in the library: `PMC.janson_prod_le` was stated for an arbitrary
subfamily, and the random subfamily is the Bernoulli weight `PMC.bweight` on `Finset ι`, whose
first and second moments are `PMC.wmean_bweight_linear` and `PMC.sum_bweight_mem_pair`. What
this file adds is the pair-sum bookkeeping that connects them.
-/

open Finset

namespace PMC

section JansonII

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The overlapping ordered pairs, second index smaller: the index set of Zhao's `Δ/2`. -/
def jPairs (g : ι → Finset α) : Finset (ι × ι) :=
  (univ : Finset (ι × ι)).filter fun q => q.2 < q.1 ∧ (g q.1 ∩ g q.2).Nonempty

lemma mem_jPairs {g : ι → Finset α} {q : ι × ι} :
    q ∈ jPairs g ↔ q.2 < q.1 ∧ (g q.1 ∩ g q.2).Nonempty := by
  rw [jPairs, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- `Δ/2` restricted to a subfamily, as a single sum over pairs. -/
noncomputable def jHalfDelta (p : α → ℝ) (g : ι → Finset α) (T : Finset ι) : ℝ :=
  ∑ q ∈ (jPairs g).filter (fun q => q.1 ∈ T ∧ q.2 ∈ T),
    wprob (pweight p) (badEvent g q.1 ∩ badEvent g q.2)

/-- `μ` restricted to a subfamily. -/
noncomputable def jMu (p : α → ℝ) (g : ι → Finset α) (T : Finset ι) : ℝ :=
  ∑ i ∈ T, wprob (pweight p) (badEvent g i)

/-- The nested double sum of `PMC.janson_upper` in the pair-sum form. -/
lemma jHalfDelta_eq (p : α → ℝ) (g : ι → Finset α) (T : Finset ι) :
    jHalfDelta p g T
      = ∑ i ∈ T, ∑ j ∈ (T.filter fun j => j < i).filter
          (fun j => (g i ∩ g j).Nonempty),
          wprob (pweight p) (badEvent g i ∩ badEvent g j) := by
  classical
  rw [jHalfDelta]
  rw [show ((jPairs g).filter fun q => q.1 ∈ T ∧ q.2 ∈ T)
      = (T ×ˢ T).filter (fun q => q.2 < q.1 ∧ (g q.1 ∩ g q.2).Nonempty) from by
    ext q
    simp only [mem_filter, mem_jPairs, Finset.mem_product]
    exact ⟨fun h => ⟨⟨h.2.1, h.2.2⟩, h.1⟩, fun h => ⟨h.2, h.1.1, h.1.2⟩⟩]
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : j < i
  · by_cases h2 : (g i ∩ g j).Nonempty <;> simp [h1, h2]
  · simp [h1]

/-- **Janson I for a subfamily.** The proof of `PMC.janson_upper` never used that the family
was everything, so it applies verbatim to any `T`. -/
theorem janson_upper_sub (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (g : ι → Finset α) (T : Finset ι) :
    wprob (pweight p) (noneOf (badEvent g) T)
      ≤ Real.exp (-(jMu p g T) + jHalfDelta p g T) := by
  classical
  rw [jHalfDelta_eq, jMu]
  calc wprob (pweight p) (noneOf (badEvent g) T)
      ≤ ∏ i ∈ T, jansonFactor p g i (T.filter fun j => j < i) :=
        janson_prod_le p hp0 hp1 g T
    _ ≤ ∏ i ∈ T, Real.exp (-wprob (pweight p) (badEvent g i)
          + ∑ j ∈ ((T.filter fun j => j < i).filter
              (fun j => (g i ∩ g j).Nonempty)),
              wprob (pweight p) (badEvent g i ∩ badEvent g j)) :=
        Finset.prod_le_prod (fun i _ => jansonFactor_nonneg p hp0 hp1 g i _)
          (fun i _ => jansonFactor_le_exp p g i _)
    _ = Real.exp (∑ i ∈ T, (-wprob (pweight p) (badEvent g i)
          + ∑ j ∈ ((T.filter fun j => j < i).filter
              (fun j => (g i ∩ g j).Nonempty)),
              wprob (pweight p) (badEvent g i ∩ badEvent g j))) := (Real.exp_sum ..).symm
    _ = Real.exp (-(∑ i ∈ T, wprob (pweight p) (badEvent g i))
          + ∑ i ∈ T, ∑ j ∈ ((T.filter fun j => j < i).filter
              (fun j => (g i ∩ g j).Nonempty)),
              wprob (pweight p) (badEvent g i ∩ badEvent g j)) := by
        congr 1
        rw [Finset.sum_add_distrib, ← Finset.sum_neg_distrib]

/-! ### The moments of a random subfamily -/

lemma wmean_bweight_jMu (p : α → ℝ) (g : ι → Finset α) (r : ℝ) :
    wmean (bweight r) (fun T => jMu p g T) = r * jMu p g (univ : Finset ι) := by
  rw [jMu]
  exact wmean_bweight_linear r (fun i => wprob (pweight p) (badEvent g i))

lemma wmean_bweight_jHalfDelta (p : α → ℝ) (g : ι → Finset α) (r : ℝ) :
    wmean (bweight r) (fun T => jHalfDelta p g T)
      = r ^ 2 * jHalfDelta p g (univ : Finset ι) := by
  classical
  set b : ι × ι → ℝ := fun q => wprob (pweight p) (badEvent g q.1 ∩ badEvent g q.2) with hb
  have hexp : ∀ T : Finset ι, jHalfDelta p g T
      = ∑ q ∈ jPairs g, (if q.1 ∈ T ∧ q.2 ∈ T then b q else 0) := by
    intro T
    rw [jHalfDelta, Finset.sum_filter]
  have huniv : jHalfDelta p g (univ : Finset ι) = ∑ q ∈ jPairs g, b q := by
    rw [jHalfDelta]
    refine Finset.sum_congr ?_ fun q _ => rfl
    ext q
    simp only [mem_filter, mem_univ, and_true]
  have hstep : ∀ T : Finset ι, bweight r T * jHalfDelta p g T
      = ∑ q ∈ jPairs g, bweight r T * (if q.1 ∈ T ∧ q.2 ∈ T then b q else 0) := by
    intro T
    rw [hexp T, Finset.mul_sum]
  rw [wmean, Finset.sum_congr rfl fun T _ => hstep T, Finset.sum_comm, huniv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hne : q.1 ≠ q.2 := ne_of_gt (mem_jPairs.mp hq).1
  calc ∑ T : Finset ι, bweight r T * (if q.1 ∈ T ∧ q.2 ∈ T then b q else 0)
      = ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => q.1 ∈ T ∧ q.2 ∈ T),
          bweight r T * b q := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun T _ => ?_
        by_cases h : q.1 ∈ T ∧ q.2 ∈ T <;> simp [h]
    _ = (∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => q.1 ∈ T ∧ q.2 ∈ T),
          bweight r T) * b q := by
        rw [Finset.sum_mul]
    _ = r ^ #({q.1, q.2} : Finset ι) * b q := by rw [sum_bweight_mem_pair]
    _ = r ^ 2 * b q := by rw [Finset.card_pair hne]

/-! ### Theorem 8.1.8 -/

/-- **Janson's inequality II** (Zhao, Theorem 8.1.8). With `μ = ∑ P(Aᵢ)` and `Δ = 2D` (so `D`
is the lower-triangular half, as in `PMC.janson_upper`), if `μ ≤ Δ` then

    P(no bad set appears) ≤ exp (-μ² / (2Δ)) = exp (-μ² / (4D)).

The notes' sampling proof: apply Janson I to a random subfamily keeping each index with
probability `q = μ/Δ`, whose moments are `E[μ_T] = qμ` and `E[Δ_T] = q²Δ`, and take a
subfamily at least as good as the average. `μ ≤ Δ` is exactly what makes `q ≤ 1`. -/
theorem janson_upper_II (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (g : ι → Finset α) (hle : jMu p g (univ : Finset ι) ≤ 2 * jHalfDelta p g (univ : Finset ι)) :
    wprob (pweight p) (noneOf (badEvent g) (univ : Finset ι))
      ≤ Real.exp (-(jMu p g (univ : Finset ι)) ^ 2
          / (4 * jHalfDelta p g (univ : Finset ι))) := by
  classical
  set μ : ℝ := jMu p g (univ : Finset ι) with hμ
  set D : ℝ := jHalfDelta p g (univ : Finset ι) with hD
  have hμ0 : 0 ≤ μ := by
    rw [hμ, jMu]
    exact Finset.sum_nonneg fun i _ => wprob_nonneg (pweight_nonneg hp0 hp1) _
  have hD0 : 0 ≤ D := by
    rw [hD, jHalfDelta]
    exact Finset.sum_nonneg fun q _ => wprob_nonneg (pweight_nonneg hp0 hp1) _
  rcases eq_or_lt_of_le hD0 with hDzero | hDpos
  · -- `Δ = 0` forces `μ = 0`, and the bound is `1`
    have hμzero : μ = 0 := le_antisymm (by rw [← hDzero] at hle; linarith) hμ0
    rw [hμzero, ← hDzero]
    norm_num
    exact wprob_le_one (pweight_nonneg hp0 hp1) (by
      have h := sum_pweight (α := α) p
      rwa [Finset.powerset_univ] at h) _
  -- the sampling probability
  set q : ℝ := μ / (2 * D) with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one (by positivity)]
    exact hle
  have hwnn : ∀ T : Finset ι, 0 ≤ bweight q T := fun T => bweight_nonneg hq0 hq1 T
  have hwsum : ∑ T : Finset ι, bweight q T = 1 := by
    have h := sum_bweight (α := ι) q
    rwa [Finset.powerset_univ] at h
  -- the mean of `-μ_T + D_T`
  have hmean : wmean (bweight q) (fun T => -(jMu p g T) + jHalfDelta p g T)
      = -(μ ^ 2 / (4 * D)) := by
    have hlin : wmean (bweight q) (fun T => -(jMu p g T) + jHalfDelta p g T)
        = -(wmean (bweight q) (fun T => jMu p g T))
          + wmean (bweight q) (fun T => jHalfDelta p g T) := by
      rw [wmean, wmean, wmean, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun T _ => by ring
    rw [hlin, wmean_bweight_jMu, wmean_bweight_jHalfDelta, ← hμ, ← hD, hq]
    field_simp
    ring
  -- some subfamily is at least as good as the average
  obtain ⟨T, hT⟩ := exists_le_wmean hwnn hwsum (fun T => -(jMu p g T) + jHalfDelta p g T)
  rw [hmean] at hT
  calc wprob (pweight p) (noneOf (badEvent g) (univ : Finset ι))
      ≤ wprob (pweight p) (noneOf (badEvent g) T) :=
        wprob_mono (pweight_nonneg hp0 hp1) (noneOf_subset (badEvent g) (Finset.subset_univ T))
    _ ≤ Real.exp (-(jMu p g T) + jHalfDelta p g T) := janson_upper_sub p hp0 hp1 g T
    _ ≤ Real.exp (-(μ ^ 2 / (4 * D))) := Real.exp_le_exp.mpr hT
    _ = Real.exp (-(μ ^ 2) / (4 * D)) := by rw [neg_div]


end JansonII

end PMC
