import ProbMethods.Chapter10.OrderChain
import ProbMethods.RandomOrder

/-!
# §10.2 — the Brégman–Minc inequality

Theorem 10.2.1: a `0-1` matrix whose `i`-th row has `dᵢ` ones has permanent at most
`∏ᵢ (dᵢ!)^{1/dᵢ}`. Equality holds for a block-diagonal matrix of all-ones blocks, so the
bound is exactly right.

Radhakrishnan's proof, which the notes follow, is the model entropy argument. Take `σ`
uniform on the permutations that select a one from every row, so `H(σ) = log (per A)`; reveal
the rows **in a uniformly random order** `τ`; and bound each conditional entropy by the log of
the number of columns still available. The whole point of the random order is the step proved
in `RandomOrder.lean`: for a fixed `σ`, as `τ` varies the number of available columns is
uniform on `{1, …, dᵢ}`, so its expected log is `log(dᵢ!)/dᵢ` rather than the lossy `log dᵢ`.

This file's combinatorial core is `PMC.card_avail_eq_tauRank`: the columns of row `i` not yet
taken correspond, under `σ`, to the rows that `τ` reveals at or after `i`. That is what makes
the abstract rank lemma applicable, and it is the identity the notes leave implicit.
-/

open Finset

namespace PMC

section Bregman

variable {n : ℕ} (row : Fin n → Finset (Fin n))

/-- The permutations selecting a one from every row: the perfect matchings the permanent
counts. -/
def matchSet (row : Fin n → Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  (univ : Finset (Equiv.Perm (Fin n))).filter fun σ => ∀ i, σ i ∈ row i

lemma mem_matchSet {σ : Equiv.Perm (Fin n)} :
    σ ∈ matchSet row ↔ ∀ i, σ i ∈ row i := by
  rw [matchSet, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- The rows whose selected column is one of row `i`'s ones. Under `σ` this set corresponds
bijectively to row `i`'s support, so it has `dᵢ` elements. -/
def hitSet (row : Fin n → Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    Finset (Fin n) :=
  (univ : Finset (Fin n)).filter fun j => σ j ∈ row i

lemma card_hitSet (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    #(hitSet row σ i) = #(row i) := by
  refine Finset.card_bij (fun j _ => σ j) ?_ ?_ ?_
  · intro j hj
    rw [hitSet, mem_filter] at hj
    exact hj.2
  · intro j _ j' _ h
    exact σ.injective h
  · intro c hc
    refine ⟨σ.symm c, ?_, by rw [Equiv.apply_symm_apply]⟩
    rw [hitSet, mem_filter, Equiv.apply_symm_apply]
    exact ⟨mem_univ _, hc⟩

lemma mem_hitSet_self {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ matchSet row) (i : Fin n) :
    i ∈ hitSet row σ i := by
  rw [hitSet, mem_filter]
  exact ⟨mem_univ _, (mem_matchSet row).mp hσ i⟩

/-- **The available columns are the rows revealed later.** For a matching `σ` and an order
`τ`, the columns of row `i` not already used by a row revealed before `i` correspond — via
`σ⁻¹` — to the members of `PMC.hitSet` that `τ` reveals at or after `i`.

This is the identity that lets the abstract uniformity of `PMC.tauRank` be applied to the
matrix: each one of row `i` sits in a column `σ j` for exactly one row `j`, and the one is
still available precisely when that `j` has not yet been revealed. -/
theorem card_avail_eq_tauRank (τ σ : Equiv.Perm (Fin n)) (i : Fin n) :
    #((row i).filter fun c => ∀ j ∈ predSet τ i, σ j ≠ c)
      = tauRank (hitSet row σ i) τ i := by
  rw [tauRank]
  refine Finset.card_bij (fun c _ => σ.symm c) ?_ ?_ ?_
  · intro c hc
    rw [mem_filter] at hc
    obtain ⟨hcrow, hcavail⟩ := hc
    rw [mem_filter, hitSet, mem_filter, Equiv.apply_symm_apply]
    refine ⟨⟨mem_univ _, hcrow⟩, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    exact hcavail (σ.symm c) (by rw [predSet, mem_filter]; exact ⟨mem_univ _, hlt⟩)
      (by rw [Equiv.apply_symm_apply])
  · intro c _ c' _ h
    exact σ.symm.injective h
  · intro j hj
    rw [mem_filter, hitSet, mem_filter] at hj
    obtain ⟨⟨-, hjrow⟩, hjlate⟩ := hj
    refine ⟨σ j, ?_, by rw [Equiv.symm_apply_apply]⟩
    rw [mem_filter]
    refine ⟨hjrow, ?_⟩
    intro j' hj' heq
    rw [predSet, mem_filter] at hj'
    have : j' = j := σ.injective heq
    subst this
    exact absurd hj'.2 (not_lt.mpr hjlate)

/-! ### The entropy of a uniform matching -/

/-- The uniform weight on the matchings. -/
noncomputable def matchWeight (row : Fin n → Finset (Fin n)) :
    ↥(matchSet row) → ℝ :=
  fun _ => 1 / Fintype.card ↥(matchSet row)

/-- The column that a matching assigns to row `i`. -/
def matchCoord (row : Fin n → Finset (Fin n)) (i : Fin n) :
    ↥(matchSet row) → Fin n :=
  fun ω => (ω : Equiv.Perm (Fin n)) i

lemma matchWeight_nonneg (ω : ↥(matchSet row)) : 0 ≤ matchWeight row ω := by
  simp only [matchWeight]
  positivity

lemma sum_matchWeight (hne : (matchSet row).Nonempty) :
    ∑ ω : ↥(matchSet row), matchWeight row ω = 1 := by
  have hcard : 0 < Fintype.card ↥(matchSet row) := by
    rw [Fintype.card_coe]
    exact Finset.card_pos.mpr hne
  have hpos : (0 : ℝ) < Fintype.card ↥(matchSet row) := by exact_mod_cast hcard
  simp only [matchWeight]
  rw [Finset.sum_const, card_univ, nsmul_eq_mul, mul_one_div, div_self (ne_of_gt hpos)]

/-- **`H(σ) = log (per A)`.** A uniform matching is determined by its coordinates, so its
entropy is the log of the number of matchings — this is the step that turns the entropy bound
back into a bound on the permanent. -/
theorem tupleEntropy_matchCoord_univ :
    tupleEntropy (matchWeight row) (matchCoord row) univ = Real.log #(matchSet row) := by
  classical
  by_cases hne : (matchSet row).Nonempty
  · have hcard : 0 < Fintype.card ↥(matchSet row) := by
      rw [Fintype.card_coe]
      exact Finset.card_pos.mpr hne
    have hinj : Function.Injective (masked (matchCoord row) (univ : Finset (Fin n))) := by
      intro ω ω' h
      have hcoord : ∀ i, (ω : Equiv.Perm (Fin n)) i = (ω' : Equiv.Perm (Fin n)) i := by
        intro i
        have := congrFun h i
        simp only [masked, if_pos (mem_univ i), matchCoord, Option.some_inj] at this
        exact this
      exact Subtype.ext (Equiv.ext hcoord)
    rw [tupleEntropy, ← Fintype.card_coe (matchSet row)]
    exact wentropy_uniform_of_injective hinj hcard
  · -- no matchings at all: both sides are `0`
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hempty : IsEmpty ↥(matchSet row) := by
      refine ⟨fun ω => ?_⟩
      obtain ⟨σ, hσ⟩ := ω
      rw [hne] at hσ
      exact Finset.notMem_empty _ hσ
    have hzero : #(matchSet row) = 0 := by rw [hne, Finset.card_empty]
    rw [tupleEntropy, wentropy, hzero]
    simp only [Nat.cast_zero, Real.log_zero]
    refine Finset.sum_eq_zero fun u _ => ?_
    have : wdist (matchWeight row) (masked (matchCoord row) univ) u = 0 := by
      rw [wdist, wprob, Finset.sum_eq_zero]
      intro ω _
      exact hempty.elim ω
    rw [this, Real.negMulLog_zero]


/-! ### The bound for a fixed order -/

/-- The columns of row `i` that the mask of `i`'s predecessors leaves free. -/
def freeCols (row : Fin n → Finset (Fin n)) (i : Fin n) (u : Fin n → Option (Fin n)) :
    Finset (Fin n) :=
  (row i).filter fun c => ∀ j, u j ≠ some c

/-- A matching's own column for row `i` is free given `i`'s predecessors — it is one of row
`i`'s ones, and no earlier row took it, since `σ` is injective. -/
lemma matchCoord_mem_freeCols (τ : Equiv.Perm (Fin n)) (i : Fin n) (ω : ↥(matchSet row)) :
    matchCoord row i ω
      ∈ freeCols row i (masked (matchCoord row) (predSet τ i) ω) := by
  rw [freeCols, mem_filter]
  refine ⟨(mem_matchSet row).mp ω.2 i, fun j hj => ?_⟩
  simp only [masked] at hj
  by_cases hjP : j ∈ predSet τ i
  · rw [if_pos hjP, Option.some_inj] at hj
    have hji : j ≠ i := by
      intro h
      subst h
      rw [predSet, mem_filter] at hjP
      exact absurd hjP.2 (lt_irrefl _)
    exact hji ((ω : Equiv.Perm (Fin n)).injective hj)
  · rw [if_neg hjP] at hj
    simp at hj

/-- **The free columns are counted by the rank**, in the shape the entropy bound produces. -/
lemma card_freeCols_masked (τ : Equiv.Perm (Fin n)) (i : Fin n) (ω : ↥(matchSet row)) :
    #(freeCols row i (masked (matchCoord row) (predSet τ i) ω))
      = tauRank (hitSet row (ω : Equiv.Perm (Fin n)) i) τ i := by
  rw [← card_avail_eq_tauRank row τ (ω : Equiv.Perm (Fin n)) i, freeCols]
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro c _
  simp only [masked, matchCoord, eq_iff_iff]
  constructor
  · intro h j hj hσj
    exact h j (by rw [if_pos hj, hσj])
  · intro h j hj
    by_cases hjP : j ∈ predSet τ i
    · rw [if_pos hjP] at hj
      exact h j hjP (Option.some_inj.mp hj)
    · rw [if_neg hjP] at hj
      simp at hj

/-- **The bound for one fixed order.** Revealing the rows in the order `τ` and bounding each
row's conditional entropy by the log of the columns still free gives

    log (per A) ≤ ∑ᵢ E_σ [ log Nᵢ(σ, τ) ],

where `Nᵢ` is the rank of `i` in `PMC.hitSet`. The inequality holds for *every* `τ`; the next
step averages it. -/
theorem log_card_matchSet_le (hne : (matchSet row).Nonempty) (τ : Equiv.Perm (Fin n)) :
    Real.log #(matchSet row)
      ≤ ∑ i : Fin n, wmean (matchWeight row)
          (fun ω => Real.log (tauRank (hitSet row (ω : Equiv.Perm (Fin n)) i) τ i)) := by
  classical
  rw [← tupleEntropy_matchCoord_univ row,
    tupleEntropy_univ_eq_sum_predSet (matchWeight_nonneg row) (sum_matchWeight row hne)
      (matchCoord row) τ]
  refine Finset.sum_le_sum fun i _ => ?_
  have hbound := wcondEntropy_le_sum_log_card (matchWeight_nonneg row)
    (masked (matchCoord row) (predSet τ i)) (matchCoord row i) (freeCols row i)
    (matchCoord_mem_freeCols row τ i)
  have hfun : ∀ ω : ↥(matchSet row),
      Real.log (tauRank (hitSet row (ω : Equiv.Perm (Fin n)) i) τ i)
        = Real.log #(freeCols row i (masked (matchCoord row) (predSet τ i) ω)) := by
    intro ω
    rw [card_freeCols_masked row τ i ω]
  have hstep : wmean (matchWeight row)
      (fun ω => Real.log (tauRank (hitSet row (ω : Equiv.Perm (Fin n)) i) τ i))
      = wmean (matchWeight row)
        (fun ω => Real.log #(freeCols row i (masked (matchCoord row) (predSet τ i) ω))) := by
    unfold wmean
    exact Finset.sum_congr rfl fun ω _ =>
      congrArg (fun t => matchWeight row ω * t) (hfun ω)
  rw [hstep, wmean_comp_eq_sum_wdist (matchWeight row)
    (masked (matchCoord row) (predSet τ i)) (fun u => Real.log #(freeCols row i u))]
  exact hbound


/-! ### Averaging over the order, and the inequality -/

/-- **The log form of Brégman–Minc.** Averaging `PMC.log_card_matchSet_le` over a uniformly
random order and using `PMC.wmean_log_tauRank` for each row gives

    log (per A) ≤ ∑ᵢ log (dᵢ!) / dᵢ.

The two expectations are exchanged by `Finset.sum_comm`: the bound holds for each order, and
for each *matching* the rank is uniform as the order varies. -/
theorem log_card_matchSet_le_sum_log_factorial :
    Real.log #(matchSet row)
      ≤ ∑ i : Fin n, Real.log (Nat.factorial #(row i)) / #(row i) := by
  classical
  have hterm_nonneg : ∀ i : Fin n, 0 ≤ Real.log (Nat.factorial #(row i)) / #(row i) := by
    intro i
    have h1 : (1 : ℝ) ≤ Nat.factorial #(row i) := by
      have := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero #(row i))
      exact_mod_cast this
    positivity
  by_cases hne : (matchSet row).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty, Nat.cast_zero, Real.log_zero]
    exact Finset.sum_nonneg fun i _ => hterm_nonneg i
  -- average the fixed-order bound over `τ`
  have hstart : Real.log #(matchSet row)
      = ∑ τ : Equiv.Perm (Fin n), unifPerm (Fin n) τ * Real.log #(matchSet row) := by
    rw [← Finset.sum_mul, sum_unifPerm, one_mul]
  have hbig : ∑ τ : Equiv.Perm (Fin n), unifPerm (Fin n) τ * Real.log #(matchSet row)
      ≤ ∑ τ : Equiv.Perm (Fin n), unifPerm (Fin n) τ
          * ∑ i : Fin n, wmean (matchWeight row)
              (fun ω => Real.log (tauRank (hitSet row (ω : Equiv.Perm (Fin n)) i) τ i)) :=
    Finset.sum_le_sum fun τ _ =>
      mul_le_mul_of_nonneg_left (log_card_matchSet_le row hne τ) (unifPerm_nonneg τ)
  -- exchange the two expectations
  have hrearr : ∑ τ : Equiv.Perm (Fin n), unifPerm (Fin n) τ
        * ∑ i : Fin n, wmean (matchWeight row)
            (fun ω => Real.log (tauRank (hitSet row (ω : Equiv.Perm (Fin n)) i) τ i))
      = ∑ i : Fin n, ∑ ω : ↥(matchSet row), matchWeight row ω
          * wmean (unifPerm (Fin n))
              (fun τ => Real.log (tauRank (hitSet row (ω : Equiv.Perm (Fin n)) i) τ i)) := by
    simp only [wmean, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  -- each inner expectation is `log (dᵢ!) / dᵢ`
  have hinner : ∀ (i : Fin n) (ω : ↥(matchSet row)),
      wmean (unifPerm (Fin n))
          (fun τ => Real.log (tauRank (hitSet row (ω : Equiv.Perm (Fin n)) i) τ i))
        = Real.log (Nat.factorial #(row i)) / #(row i) := by
    intro i ω
    rw [wmean_log_tauRank (mem_hitSet_self row ω.2 i), card_hitSet row]
  have hfinal : ∑ i : Fin n, ∑ ω : ↥(matchSet row), matchWeight row ω
        * wmean (unifPerm (Fin n))
            (fun τ => Real.log (tauRank (hitSet row (ω : Equiv.Perm (Fin n)) i) τ i))
      = ∑ i : Fin n, Real.log (Nat.factorial #(row i)) / #(row i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun ω (_ : ω ∈ (univ : Finset ↥(matchSet row))) =>
      congrArg (fun t => matchWeight row ω * t) (hinner i ω), ← Finset.sum_mul,
      sum_matchWeight row hne, one_mul]
  rw [hstart, ← hfinal, ← hrearr]
  exact hbig

/-- **Theorem 10.2.1 (Brégman–Minc).** A `0-1` matrix whose `i`-th row has `dᵢ` ones has
permanent at most `∏ᵢ (dᵢ!)^{1/dᵢ}`.

Equality holds for a block-diagonal matrix of all-ones blocks, so the bound cannot be
improved. -/
theorem card_matchSet_le_prod :
    (#(matchSet row) : ℝ)
      ≤ ∏ i : Fin n, (Nat.factorial #(row i) : ℝ) ^ (1 / (#(row i) : ℝ)) := by
  have hfacpos : ∀ i : Fin n, (0 : ℝ) < Nat.factorial #(row i) := by
    intro i
    have := Nat.factorial_pos #(row i)
    exact_mod_cast this
  have hRpos : (0 : ℝ) < ∏ i : Fin n, (Nat.factorial #(row i) : ℝ) ^ (1 / (#(row i) : ℝ)) :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hfacpos i) _
  have hlogR : Real.log (∏ i : Fin n, (Nat.factorial #(row i) : ℝ) ^ (1 / (#(row i) : ℝ)))
      = ∑ i : Fin n, Real.log (Nat.factorial #(row i)) / #(row i) := by
    rw [Real.log_prod fun i _ => ne_of_gt (Real.rpow_pos_of_pos (hfacpos i) _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_rpow (hfacpos i), div_mul_eq_mul_div, one_mul]
  rcases Nat.eq_zero_or_pos #(matchSet row) with h0 | hpos
  · rw [h0, Nat.cast_zero]
    exact le_of_lt hRpos
  · have hNpos : (0 : ℝ) < #(matchSet row) := by exact_mod_cast hpos
    rw [← Real.log_le_log_iff hNpos hRpos, hlogR]
    exact log_card_matchSet_le_sum_log_factorial row


/-! ### Corollary 10.2.2 for bipartite graphs

The notes' Corollary 10.2.2 (Kahn–Lovász) is `pm(G) ≤ ∏_v (d_v!)^{1/(2d_v)}` over *all*
vertices. For a bipartite graph it follows from Brégman applied to each side in turn, which
is what is proved here. The non-bipartite case is not: it needs `pm(G ⊔ G) ≤ pm(G × K₂)`,
which the notes leave as an exercise and which is the actual content of Kahn–Lovász.

Applying Brégman to the other side needs the permanent to be transpose-invariant, and that is
the inversion `σ ↦ σ⁻¹`. -/

/-- The rows meeting column `j` — the transpose of `row`. -/
def colOf (row : Fin n → Finset (Fin n)) (j : Fin n) : Finset (Fin n) :=
  (univ : Finset (Fin n)).filter fun i => j ∈ row i

/-- **The permanent is transpose-invariant**, by `σ ↦ σ⁻¹`. -/
theorem card_matchSet_colOf : #(matchSet (colOf row)) = #(matchSet row) := by
  refine Finset.card_bij' (fun σ _ => σ⁻¹) (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [mem_matchSet] at hσ ⊢
    intro i
    have h := hσ (σ⁻¹ i)
    rw [colOf, mem_filter] at h
    have hsi : σ (σ⁻¹ i) = i := by simp
    rw [hsi] at h
    exact h.2
  · intro σ hσ
    rw [mem_matchSet] at hσ ⊢
    intro j
    rw [colOf, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have h := hσ (σ⁻¹ j)
    have hsj : σ (σ⁻¹ j) = j := by simp
    rw [hsj] at h
    exact h
  · intro σ _
    exact inv_inv σ
  · intro σ _
    exact inv_inv σ

/-- **Corollary 10.2.2 for bipartite graphs.** The number of perfect matchings satisfies

    pm(G)² ≤ ∏_{x ∈ X} (d_x!)^{1/d_x} · ∏_{y ∈ Y} (d_y!)^{1/d_y},

i.e. `pm(G) ≤ ∏_{v} (d_v!)^{1/(2d_v)}` over all `2n` vertices. Brégman on each side. -/
theorem card_matchSet_sq_le_prod :
    (#(matchSet row) : ℝ) ^ 2
      ≤ (∏ i : Fin n, (Nat.factorial #(row i) : ℝ) ^ (1 / (#(row i) : ℝ)))
        * ∏ j : Fin n, (Nat.factorial #(colOf row j) : ℝ) ^ (1 / (#(colOf row j) : ℝ)) := by
  have h1 := card_matchSet_le_prod row
  have h2 := card_matchSet_le_prod (colOf row)
  rw [card_matchSet_colOf row] at h2
  have hnn : (0 : ℝ) ≤ #(matchSet row) := Nat.cast_nonneg _
  calc (#(matchSet row) : ℝ) ^ 2 = (#(matchSet row) : ℝ) * #(matchSet row) := by ring
    _ ≤ (∏ i : Fin n, (Nat.factorial #(row i) : ℝ) ^ (1 / (#(row i) : ℝ)))
          * ∏ j : Fin n, (Nat.factorial #(colOf row j) : ℝ) ^ (1 / (#(colOf row j) : ℝ)) :=
        mul_le_mul h1 h2 hnn (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _)


end Bregman

end PMC
