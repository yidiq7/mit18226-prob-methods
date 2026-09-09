import ProbMethods.Weighted

/-!
# §4.2 — the variance of a sum of indicators (Setup 4.2.2)

Zhao, *Probabilistic Methods in Combinatorics*, Setup 4.2.2 and Lemma 4.2.4. The second-moment
method needs the variance of `X = ∑ᵢ 1_{Aᵢ}` for a family of events with a *dependency
structure*: pairs of events that are independent contribute nothing, so

    Var X ≤ E X + ∑ᵢ ∑_{j ∈ N i} P(Aᵢ ∩ A_j),

where `N i` lists the indices `j ≠ i` whose event may depend on `Aᵢ`. The notes write the
second term as `μ Δ*` with `Δ* = maxᵢ ∑_{j ∈ N i} P(A_j | Aᵢ)`; dividing is avoided here by
keeping the double sum, and the `Δ*` form follows by bounding each inner sum.

**Why this is worth having.** Every second-moment threshold in §4.2 and §4.4 — Theorem 4.2.5's
other direction, Theorem 4.2.10's other direction, Theorem 4.4.2(b) — is this bound followed by
`PMC.tendsto_wprob_zero_of_var_div_sq_mean`. §4.1's triangle case was done by hand
(`PMC.wvar_card_triangles_le'`), and that proof is exactly this bound specialised, so having it
once in general is what makes the remaining thresholds reachable.

Note the shape of the independence hypothesis: it constrains only the pairs *outside* the
dependency lists, which is what makes the bound usable — the whole point is that the `N i` are
small and nothing has to be known about the pairs inside them.
-/

open Finset

namespace PMC

section DeltaStar

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of events of the family that occur at `ω`. -/
def occCount (A : ι → Finset Ω) (ω : Ω) : ℝ :=
  #((univ : Finset ι).filter fun i => ω ∈ A i)

/-- The indicator of `S`, weighted and summed, is exactly `wprob w S`. -/
private lemma sum_mul_indicator (w : Ω → ℝ) (S : Finset Ω) :
    ∑ ω, w ω * (if ω ∈ S then (1 : ℝ) else 0) = wprob w S := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, wprob]

omit [Fintype Ω] [DecidableEq ι] in
/-- `occCount` is the sum of the indicators of the events. -/
private lemma occCount_eq_sum (A : ι → Finset Ω) (ω : Ω) :
    occCount A ω = ∑ i, if ω ∈ A i then (1 : ℝ) else 0 := by
  rw [occCount, Finset.sum_boole]

omit [DecidableEq ι] in
/-- The mean of the count is the sum of the probabilities: linearity of expectation. -/
private lemma wmean_occCount (w : Ω → ℝ) (A : ι → Finset Ω) :
    wmean w (occCount A) = ∑ i, wprob w (A i) := by
  simp only [wmean, occCount_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_mul_indicator w (A i)

omit [DecidableEq ι] in
/-- The second moment of the count is the sum of the pair probabilities. -/
private lemma wmean_occCount_sq (w : Ω → ℝ) (A : ι → Finset Ω) :
    wmean w (fun ω => occCount A ω ^ 2) = ∑ i, ∑ j, wprob w (A i ∩ A j) := by
  have hsq : ∀ ω, occCount A ω ^ 2 = ∑ i, ∑ j, if ω ∈ A i ∩ A j then (1 : ℝ) else 0 := by
    intro ω
    rw [pow_two, occCount_eq_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h1 : ω ∈ A i <;> by_cases h2 : ω ∈ A j <;> simp [h1, h2]
  simp only [wmean, hsq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => sum_mul_indicator w (A i ∩ A j)

/-- **Setup 4.2.2's variance bound.** For a family of events whose non-adjacent pairs are
independent,

    Var (∑ᵢ 1_{Aᵢ}) ≤ ∑ᵢ P(Aᵢ) + ∑ᵢ ∑_{j ∈ N i} P(Aᵢ ∩ A_j).

The two terms are the notes' `μ` and `μ Δ*`. The diagonal `i = j` contributes
`P(Aᵢ) - P(Aᵢ)² ≤ P(Aᵢ)`, the independent pairs contribute exactly `0`, and the dependent
pairs are bounded by dropping the `-P(Aᵢ)P(A_j)`. -/
theorem wvar_occCount_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (A : ι → Finset Ω) (N : ι → Finset ι) (hself : ∀ i, i ∉ N i)
    (hindep : ∀ i j, i ≠ j → j ∉ N i →
      wprob w (A i ∩ A j) = wprob w (A i) * wprob w (A j)) :
    wvar w (occCount A) ≤ (∑ i, wprob w (A i)) + ∑ i, ∑ j ∈ N i, wprob w (A i ∩ A j) := by
  -- `Var X = ∑ᵢ ∑ⱼ (P(Aᵢ ∩ Aⱼ) - P(Aᵢ) P(Aⱼ))`, the second moment minus the square of the mean.
  have hvar : wvar w (occCount A)
      = ∑ i, ∑ j, (wprob w (A i ∩ A j) - wprob w (A i) * wprob w (A j)) := by
    rw [wvar_eq_wmean_sq_sub w _ hsum, wmean_occCount_sq, wmean_occCount, pow_two,
      Finset.sum_mul_sum]
    simp only [← Finset.sum_sub_distrib]
  rw [hvar, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  -- Outside `insert i (N i)` every term vanishes, by independence.
  have hzero : ∀ j ∈ (univ : Finset ι), j ∉ insert i (N i) →
      wprob w (A i ∩ A j) - wprob w (A i) * wprob w (A j) = 0 := by
    intro j _ hj
    rw [Finset.mem_insert, not_or] at hj
    exact sub_eq_zero_of_eq (hindep i j (Ne.symm hj.1) hj.2)
  rw [← Finset.sum_subset (Finset.subset_univ (insert i (N i))) hzero,
    Finset.sum_insert (hself i), Finset.inter_self]
  -- The diagonal gives `P(Aᵢ) - P(Aᵢ)² ≤ P(Aᵢ)`; each dependent pair drops its `-P(Aᵢ)P(Aⱼ)`.
  exact add_le_add (sub_le_self _ (mul_nonneg (wprob_nonneg hw (A i)) (wprob_nonneg hw (A i))))
    (Finset.sum_le_sum fun j _ =>
      sub_le_self _ (mul_nonneg (wprob_nonneg hw (A i)) (wprob_nonneg hw (A j))))

end DeltaStar

end PMC
