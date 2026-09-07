import ProbMethods.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# §3.1 — Dominating sets

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 3.1.1.
-/

open Finset

namespace PMC

section Bernoulli

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Bernoulli-`p` weight of a vertex subset: a factor `p` for each vertex taken and
`1 - p` for each vertex left out.

Summed over all subsets these weights give `1` (`PMC.sum_wt`), so averaging against them
is ordinary finite averaging — the distribution is not uniform, but no measure theory is
needed. -/
private noncomputable def wt (p : ℝ) (X : Finset V) : ℝ :=
  p ^ #X * (1 - p) ^ #((univ : Finset V) \ X)

private lemma wt_def (p : ℝ) (X : Finset V) :
    wt p X = p ^ #X * (1 - p) ^ #((univ : Finset V) \ X) := rfl

private lemma wt_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (X : Finset V) : 0 < wt p X :=
  mul_pos (pow_pos hp0 _) (pow_pos (by linarith) _)

/-- The weights form a probability distribution. -/
private lemma sum_wt (p : ℝ) : ∑ X ∈ (univ : Finset V).powerset, wt p X = 1 := by
  have h := Finset.prod_add (fun _ : V => p) (fun _ : V => 1 - p) univ
  simp only [prod_const] at h
  rw [show p + (1 - p) = 1 from by ring, one_pow] at h
  simp only [wt_def]
  exact h.symm

omit [Fintype V] in
/-- Zeroing out the factors on `B` kills exactly the subsets meeting `B`. -/
private lemma prod_ite_mem_eq (p : ℝ) (B t : Finset V) :
    (∏ i ∈ t, (if i ∈ B then (0 : ℝ) else p)) = if Disjoint t B then p ^ #t else 0 := by
  by_cases hd : Disjoint t B
  · rw [if_pos hd, Finset.prod_congr rfl fun i hi =>
      if_neg (Finset.disjoint_left.1 hd hi), prod_const]
  · rw [if_neg hd]
    rw [Finset.not_disjoint_iff] at hd
    obtain ⟨i, hit, hiB⟩ := hd
    exact Finset.prod_eq_zero hit (if_pos hiB)

/-- **The mass of the subsets avoiding `B` is `(1 - p) ^ #B`.** -/
private lemma sum_wt_disjoint (p : ℝ) (B : Finset V) :
    ∑ X ∈ (univ : Finset V).powerset, (if Disjoint X B then wt p X else 0)
      = (1 - p) ^ #B := by
  have hfilter : (univ : Finset V).filter (· ∈ B) = B := by ext x; simp
  have h := Finset.prod_add (fun i : V => if i ∈ B then (0 : ℝ) else p)
    (fun _ : V => 1 - p) univ
  have hL : ∏ i ∈ (univ : Finset V), ((if i ∈ B then (0 : ℝ) else p) + (1 - p))
      = (1 - p) ^ #B := by
    have hpt : ∀ i ∈ (univ : Finset V),
        ((if i ∈ B then (0 : ℝ) else p) + (1 - p)) = (if i ∈ B then (1 - p) else 1) := by
      intro i _; split_ifs <;> ring
    rw [Finset.prod_congr rfl hpt, ← Finset.prod_filter, hfilter, prod_const]
  have hR : ∀ t ∈ (univ : Finset V).powerset,
      (∏ i ∈ t, (if i ∈ B then (0 : ℝ) else p)) * ∏ _i ∈ (univ : Finset V) \ t, (1 - p)
        = if Disjoint t B then wt p t else 0 := by
    intro t _
    rw [prod_const, prod_ite_mem_eq]
    by_cases hd : Disjoint t B
    · rw [if_pos hd, if_pos hd, wt_def]
    · rw [if_neg hd, if_neg hd, zero_mul]
  rw [Finset.sum_congr rfl hR, hL] at h
  exact h.symm

/-- Zeroing out the `1 - p` factor at `v` kills exactly the subsets omitting `v`. -/
private lemma prod_ite_eq_zero (p : ℝ) (v : V) (t : Finset V) :
    (∏ i ∈ (univ : Finset V) \ t, (if i = v then (0 : ℝ) else 1 - p))
      = if v ∈ t then (1 - p) ^ #((univ : Finset V) \ t) else 0 := by
  by_cases hv : v ∈ t
  · rw [if_pos hv, Finset.prod_congr rfl fun i hi =>
      if_neg (fun hiv => (mem_sdiff.1 hi).2 (hiv ▸ hv)), prod_const]
  · rw [if_neg hv]
    exact Finset.prod_eq_zero (mem_sdiff.2 ⟨mem_univ v, hv⟩) (if_pos rfl)

/-- **The mass of the subsets containing `v` is `p`.** -/
private lemma sum_wt_mem (p : ℝ) (v : V) :
    ∑ X ∈ (univ : Finset V).powerset, (if v ∈ X then wt p X else 0) = p := by
  have h := Finset.prod_add (fun _ : V => p)
    (fun i : V => if i = v then (0 : ℝ) else 1 - p) univ
  have hL : ∏ i ∈ (univ : Finset V), (p + if i = v then (0 : ℝ) else 1 - p) = p := by
    rw [Finset.prod_eq_single_of_mem v (mem_univ v)]
    · rw [if_pos rfl, add_zero]
    · intro b _ hbv
      rw [if_neg hbv]
      ring
  have hR : ∀ t ∈ (univ : Finset V).powerset,
      (∏ _i ∈ t, p) * ∏ i ∈ (univ : Finset V) \ t, (if i = v then (0 : ℝ) else 1 - p)
        = if v ∈ t then wt p t else 0 := by
    intro t _
    rw [prod_const, prod_ite_eq_zero]
    by_cases hv : v ∈ t
    · rw [if_pos hv, if_pos hv, wt_def]
    · rw [if_neg hv, if_neg hv, mul_zero]
  rw [Finset.sum_congr rfl hR, hL] at h
  exact h.symm

end Bernoulli

section Alteration

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two-step alteration: keep `X`, then add every vertex that `X` fails to dominate.
The result is dominating by construction. -/
private def closeUp (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : Finset V :=
  {v ∈ (univ : Finset V) | v ∈ X ∨ Disjoint X (insert v (G.neighborFinset v))}

private lemma mem_closeUp {G : SimpleGraph V} [DecidableRel G.Adj] {X : Finset V} {v : V} :
    v ∈ closeUp G X ↔ v ∈ X ∨ Disjoint X (insert v (G.neighborFinset v)) := by
  simp [closeUp]

private lemma isDominating_closeUp (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) : IsDominating G (closeUp G X) := by
  intro v hv
  rw [mem_closeUp, not_or] at hv
  obtain ⟨hvX, hnd⟩ := hv
  rw [Finset.not_disjoint_iff] at hnd
  obtain ⟨u, huX, huN⟩ := hnd
  rw [mem_insert, SimpleGraph.mem_neighborFinset] at huN
  refine ⟨u, mem_closeUp.2 (Or.inl huX), ?_⟩
  rcases huN with rfl | h
  · exact absurd huX hvX
  · exact h

/-- The expected size of `closeUp G X` is at most `n * (p + (1 - p) ^ (1 + δ))`: each
vertex survives either by being chosen (mass `p`) or by having its whole closed
neighbourhood missed (mass `(1 - p) ^ (1 + deg v)`), and those are disjoint events. -/
private lemma sum_wt_card_closeUp_le (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {δ : ℕ} (hdeg : ∀ v, δ ≤ G.degree v) :
    ∑ X ∈ (univ : Finset V).powerset, wt p X * #(closeUp G X)
      ≤ (Fintype.card V : ℝ) * (p + (1 - p) ^ (1 + δ)) := by
  have hone : (0 : ℝ) ≤ 1 - p := by linarith
  -- Expand `#(closeUp G X)` as a sum of indicators and exchange the two sums.
  have hexpand : ∑ X ∈ (univ : Finset V).powerset, wt p X * #(closeUp G X)
      = ∑ v : V, ∑ X ∈ (univ : Finset V).powerset,
          ((if v ∈ X then wt p X else 0)
            + (if Disjoint X (insert v (G.neighborFinset v)) then wt p X else 0)) := by
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [closeUp, card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hA : v ∈ X
    · have hnd : ¬ Disjoint X (insert v (G.neighborFinset v)) := fun hd =>
        (Finset.disjoint_left.1 hd hA) (mem_insert_self v _)
      rw [if_pos (Or.inl hA), if_pos hA, if_neg hnd, Nat.cast_one, mul_one, add_zero]
    · by_cases hB : Disjoint X (insert v (G.neighborFinset v))
      · rw [if_pos (Or.inr hB), if_pos hB, if_neg hA, Nat.cast_one, mul_one, zero_add]
      · rw [if_neg (not_or.2 ⟨hA, hB⟩), if_neg hA, if_neg hB, Nat.cast_zero, mul_zero,
          add_zero]
  rw [hexpand]
  -- Each vertex contributes `p + (1 - p) ^ (1 + deg v) ≤ p + (1 - p) ^ (1 + δ)`.
  have hvertex : ∀ v : V, ∑ X ∈ (univ : Finset V).powerset,
      ((if v ∈ X then wt p X else 0)
        + (if Disjoint X (insert v (G.neighborFinset v)) then wt p X else 0))
      ≤ p + (1 - p) ^ (1 + δ) := by
    intro v
    rw [Finset.sum_add_distrib, sum_wt_mem, sum_wt_disjoint]
    have hcard : #(insert v (G.neighborFinset v)) = 1 + G.degree v := by
      rw [card_insert_of_notMem (G.notMem_neighborFinset_self v),
        SimpleGraph.card_neighborFinset_eq_degree, Nat.add_comm]
    rw [hcard]
    have : (1 - p) ^ (1 + G.degree v) ≤ (1 - p) ^ (1 + δ) :=
      pow_le_pow_of_le_one hone (by linarith) (by have := hdeg v; omega)
    linarith
  calc ∑ v : V, ∑ X ∈ (univ : Finset V).powerset,
        ((if v ∈ X then wt p X else 0)
          + (if Disjoint X (insert v (G.neighborFinset v)) then wt p X else 0))
      ≤ ∑ _v : V, (p + (1 - p) ^ (1 + δ)) := Finset.sum_le_sum fun v _ => hvertex v
    _ = (Fintype.card V : ℝ) * (p + (1 - p) ^ (1 + δ)) := by
        rw [sum_const, card_univ, nsmul_eq_mul]

end Alteration

/-- **Small dominating sets** (Zhao, Theorem 3.1.1).

Every graph with minimum degree `δ > 1` has a dominating set of size at most
`((log (δ + 1) + 1) / (δ + 1)) * n`.

The book's proof is the alteration method in two steps. Include each vertex of `V`
independently with probability `p`, giving a set `X`; then let `Y` be the vertices that
neither lie in `X` nor have a neighbour in `X`, so that `X ∪ Y` is dominating by
construction. A vertex lands in `Y` with probability at most `(1 - p) ^ (1 + δ)`, so

    E|X ∪ Y| ≤ p * n + (1 - p) ^ (1 + δ) * n ≤ (p + exp (-p * (1 + δ))) * n

using `1 + x ≤ exp x`. Setting `p = log (δ + 1) / (δ + 1)` minimises the bracket and gives
the stated bound.

**Note on the formalization.** The distribution here is *not* uniform — it is
`Bernoulli p` with `p` generally irrational — so this is the first node in the project that
the pure counting convention does not cover. It does not need `MeasureTheory` either: over
a finite vertex set the expectation is a finite weighted sum
`∑ X ⊆ univ, p ^ #X * (1 - p) ^ (n - #X) * f X`, and `Finset.prod_add` supplies
`∑ X, p ^ #X * (1 - p) ^ (n - #X) = (p + (1 - p)) ^ n = 1`. Averaging against those
weights is the whole probabilistic content. -/
theorem exists_isDominating_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {δ : ℕ} (hδ : 1 < δ)
    (hdeg : ∀ v, δ ≤ G.degree v) :
    ∃ U : Finset V, IsDominating G U ∧
      (#U : ℝ) ≤ (Real.log (δ + 1) + 1) / (δ + 1) * Fintype.card V := by
  have hd1 : (0 : ℝ) < (δ : ℝ) + 1 := by positivity
  have hδ1 : (1 : ℝ) < (δ : ℝ) + 1 := by
    have : (1 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
    linarith
  set p : ℝ := Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1) with hpdef
  have hlogpos : 0 < Real.log ((δ : ℝ) + 1) := Real.log_pos hδ1
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hp1 : p < 1 := by
    rw [hpdef, div_lt_one hd1]
    have := Real.log_le_sub_one_of_pos hd1
    linarith
  -- `(1 - p) ^ (1 + δ) ≤ 1 / (δ + 1)`, with equality in the exponential step.
  have hexp : (1 - p) ^ (1 + δ) ≤ 1 / ((δ : ℝ) + 1) := by
    have h1 : (1 : ℝ) - p ≤ Real.exp (-p) := by
      have := Real.add_one_le_exp (-p); linarith
    have h2 : (1 - p) ^ (1 + δ) ≤ Real.exp (-p) ^ (1 + δ) := by
      gcongr
    have h3 : Real.exp (-p) ^ (1 + δ) = 1 / ((δ : ℝ) + 1) := by
      rw [← Real.exp_nat_mul]
      rw [show ((1 + δ : ℕ) : ℝ) * -p = -Real.log ((δ : ℝ) + 1) by
        rw [hpdef]; push_cast; field_simp; ring]
      rw [Real.exp_neg, Real.exp_log hd1, one_div]
    linarith
  -- The average of `#(closeUp G X)` is below the target bound.
  have hEbound : ∑ X ∈ (univ : Finset V).powerset, wt p X * #(closeUp G X)
      ≤ (Real.log ((δ : ℝ) + 1) + 1) / ((δ : ℝ) + 1) * Fintype.card V := by
    refine (sum_wt_card_closeUp_le G hp0.le hp1.le hdeg).trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
    rw [add_div, ← hpdef]
    linarith
  -- Averaging: some `X` is at least as good as the average.
  obtain ⟨X, -, hX⟩ := Finset.exists_le_of_sum_le (s := (univ : Finset V).powerset)
    ⟨∅, by simp⟩
    (f := fun X => (#(closeUp G X) : ℝ) * wt p X)
    (g := fun X => ((Real.log ((δ : ℝ) + 1) + 1) / ((δ : ℝ) + 1) * Fintype.card V) * wt p X)
    (by
      rw [← Finset.mul_sum, sum_wt, mul_one]
      refine le_trans ?_ hEbound
      exact le_of_eq (Finset.sum_congr rfl fun X _ => mul_comm _ _))
  refine ⟨closeUp G X, isDominating_closeUp G X, ?_⟩
  exact le_of_mul_le_mul_right hX (wt_pos hp0 hp1 X)

end PMC
