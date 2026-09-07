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

variable {V : Type*} [Fintype V] [DecidableEq V] {p : ℝ}

/-- The Bernoulli weights on subsets sum to `1`: this is `Finset.prod_add` with both
factors constant. It is what makes the finite weighted average below a genuine
expectation, with no measure theory involved. -/
private lemma sum_bernoulli (S : Finset V) (p : ℝ) :
    ∑ X ∈ S.powerset, p ^ #X * (1 - p) ^ (#S - #X) = 1 := by
  have h := Finset.prod_add (fun _ : V => p) (fun _ : V => 1 - p) S
  calc ∑ X ∈ S.powerset, p ^ #X * (1 - p) ^ (#S - #X)
      = ∑ X ∈ S.powerset, (∏ _i ∈ X, p) * ∏ _i ∈ S \ X, (1 - p) := by
        refine Finset.sum_congr rfl fun X hX => ?_
        rw [mem_powerset] at hX
        rw [prod_const, prod_const, card_sdiff_of_subset hX]
    _ = ∏ _i ∈ S, (p + (1 - p)) := h.symm
    _ = 1 := by simp

/-- The weight of the subsets avoiding a fixed `B` is `(1 - p) ^ #B`. -/
private lemma sum_bernoulli_avoid (B : Finset V) (p : ℝ) :
    ∑ X ∈ (univ \ B).powerset, p ^ #X * (1 - p) ^ (Fintype.card V - #X)
      = (1 - p) ^ #B := by
  have hcard : #(univ \ B) = Fintype.card V - #B := by
    rw [card_sdiff_of_subset (subset_univ B), card_univ]
  have hBle : #B ≤ Fintype.card V := by
    rw [← card_univ]; exact card_le_univ B
  calc ∑ X ∈ (univ \ B).powerset, p ^ #X * (1 - p) ^ (Fintype.card V - #X)
      = ∑ X ∈ (univ \ B).powerset,
          (p ^ #X * (1 - p) ^ (#(univ \ B) - #X)) * (1 - p) ^ #B := by
        refine Finset.sum_congr rfl fun X hX => ?_
        rw [mem_powerset] at hX
        have hXle : #X ≤ #(univ \ B) := card_le_card hX
        rw [mul_assoc, ← pow_add]
        congr 2
        omega
    _ = (∑ X ∈ (univ \ B).powerset, p ^ #X * (1 - p) ^ (#(univ \ B) - #X)) * (1 - p) ^ #B := by
        rw [Finset.sum_mul]
    _ = (1 - p) ^ #B := by rw [sum_bernoulli, one_mul]

/-- The weight total is `1`, over all subsets of the vertex set. -/
private lemma sum_bernoulli_univ (p : ℝ) :
    ∑ X ∈ (univ : Finset V).powerset, p ^ #X * (1 - p) ^ (Fintype.card V - #X) = 1 := by
  have h := sum_bernoulli (univ : Finset V) p
  rwa [card_univ] at h

/-- The subsets disjoint from `B` carry weight `(1 - p) ^ #B`. -/
private lemma sum_bernoulli_disjoint (B : Finset V) (p : ℝ) :
    ∑ X ∈ (univ : Finset V).powerset.filter (fun X => Disjoint X B),
        p ^ #X * (1 - p) ^ (Fintype.card V - #X) = (1 - p) ^ #B := by
  have hset : (univ : Finset V).powerset.filter (fun X => Disjoint X B)
      = (univ \ B).powerset := by
    ext X
    simp only [mem_filter, mem_powerset, subset_univ, true_and, subset_sdiff]
  rw [hset]
  exact sum_bernoulli_avoid B p

/-- The subsets containing `v` carry weight `p`: what is left after removing those that
avoid `v`. -/
private lemma sum_bernoulli_mem (v : V) (p : ℝ) :
    ∑ X ∈ (univ : Finset V).powerset.filter (fun X => v ∈ X),
        p ^ #X * (1 - p) ^ (Fintype.card V - #X) = p := by
  have havoid : ∑ X ∈ (univ : Finset V).powerset.filter (fun X => ¬ v ∈ X),
      p ^ #X * (1 - p) ^ (Fintype.card V - #X) = 1 - p := by
    have hset : (univ : Finset V).powerset.filter (fun X => ¬ v ∈ X)
        = (univ : Finset V).powerset.filter (fun X => Disjoint X ({v} : Finset V)) := by
      ext X
      simp [disjoint_singleton_right]
    rw [hset, sum_bernoulli_disjoint, card_singleton, pow_one]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((univ : Finset V).powerset) (fun X => v ∈ X)
    (fun X => p ^ #X * (1 - p) ^ (Fintype.card V - #X))
  rw [sum_bernoulli_univ, havoid] at hsplit
  linarith

end Bernoulli

section Alteration

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- What `X` fails to dominate: the vertices `v` with `X` missing `v` and all its
neighbours. -/
private def leftover (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : Finset V :=
  univ.filter fun v => Disjoint X (insert v (G.neighborFinset v))

/-- `X` repaired: together with what it fails to dominate. Dominating by construction. -/
private def repaired (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : Finset V :=
  X ∪ leftover G X

private lemma mem_repaired {G : SimpleGraph V} [DecidableRel G.Adj] {X : Finset V} {v : V} :
    v ∈ repaired G X ↔ v ∈ X ∨ Disjoint X (insert v (G.neighborFinset v)) := by
  simp [repaired, leftover]

private lemma isDominating_repaired (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) : IsDominating G (repaired G X) := by
  intro v hv
  rw [mem_repaired, not_or] at hv
  obtain ⟨hvX, hdis⟩ := hv
  rw [Finset.not_disjoint_iff] at hdis
  obtain ⟨u, huX, huv⟩ := hdis
  rw [mem_insert] at huv
  rcases huv with rfl | huv
  · exact absurd huX hvX
  · exact ⟨u, mem_repaired.mpr (Or.inl huX), (G.mem_neighborFinset _ _).mp huv⟩

/-- The two ways a vertex can end up in `repaired G X` are disjoint, and together they are
exactly membership. -/
private lemma indicator_repaired (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (X : Finset V) :
    (if v ∈ repaired G X then (1 : ℝ) else 0)
      = (if v ∈ X then (1 : ℝ) else 0)
        + (if Disjoint X (insert v (G.neighborFinset v)) then (1 : ℝ) else 0) := by
  by_cases h1 : v ∈ X
  · have h2 : ¬ Disjoint X (insert v (G.neighborFinset v)) := by
      rw [Finset.not_disjoint_iff]
      exact ⟨v, h1, mem_insert_self _ _⟩
    simp [mem_repaired, h1, h2]
  · by_cases h2 : Disjoint X (insert v (G.neighborFinset v)) <;>
      simp [mem_repaired, h1, h2]

/-- A vertex survives into the repaired set with weight `p + (1 - p) ^ (1 + degree v)`. -/
private lemma sum_weight_indicator (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (p : ℝ) :
    ∑ X ∈ (univ : Finset V).powerset,
        (p ^ #X * (1 - p) ^ (Fintype.card V - #X))
          * (if v ∈ repaired G X then (1 : ℝ) else 0)
      = p + (1 - p) ^ (1 + G.degree v) := by
  have hcardB : #(insert v (G.neighborFinset v)) = 1 + G.degree v := by
    rw [card_insert_of_notMem (G.notMem_neighborFinset_self v),
      SimpleGraph.card_neighborFinset_eq_degree]
    omega
  calc ∑ X ∈ (univ : Finset V).powerset,
        (p ^ #X * (1 - p) ^ (Fintype.card V - #X))
          * (if v ∈ repaired G X then (1 : ℝ) else 0)
      = ∑ X ∈ (univ : Finset V).powerset,
          ((p ^ #X * (1 - p) ^ (Fintype.card V - #X))
              * (if v ∈ X then (1 : ℝ) else 0)
            + (p ^ #X * (1 - p) ^ (Fintype.card V - #X))
              * (if Disjoint X (insert v (G.neighborFinset v)) then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl fun X _ => ?_
        rw [indicator_repaired, mul_add]
    _ = (∑ X ∈ (univ : Finset V).powerset,
            (p ^ #X * (1 - p) ^ (Fintype.card V - #X)) * (if v ∈ X then (1 : ℝ) else 0))
          + ∑ X ∈ (univ : Finset V).powerset,
            (p ^ #X * (1 - p) ^ (Fintype.card V - #X))
              * (if Disjoint X (insert v (G.neighborFinset v)) then (1 : ℝ) else 0) :=
        Finset.sum_add_distrib
    _ = p + (1 - p) ^ (1 + G.degree v) := by
        have e1 : ∑ X ∈ (univ : Finset V).powerset,
            (p ^ #X * (1 - p) ^ (Fintype.card V - #X)) * (if v ∈ X then (1 : ℝ) else 0)
              = ∑ X ∈ (univ : Finset V).powerset.filter (fun X => v ∈ X),
                p ^ #X * (1 - p) ^ (Fintype.card V - #X) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun X _ => ?_
          by_cases h : v ∈ X <;> simp [h]
        have e2 : ∑ X ∈ (univ : Finset V).powerset,
            (p ^ #X * (1 - p) ^ (Fintype.card V - #X))
              * (if Disjoint X (insert v (G.neighborFinset v)) then (1 : ℝ) else 0)
              = ∑ X ∈ (univ : Finset V).powerset.filter
                  (fun X => Disjoint X (insert v (G.neighborFinset v))),
                p ^ #X * (1 - p) ^ (Fintype.card V - #X) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun X _ => ?_
          by_cases h : Disjoint X (insert v (G.neighborFinset v)) <;> simp [h]
        rw [e1, e2, sum_bernoulli_mem, sum_bernoulli_disjoint, hcardB]

/-- The alteration bound with the inclusion probability left as a parameter. -/
private lemma exists_isDominating_le_of_prob (G : SimpleGraph V) [DecidableRel G.Adj]
    {δ : ℕ} (hdeg : ∀ v, δ ≤ G.degree v) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ U : Finset V, IsDominating G U ∧
      (#U : ℝ) ≤ (p + (1 - p) ^ (1 + δ)) * Fintype.card V := by
  classical
  have h1p : (0 : ℝ) < 1 - p := by linarith
  set w : Finset V → ℝ := fun X => p ^ #X * (1 - p) ^ (Fintype.card V - #X) with hwdef
  have hwpos : ∀ X : Finset V, 0 < w X := fun X =>
    mul_pos (pow_pos hp0 _) (pow_pos h1p _)
  have htot : ∑ X ∈ (univ : Finset V).powerset, w X = 1 := sum_bernoulli_univ p
  -- Rewrite the repaired size as a sum of indicators, then exchange.
  have hcardsum : ∀ X : Finset V,
      (#(repaired G X) : ℝ) = ∑ v : V, (if v ∈ repaired G X then (1 : ℝ) else 0) := by
    intro X
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hexp : ∑ X ∈ (univ : Finset V).powerset, w X * (#(repaired G X) : ℝ)
      = ∑ v : V, (p + (1 - p) ^ (1 + G.degree v)) := by
    calc ∑ X ∈ (univ : Finset V).powerset, w X * (#(repaired G X) : ℝ)
        = ∑ X ∈ (univ : Finset V).powerset, ∑ v : V,
            w X * (if v ∈ repaired G X then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun X _ => ?_
          rw [hcardsum, Finset.mul_sum]
      _ = ∑ v : V, ∑ X ∈ (univ : Finset V).powerset,
            w X * (if v ∈ repaired G X then (1 : ℝ) else 0) := Finset.sum_comm
      _ = ∑ v : V, (p + (1 - p) ^ (1 + G.degree v)) :=
          Finset.sum_congr rfl fun v _ => sum_weight_indicator G v p
  -- Bound each vertex's contribution using the minimum degree.
  have hbound : ∑ v : V, (p + (1 - p) ^ (1 + G.degree v))
      ≤ (p + (1 - p) ^ (1 + δ)) * Fintype.card V := by
    calc ∑ v : V, (p + (1 - p) ^ (1 + G.degree v))
        ≤ ∑ _v : V, (p + (1 - p) ^ (1 + δ)) := by
          refine Finset.sum_le_sum fun v _ => ?_
          have := pow_le_pow_of_le_one h1p.le (by linarith) (by have := hdeg v; omega : 1 + δ ≤ 1 + G.degree v)
          linarith
      _ = (p + (1 - p) ^ (1 + δ)) * Fintype.card V := by
          rw [Finset.sum_const, card_univ, nsmul_eq_mul, mul_comm]
  -- Average: some `X` is at least as good as the weighted mean.
  have hle : ∑ X ∈ (univ : Finset V).powerset, w X * (#(repaired G X) : ℝ)
      ≤ ∑ X ∈ (univ : Finset V).powerset,
          w X * ((p + (1 - p) ^ (1 + δ)) * Fintype.card V) := by
    rw [← Finset.sum_mul, htot, one_mul, hexp]
    exact hbound
  obtain ⟨X, -, hX⟩ := Finset.exists_le_of_sum_le
    ⟨∅, by simp⟩ hle
  exact ⟨repaired G X, isDominating_repaired G X,
    le_of_mul_le_mul_left (by linarith [hX]) (hwpos X)⟩

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
  have hδR : (1 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδpos : (0 : ℝ) < (δ : ℝ) + 1 := by linarith
  have hδ1 : (1 : ℝ) < (δ : ℝ) + 1 := by linarith
  have hlogpos : 0 < Real.log ((δ : ℝ) + 1) := Real.log_pos hδ1
  have hp0 : 0 < Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1) := div_pos hlogpos hδpos
  have hp1 : Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1) < 1 := by
    rw [div_lt_one hδpos]
    have h := Real.log_lt_sub_one_of_pos hδpos (by linarith : (δ : ℝ) + 1 ≠ 1)
    linarith
  obtain ⟨U, hUdom, hUcard⟩ := exists_isDominating_le_of_prob G hdeg
    (p := Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1)) hp0 hp1
  refine ⟨U, hUdom, hUcard.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))⟩
  -- `1 - p ≤ exp (-p)`, and `exp (-p (1 + δ)) = 1 / (δ + 1)` exactly.
  have h1 : 1 - Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1)
      ≤ Real.exp (-(Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1))) := by
    have := Real.add_one_le_exp (-(Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1)))
    linarith
  have h2 : (1 - Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1)) ^ (1 + δ)
      ≤ Real.exp (-(Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1))) ^ (1 + δ) :=
    pow_le_pow_left₀ (by linarith) h1 _
  have h3 : Real.exp (-(Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1))) ^ (1 + δ)
      = 1 / ((δ : ℝ) + 1) := by
    rw [← Real.exp_nat_mul, show ((1 + δ : ℕ) : ℝ) * -(Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1))
        = -Real.log ((δ : ℝ) + 1) by push_cast; field_simp; ring,
      Real.exp_neg, Real.exp_log hδpos, one_div]
  have h5 : (1 - Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1)) ^ (1 + δ) ≤ 1 / ((δ : ℝ) + 1) := by
    rw [← h3]; exact h2
  have h6 : (Real.log ((δ : ℝ) + 1) + 1) / ((δ : ℝ) + 1)
      = Real.log ((δ : ℝ) + 1) / ((δ : ℝ) + 1) + 1 / ((δ : ℝ) + 1) :=
    add_div _ _ _
  rw [h6]
  linarith

end PMC
