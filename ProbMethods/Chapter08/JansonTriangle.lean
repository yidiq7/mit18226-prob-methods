import ProbMethods.Chapter08.Janson
import ProbMethods.Chapter04.TriangleThreshold

/-!
# §8.1 — Janson's upper bound for triangle-freeness

Zhao, *Probabilistic Methods in Combinatorics*, §8.1 applied to triangles (the estimate §8.3
and Theorem 8.1.6 rest on):

    P(G(n,p) triangle-free) ≤ exp (-C(n,3) p³ + 3n C(n,3) p⁵ / 2).

`PMC.janson` supplies `exp(-μ + Δ/2)` for an arbitrary family of "bad" edge sets; what this
file does is compute the two quantities for the family of `C(n,3)` potential triangles:

* `μ = ∑ P(triangle t present) = C(n,3) p³`, since each triangle spans three edges;
* `Δ = ∑_{t ≠ t' sharing an edge} P(both present) ≤ 3n C(n,3) p⁵`. Two distinct triples share
  an edge exactly when they share two vertices, in which case they span `6 - 1 = 5` edges
  (`PMC.card_spannedEdges_union`), and each triple has at most `3n` such partners
  (`PMC.card_partners_le`).

Together with `PMC.prob_not_hasTriangle_ge` — the Harris lower bound `(1-p³)^{C(n,3)}` — this
brackets the triangle-free probability from both sides, which is what Corollary 8.1.7's limit
`e^{-c³/6}` at `p = c/n` needs: both brackets tend to it, since `C(n,3)p³ → c³/6` and
`3n C(n,3) p⁵ → 0`.

The index type is `Fin (C(n,3))` rather than the triples themselves: `PMC.janson`'s upper half
needs a linear order on the index (it peels the largest index at each step), and transporting
one onto `Finset (Fin n)` would bring its own `DecidableEq` and break every `filter` in the
statement — the trap `Chapter10/Shearer.lean` documents. An explicit enumeration avoids it.
-/

open Finset

namespace PMC

section JansonTriangle

variable {n : ℕ}

/-- An enumeration of the `C(n,3)` vertex triples. -/
noncomputable def tripleEnum (n : ℕ) :
    Fin (n.choose 3) ≃ {t : Finset (Fin n) // t ∈ powersetCard 3 (univ : Finset (Fin n))} :=
  (Finset.equivFinOfCardEq (by rw [card_powersetCard, card_univ, Fintype.card_fin])).symm

/-- The edge set of the `i`-th potential triangle. -/
noncomputable def triangleBlock (n : ℕ) (i : Fin (n.choose 3)) : Finset (Sym2 (Fin n)) :=
  spannedEdges (tripleEnum n i).1

lemma card_triple (i : Fin (n.choose 3)) : #(tripleEnum n i).1 = 3 :=
  (Finset.mem_powersetCard.mp (tripleEnum n i).2).2

@[simp] lemma card_triangleBlock (i : Fin (n.choose 3)) : #(triangleBlock n i) = 3 := by
  rw [triangleBlock, card_spannedEdges, card_triple, show Nat.choose 3 2 = 3 from by decide]

/-- **The bad events of the triangle family are exactly the triangles.** -/
lemma noneOf_badEvent_triangleBlock (E : Finset (Sym2 (Fin n))) :
    E ∈ noneOf (badEvent (triangleBlock n)) (univ : Finset (Fin (n.choose 3)))
      ↔ ¬ HasTriangle E := by
  rw [mem_noneOf]
  constructor
  · intro h ⟨t, ht, hsub⟩
    have hthis := h ((tripleEnum n).symm ⟨t, ht⟩) (mem_univ _)
    rw [mem_badEvent, triangleBlock, Equiv.apply_symm_apply] at hthis
    exact hthis hsub
  · intro h i _
    rw [mem_badEvent]
    intro hsub
    exact h ⟨(tripleEnum n i).1, (tripleEnum n i).2, hsub⟩

/-- Two distinct triples whose triangles share an edge share exactly two vertices, so their
triangles span five edges between them. -/
lemma card_union_triangleBlock {i j : Fin (n.choose 3)} (hij : i ≠ j)
    (hshare : (triangleBlock n i ∩ triangleBlock n j).Nonempty) :
    #(triangleBlock n i ∪ triangleBlock n j) = 5 := by
  classical
  obtain ⟨x, hx⟩ := hshare
  rw [mem_inter, triangleBlock, triangleBlock, mem_spannedEdges, mem_spannedEdges] at hx
  obtain ⟨⟨a, ha, b, hb, hab, rfl⟩, ⟨c, hc, d, hd, hcd, heq⟩⟩ := hx
  set t := (tripleEnum n i).1 with ht
  set t' := (tripleEnum n j).1 with ht'
  -- the shared edge gives two shared vertices
  have hsub : {a, b} ⊆ t ∩ t' := by
    rw [Sym2.eq_iff] at heq
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hy with rfl | rfl <;>
      exact mem_inter.mpr (by constructor <;> assumption)
  have hcard2 : 2 ≤ #(t ∩ t') := by
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton] at this
    exact this
  -- distinct triples cannot share all three
  have hne : t ≠ t' := by
    intro h
    exact hij ((tripleEnum n).injective (Subtype.ext h))
  have hcard3 : #(t ∩ t') ≠ 3 := by
    intro h3
    have h1 : t ∩ t' = t :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h3, card_triple])
    have h2 : t ⊆ t' := by
      rw [← h1]
      exact Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le h2 (by rw [card_triple, card_triple]))
  have hle : #(t ∩ t') ≤ 3 := by
    have := Finset.card_le_card (Finset.inter_subset_left : t ∩ t' ⊆ t)
    rw [card_triple] at this
    exact this
  have h2eq : #(t ∩ t') = 2 := by omega
  have hunion := card_spannedEdges_union t t'
  rw [h2eq, card_triple, card_triple, show Nat.choose 3 2 = 3 from by decide,
    show Nat.choose 2 2 = 1 from by decide] at hunion
  rw [triangleBlock, triangleBlock, ← ht, ← ht']
  omega

/-- **Janson's upper bound for triangles.**

`P(G(n,p) triangle-free) ≤ exp (-C(n,3) p³ + 3n C(n,3) p⁵ / 2)`. -/
theorem probTriangleFree_le_exp (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    probTriangleFree n p
      ≤ Real.exp (-((n.choose 3 : ℝ) * p ^ 3)
          + 3 * (n : ℝ) * (n.choose 3 : ℝ) * p ^ 5 / 2) := by
  classical
  have hjan := (janson (α := Sym2 (Fin n)) (fun _ => p) (fun _ => hp0) (fun _ => hp1)
    (triangleBlock n)).2
  -- the event is triangle-freeness
  have hevent : wprob (pweight (fun _ : Sym2 (Fin n) => p))
      (noneOf (badEvent (triangleBlock n)) (univ : Finset (Fin (n.choose 3))))
      = probTriangleFree n p := by
    rw [wprob, probTriangleFree]
    refine Finset.sum_congr ?_ fun E _ => (bweight_eq_pweight p E).symm
    ext E
    rw [mem_filter]
    exact ⟨fun h => ⟨mem_univ _, (noneOf_badEvent_triangleBlock E).mp h⟩,
      fun h => (noneOf_badEvent_triangleBlock E).mpr h.2⟩
  -- each bad event has probability `p ^ 3`
  have hone : ∀ i : Fin (n.choose 3),
      wprob (pweight (fun _ : Sym2 (Fin n) => p)) (badEvent (triangleBlock n) i) = p ^ 3 := by
    intro i
    rw [wprob, badEvent]
    have h := sum_pweight_superset (fun _ : Sym2 (Fin n) => p) (triangleBlock n i)
    rw [Finset.powerset_univ] at h
    rw [h, Finset.prod_const, card_triangleBlock]
  have hmu : ∑ i : Fin (n.choose 3),
      wprob (pweight (fun _ : Sym2 (Fin n) => p)) (badEvent (triangleBlock n) i)
      = (n.choose 3 : ℝ) * p ^ 3 := by
    rw [Finset.sum_congr rfl fun i _ => hone i, Finset.sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  -- each dependent pair contributes `p ^ 5`, and there are at most `3n` per triangle
  have hpair : ∀ i j : Fin (n.choose 3), i ≠ j →
      (triangleBlock n i ∩ triangleBlock n j).Nonempty →
      wprob (pweight (fun _ : Sym2 (Fin n) => p))
        (badEvent (triangleBlock n) i ∩ badEvent (triangleBlock n) j) = p ^ 5 := by
    intro i j hij hshare
    have hinter : badEvent (triangleBlock n) i ∩ badEvent (triangleBlock n) j
        = (univ : Finset (Finset (Sym2 (Fin n)))).filter
          fun S => triangleBlock n i ∪ triangleBlock n j ⊆ S := by
      ext S
      rw [mem_inter, mem_badEvent, mem_badEvent, mem_filter, Finset.union_subset_iff]
      exact ⟨fun h => ⟨mem_univ _, h⟩, fun h => h.2⟩
    rw [wprob, hinter]
    have h := sum_pweight_superset (fun _ : Sym2 (Fin n) => p)
      (triangleBlock n i ∪ triangleBlock n j)
    rw [Finset.powerset_univ] at h
    rw [h, Finset.prod_const, card_union_triangleBlock hij hshare]
  have hdeg : ∀ i : Fin (n.choose 3),
      #((univ : Finset (Fin (n.choose 3))).filter
        fun j => j ≠ i ∧ (triangleBlock n i ∩ triangleBlock n j).Nonempty) ≤ 3 * n := by
    intro i
    have hpc := card_partners_le (V := Fin n) (tripleEnum n i).1
    rw [card_powersetCard, card_triple, Fintype.card_fin,
      show Nat.choose 3 2 = 3 from by decide] at hpc
    refine le_trans (Finset.card_le_card_of_injOn (fun j => (tripleEnum n j).1) ?_ ?_) hpc
    · intro j hj
      rw [mem_coe, mem_filter] at hj
      rw [mem_coe, mem_filter]
      refine ⟨(tripleEnum n j).2, ?_⟩
      -- sharing an edge means sharing two vertices
      obtain ⟨x, hx⟩ := hj.2.2
      rw [mem_inter, triangleBlock, triangleBlock, mem_spannedEdges, mem_spannedEdges] at hx
      obtain ⟨⟨a, ha, b, hb, hab, rfl⟩, ⟨c, hc, d, hd, hcd, heq⟩⟩ := hx
      have hsub : {a, b} ⊆ (tripleEnum n i).1 ∩ (tripleEnum n j).1 := by
        rw [Sym2.eq_iff] at heq
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hy with rfl | rfl <;>
          exact mem_inter.mpr (by constructor <;> assumption)
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton] at this
      exact this
    · intro j _ k _ h
      exact (tripleEnum n).injective (Subtype.ext h)
  have hdelta : (∑ i : Fin (n.choose 3), ∑ j ∈ (univ : Finset (Fin (n.choose 3))).filter
        (fun j => j ≠ i ∧ (triangleBlock n i ∩ triangleBlock n j).Nonempty),
        wprob (pweight (fun _ : Sym2 (Fin n) => p))
          (badEvent (triangleBlock n) i ∩ badEvent (triangleBlock n) j))
      ≤ 3 * (n : ℝ) * (n.choose 3 : ℝ) * p ^ 5 := by
    have hstep : ∀ i : Fin (n.choose 3),
        (∑ j ∈ (univ : Finset (Fin (n.choose 3))).filter
          (fun j => j ≠ i ∧ (triangleBlock n i ∩ triangleBlock n j).Nonempty),
          wprob (pweight (fun _ : Sym2 (Fin n) => p))
            (badEvent (triangleBlock n) i ∩ badEvent (triangleBlock n) j))
        ≤ 3 * (n : ℝ) * p ^ 5 := by
      intro i
      have hterm : ∀ j ∈ (univ : Finset (Fin (n.choose 3))).filter
          (fun j => j ≠ i ∧ (triangleBlock n i ∩ triangleBlock n j).Nonempty),
          wprob (pweight (fun _ : Sym2 (Fin n) => p))
            (badEvent (triangleBlock n) i ∩ badEvent (triangleBlock n) j) = p ^ 5 := by
        intro j hj
        rw [mem_filter] at hj
        exact hpair i j (Ne.symm hj.2.1) hj.2.2
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast hdeg i
    calc (∑ i : Fin (n.choose 3), ∑ j ∈ (univ : Finset (Fin (n.choose 3))).filter
          (fun j => j ≠ i ∧ (triangleBlock n i ∩ triangleBlock n j).Nonempty),
          wprob (pweight (fun _ : Sym2 (Fin n) => p))
            (badEvent (triangleBlock n) i ∩ badEvent (triangleBlock n) j))
        ≤ ∑ _i : Fin (n.choose 3), 3 * (n : ℝ) * p ^ 5 := Finset.sum_le_sum fun i _ => hstep i
      _ = 3 * (n : ℝ) * (n.choose 3 : ℝ) * p ^ 5 := by
          rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [hevent, hmu] at hjan
  refine le_trans hjan (Real.exp_le_exp.mpr ?_)
  linarith [hdelta]


/-- **The lower bracket for `1 - u`**: `exp(-u/(1-u)) ≤ 1 - u` for `0 ≤ u < 1`.

`Real.add_one_le_exp` at `u/(1-u)` says `1/(1-u) ≤ exp(u/(1-u))`; multiplying by
`exp(-u/(1-u))` gives this. Together with `1 - u ≤ exp(-u)` it brackets `1 - u` between two
exponentials, which is what makes §8.1's limits elementary — no logarithm expansion, hence no
error term to control. -/
lemma exp_neg_div_one_sub_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Real.exp (-(u / (1 - u))) ≤ 1 - u := by
  have h1u : 0 < 1 - u := by linarith
  have h1u' : (1 : ℝ) - u ≠ 0 := ne_of_gt h1u
  have hv : 1 + u / (1 - u) = 1 / (1 - u) := by
    field_simp
    ring
  have hexp : 1 / (1 - u) ≤ Real.exp (u / (1 - u)) := by
    have hle := Real.add_one_le_exp (u / (1 - u))
    rw [add_comm, hv] at hle
    exact hle
  have hmul : Real.exp (-(u / (1 - u))) * (1 / (1 - u))
      ≤ Real.exp (-(u / (1 - u))) * Real.exp (u / (1 - u)) :=
    mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
  rwa [mul_one_div, div_le_one h1u] at hmul

/-! ### Corollary 8.1.7: the limit at `p = c/n`

Both brackets tend to `e^{-c³/6}`, so the triangle-free probability does. -/

/-- `C(n,3) (c/n)³ → c³/6`. -/
private lemma tendsto_mu (c : ℝ) :
    Filter.Tendsto (fun n : ℕ => (n.choose 3 : ℝ) * (c / n) ^ 3) Filter.atTop
      (nhds (c ^ 3 / 6)) := by
  have hfrac : Filter.Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)) * (1 - 2 / (n : ℝ)))
      Filter.atTop (nhds 1) := by
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have h2 : Filter.Tendsto (fun n : ℕ => 2 / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 2
    have ha : Filter.Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) Filter.atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    have hb : Filter.Tendsto (fun n : ℕ => 1 - 2 / (n : ℝ)) Filter.atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h2
    simpa using ha.mul hb
  have hlim : Filter.Tendsto
      (fun n : ℕ => c ^ 3 / 6 * ((1 - 1 / (n : ℝ)) * (1 - 2 / (n : ℝ)))) Filter.atTop
      (nhds (c ^ 3 / 6)) := by
    simpa using (tendsto_const_nhds (x := c ^ 3 / 6)).mul hfrac
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcast := choose_three_cast (n := n) hn
  field_simp
  linear_combination -c ^ 3 * hcast

/-- **Corollary 8.1.7.** `P(G(n, c/n) triangle-free) → e^{-c³/6}`.

The Harris lower bound `(1-p³)^{C(n,3)}` and the Janson upper bound
`exp(-C(n,3)p³ + 3n C(n,3)p⁵/2)` both tend to `e^{-c³/6}` at `p = c/n`: the first because
`exp(-C(n,3)p³/(1-p³)) ≤ (1-p³)^{C(n,3)}` and `C(n,3)p³ → c³/6`, the second because in
addition `3n C(n,3)p⁵ = 3c⁵ · C(n,3)/n⁴ → 0`.

`1 - u ≤ exp(-u)` and `exp(-u/(1-u)) ≤ 1 - u` are both `Real.add_one_le_exp`, the second at
`u/(1-u)`; no logarithms and no series are needed. -/
theorem tendsto_probTriangleFree_exp {c : ℝ} (hc0 : 0 ≤ c) :
    Filter.Tendsto (fun n : ℕ => probTriangleFree n (c / n)) Filter.atTop
      (nhds (Real.exp (-(c ^ 3) / 6))) := by
  have hmu := tendsto_mu c
  -- the upper bracket
  have hupper : Filter.Tendsto (fun n : ℕ => Real.exp (-((n.choose 3 : ℝ) * (c / n) ^ 3)
      + 3 * (n : ℝ) * (n.choose 3 : ℝ) * (c / n) ^ 5 / 2)) Filter.atTop
      (nhds (Real.exp (-(c ^ 3) / 6))) := by
    refine (Real.continuous_exp.tendsto _).comp ?_
    have hdelta : Filter.Tendsto
        (fun n : ℕ => 3 * (n : ℝ) * (n.choose 3 : ℝ) * (c / n) ^ 5 / 2) Filter.atTop
        (nhds 0) := by
      have hmul : Filter.Tendsto (fun n : ℕ => ((n.choose 3 : ℝ) * (c / n) ^ 3)
          * (3 * c ^ 2 / 2 * (1 / (n : ℝ)))) Filter.atTop (nhds 0) := by
        have h0 : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (nhds 0) :=
          tendsto_const_div_atTop_nhds_zero_nat 1
        have := hmu.mul ((tendsto_const_nhds (x := 3 * c ^ 2 / 2)).mul h0)
        simpa using this
      refine hmul.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      field_simp
    have := (hmu.neg).add hdelta
    simpa [neg_div] using this
  -- the lower bracket
  have hlower : Filter.Tendsto (fun n : ℕ =>
      Real.exp (-((n.choose 3 : ℝ) * (c / n) ^ 3 * (1 - (c / n) ^ 3)⁻¹))) Filter.atTop
      (nhds (Real.exp (-(c ^ 3) / 6))) := by
    refine (Real.continuous_exp.tendsto _).comp ?_
    have hden : Filter.Tendsto (fun n : ℕ => 1 - (c / n) ^ 3) Filter.atTop (nhds 1) := by
      have hc : Filter.Tendsto (fun n : ℕ => (c / n) ^ 3) Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun n : ℕ => c / (n : ℝ)) Filter.atTop (nhds 0) :=
          tendsto_const_div_atTop_nhds_zero_nat c
        have := h1.pow 3
        simpa using this
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hc
    have hinv : Filter.Tendsto (fun n : ℕ => (1 - (c / n) ^ 3)⁻¹) Filter.atTop (nhds 1) := by
      simpa using hden.inv₀ one_ne_zero
    have hquot : Filter.Tendsto (fun n : ℕ => (n.choose 3 : ℝ) * (c / n) ^ 3
        * (1 - (c / n) ^ 3)⁻¹) Filter.atTop (nhds (c ^ 3 / 6)) := by
      simpa using hmu.mul hinv
    have := hquot.neg
    simpa [neg_div] using this
  -- squeeze
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1,
      (tendsto_const_div_atTop_nhds_zero_nat c).eventually_lt_const
        (show (0:ℝ) < 1 by norm_num)] with n hn hp1
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hp0 : 0 ≤ c / n := div_nonneg hc0 (le_of_lt hnpos)
    have hu0 : 0 ≤ (c / (n : ℝ)) ^ 3 := by positivity
    have hu1 : (c / (n : ℝ)) ^ 3 < 1 := by
      calc (c / (n : ℝ)) ^ 3 ≤ (c / (n : ℝ)) ^ 1 := by
            refine pow_le_pow_of_le_one hp0 (le_of_lt hp1) (by norm_num)
        _ = c / (n : ℝ) := pow_one _
        _ < 1 := hp1
    -- `exp(-u/(1-u)) ≤ (1-u)^k ≤ P`
    have hstep : Real.exp (-((c / (n : ℝ)) ^ 3 / (1 - (c / (n : ℝ)) ^ 3)))
        ≤ 1 - (c / (n : ℝ)) ^ 3 := exp_neg_div_one_sub_le hu0 hu1
    have hpow : Real.exp (-((n.choose 3 : ℝ) * (c / (n : ℝ)) ^ 3 * (1 - (c / (n : ℝ)) ^ 3)⁻¹))
        ≤ (1 - (c / (n : ℝ)) ^ 3) ^ (n.choose 3) := by
      have hbase : Real.exp (-((c / (n : ℝ)) ^ 3 / (1 - (c / (n : ℝ)) ^ 3))) ^ (n.choose 3)
          ≤ (1 - (c / (n : ℝ)) ^ 3) ^ (n.choose 3) :=
        pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hstep _
      calc Real.exp (-((n.choose 3 : ℝ) * (c / (n : ℝ)) ^ 3 * (1 - (c / (n : ℝ)) ^ 3)⁻¹))
          = Real.exp (-((c / (n : ℝ)) ^ 3 / (1 - (c / (n : ℝ)) ^ 3))) ^ (n.choose 3) := by
            rw [← Real.exp_nat_mul]
            congr 1
            field_simp
        _ ≤ _ := hbase
    refine le_trans hpow ?_
    have hharris := prob_not_hasTriangle_ge (V := Fin n) (c / n) hp0 (le_of_lt hp1)
    rw [Fintype.card_fin] at hharris
    exact hharris
  · filter_upwards [Filter.eventually_ge_atTop 1,
      (tendsto_const_div_atTop_nhds_zero_nat c).eventually_lt_const
        (show (0:ℝ) < 1 by norm_num)] with n hn hp1
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hp0 : 0 ≤ c / n := div_nonneg hc0 (le_of_lt hnpos)
    exact probTriangleFree_le_exp n hp0 (le_of_lt hp1)


/-! ### Theorem 8.1.6: the exponent is `-(1 + o(1))μ` -/

/-- **Theorem 8.1.6.** If `p = o(n^{-1/2})` then

    log P(G(n,p) triangle-free) / μ → -1,   where μ = C(n,3)p³,

which is the notes' `P = e^{-(1+o(1))μ}`.

Both brackets divided by `μ` tend to `-1`: the Janson side gives
`log P/μ ≤ -1 + Δ/(2μ) = -1 + 3np²/2`, and `np² → 0` is *exactly* the hypothesis
`p = o(n^{-1/2})`; the Harris side gives `log P/μ ≥ -1/(1-p³)`. So the hypothesis is not an
artifact — it is the condition under which `Δ` is negligible against `μ`, which is what
Janson's inequality needs to be sharp. -/
theorem tendsto_log_probTriangleFree_div {p : ℕ → ℝ} (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n ≤ 1)
    (hhalf : Filter.Tendsto (fun n : ℕ => (n : ℝ) * p n ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ => Real.log (probTriangleFree n (p n)) / ((n.choose 3 : ℝ) * p n ^ 3))
      Filter.atTop (nhds (-1)) := by
  -- `p n → 0` fast enough that `p n ^ 3 → 0`
  have hsq : Filter.Tendsto (fun n : ℕ => p n ^ 2) Filter.atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) ?_ hhalf
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [sq_nonneg (p n)]
  have hcube : Filter.Tendsto (fun n : ℕ => p n ^ 3) Filter.atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => pow_nonneg (hp0 n).le 3)
      (Filter.Eventually.of_forall fun n => ?_) hsq
    exact pow_le_pow_of_le_one (hp0 n).le (hp1 n) (by norm_num)
  have hplt : ∀ᶠ n : ℕ in Filter.atTop, p n ^ 3 < 1 :=
    hcube.eventually_lt_const (show (0:ℝ) < 1 by norm_num)
  -- the two brackets
  have hupper : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (probTriangleFree n (p n)) / ((n.choose 3 : ℝ) * p n ^ 3)
        ≤ -1 + 3 * (n : ℝ) * p n ^ 2 / 2 := by
    filter_upwards [Filter.eventually_ge_atTop 3, hplt] with n hn3 hp3
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hcpos : (0 : ℝ) < (n.choose 3 : ℝ) := by
      have : 0 < n.choose 3 := Nat.choose_pos hn3
      exact_mod_cast this
    have hmu : (0 : ℝ) < (n.choose 3 : ℝ) * p n ^ 3 := mul_pos hcpos (pow_pos (hp0 n) 3)
    have hu0 : 0 ≤ p n ^ 3 := pow_nonneg (hp0 n).le 3
    have hharris : (1 - p n ^ 3) ^ (n.choose 3) ≤ probTriangleFree n (p n) := by
      have h := prob_not_hasTriangle_ge (V := Fin n) (p n) (le_of_lt (hp0 n)) (hp1 n)
      rw [Fintype.card_fin] at h
      exact h
    have hpos : 0 < probTriangleFree n (p n) :=
      lt_of_lt_of_le (pow_pos (by linarith) _) hharris
    have hle := probTriangleFree_le_exp n (le_of_lt (hp0 n)) (hp1 n)
    have hlog : Real.log (probTriangleFree n (p n))
        ≤ -((n.choose 3 : ℝ) * p n ^ 3) + 3 * (n : ℝ) * (n.choose 3 : ℝ) * p n ^ 5 / 2 := by
      have := Real.log_le_log hpos hle
      rwa [Real.log_exp] at this
    rw [div_le_iff₀ hmu]
    calc Real.log (probTriangleFree n (p n))
        ≤ -((n.choose 3 : ℝ) * p n ^ 3) + 3 * (n : ℝ) * (n.choose 3 : ℝ) * p n ^ 5 / 2 := hlog
      _ = (-1 + 3 * (n : ℝ) * p n ^ 2 / 2) * ((n.choose 3 : ℝ) * p n ^ 3) := by ring
  have hlower : ∀ᶠ n : ℕ in Filter.atTop,
      -1 / (1 - p n ^ 3) ≤ Real.log (probTriangleFree n (p n)) / ((n.choose 3 : ℝ) * p n ^ 3) := by
    filter_upwards [Filter.eventually_ge_atTop 3, hplt] with n hn3 hp3
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hcpos : (0 : ℝ) < (n.choose 3 : ℝ) := by
      have : 0 < n.choose 3 := Nat.choose_pos hn3
      exact_mod_cast this
    have hmu : (0 : ℝ) < (n.choose 3 : ℝ) * p n ^ 3 := mul_pos hcpos (pow_pos (hp0 n) 3)
    have hu0 : 0 ≤ p n ^ 3 := pow_nonneg (hp0 n).le 3
    have h1u : (0 : ℝ) < 1 - p n ^ 3 := by linarith
    -- `exp(-u/(1-u)) ≤ 1 - u`, raised to the `C(n,3)`
    have hstep := exp_neg_div_one_sub_le hu0 hp3
    have hpow : Real.exp (-((n.choose 3 : ℝ) * p n ^ 3 / (1 - p n ^ 3)))
        ≤ (1 - p n ^ 3) ^ (n.choose 3) := by
      calc Real.exp (-((n.choose 3 : ℝ) * p n ^ 3 / (1 - p n ^ 3)))
          = Real.exp (-(p n ^ 3 / (1 - p n ^ 3))) ^ (n.choose 3) := by
            rw [← Real.exp_nat_mul]
            congr 1
            field_simp
        _ ≤ (1 - p n ^ 3) ^ (n.choose 3) :=
            pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hstep _
    have hharris : (1 - p n ^ 3) ^ (n.choose 3) ≤ probTriangleFree n (p n) := by
      have h := prob_not_hasTriangle_ge (V := Fin n) (p n) (le_of_lt (hp0 n)) (hp1 n)
      rw [Fintype.card_fin] at h
      exact h
    have hlog : -((n.choose 3 : ℝ) * p n ^ 3 / (1 - p n ^ 3))
        ≤ Real.log (probTriangleFree n (p n)) := by
      rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (pow_pos h1u _) hharris)]
      exact le_trans hpow hharris
    rw [le_div_iff₀ hmu]
    calc -1 / (1 - p n ^ 3) * ((n.choose 3 : ℝ) * p n ^ 3)
        = -((n.choose 3 : ℝ) * p n ^ 3 / (1 - p n ^ 3)) := by
          field_simp
      _ ≤ Real.log (probTriangleFree n (p n)) := hlog
  -- both brackets tend to `-1`
  have hupperlim : Filter.Tendsto (fun n : ℕ => -1 + 3 * (n : ℝ) * p n ^ 2 / 2)
      Filter.atTop (nhds (-1)) := by
    have : Filter.Tendsto (fun n : ℕ => 3 * ((n : ℝ) * p n ^ 2) / 2) Filter.atTop (nhds 0) := by
      have := (hhalf.const_mul (3 : ℝ)).div_const 2
      simpa using this
    have h2 := (tendsto_const_nhds (x := (-1 : ℝ))).add this
    rw [add_zero] at h2
    refine h2.congr fun n => ?_
    ring
  have hlowerlim : Filter.Tendsto (fun n : ℕ => -1 / (1 - p n ^ 3)) Filter.atTop (nhds (-1)) := by
    have hden : Filter.Tendsto (fun n : ℕ => 1 - p n ^ 3) Filter.atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hcube
    have hinv : Filter.Tendsto (fun n : ℕ => (1 - p n ^ 3)⁻¹) Filter.atTop (nhds 1) := by
      simpa using hden.inv₀ one_ne_zero
    have := hinv.const_mul (-1 : ℝ)
    simpa [div_eq_mul_inv] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerlim hupperlim hlower hupper

end JansonTriangle

end PMC
