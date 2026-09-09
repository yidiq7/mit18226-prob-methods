import ProbMethods.Chapter04.SecondMoment

/-!
# §4.1 — The variance of the triangle count

Zhao, *Probabilistic Methods in Combinatorics*, §4.1.

The overlap analysis that turns `PMC.sum_bweight_triangleFree_le` into an explicit
threshold. Two triples span `3`, `5` or `6` edges between them according as they share
`3`, `2` or at most `1` vertex (`PMC.card_spannedEdges_union`), and only the first two
cases contribute to the variance — the `6`-edge pairs cancel exactly against `E[X]²`.
-/

open Finset

namespace PMC

/-- For a fixed triple `t`, at most `3 * n` triples meet it in two or more vertices: such a
`t'` is `insert v u` for a `2`-subset `u ⊆ t` and some vertex `v`.

Public because §8.1's Janson bound for triangles counts the same partners: two triangles are
dependent exactly when they share an edge, i.e. two vertices. -/
lemma card_partners_le {V : Type*} [Fintype V] [DecidableEq V] (t : Finset V) :
    #((powersetCard 3 (univ : Finset V)).filter fun t' => 2 ≤ #(t ∩ t'))
      ≤ #(powersetCard 2 t) * Fintype.card V := by
  classical
  have hsub : ((powersetCard 3 (univ : Finset V)).filter fun t' => 2 ≤ #(t ∩ t'))
      ⊆ ((powersetCard 2 t) ×ˢ (univ : Finset V)).image (fun q => insert q.2 q.1) := by
    intro t' ht'
    rw [mem_filter, mem_powersetCard] at ht'
    obtain ⟨⟨-, ht'card⟩, hmeet⟩ := ht'
    obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq hmeet
    have huT : u ⊆ t := hu.trans inter_subset_left
    have huT' : u ⊆ t' := hu.trans inter_subset_right
    have hlt : #u < #t' := by omega
    obtain ⟨v, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine mem_image.mpr ⟨(u, v), ?_, ?_⟩
    · rw [mem_product, mem_powersetCard]
      exact ⟨⟨huT, hucard⟩, mem_univ v⟩
    · have hins : insert v u ⊆ t' := insert_subset hv.1 huT'
      have hcard : #(insert v u) = 3 := by
        rw [card_insert_of_notMem hv.2, hucard]
      have heq : insert v u = t' :=
        Finset.eq_of_subset_of_card_le hins (by rw [hcard, ht'card])
      exact heq
  calc #((powersetCard 3 (univ : Finset V)).filter fun t' => 2 ≤ #(t ∩ t'))
      ≤ #(((powersetCard 2 t) ×ˢ (univ : Finset V)).image (fun q => insert q.2 q.1)) :=
        card_le_card hsub
    _ ≤ #((powersetCard 2 t) ×ˢ (univ : Finset V)) := card_image_le
    _ = #(powersetCard 2 t) * Fintype.card V := by rw [card_product, card_univ]

/-- Two triples span `6` edges between them unless they share two or more vertices, in
which case they span at least `3`. -/
private lemma card_union_cases {V : Type*} [DecidableEq V] {t t' : Finset V}
    (ht : #t = 3) (ht' : #t' = 3) :
    #(spannedEdges t ∪ spannedEdges t') + (#(t ∩ t')).choose 2 = 6
      ∧ 3 ≤ #(spannedEdges t ∪ spannedEdges t') := by
  refine ⟨?_, ?_⟩
  · have h := card_spannedEdges_union t t'
    rw [ht, ht'] at h
    simpa using h
  · have h : spannedEdges t ⊆ spannedEdges t ∪ spannedEdges t' := subset_union_left
    have := card_le_card h
    rw [card_spannedEdges, ht] at this
    simpa using this

/-- **The variance of the triangle count** (Zhao, §4.1).

`Var ≤ 3 n C(n,3) p ^ 3`.

Pairs of triples sharing at most one vertex span exactly `6` edges, so their contribution
cancels against `E[X]²` term by term — this is why only overlapping pairs matter. Pairs
sharing two or more span `3` or `5` edges, hence contribute at most `p ^ 3` each, and there
are at most `C(n,3) * 3n` of them (`PMC.card_partners_le`).

The ratio to `(E X) ^ 2 = (C(n,3) p ^ 3) ^ 2` is `3n / (C(n,3) p ^ 3)`, which is small
exactly when `n p → ∞` — so the crude `3n` over-count loses nothing that matters, and
feeding this into `PMC.sum_bweight_triangleFree_le` gives the threshold. -/
theorem wvar_card_triangles_le {V : Type*} [Fintype V] [DecidableEq V] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    wvar (bweight p) (fun E : Finset (Sym2 V) => (#(triangles E) : ℝ))
      ≤ 3 * Fintype.card V * ((Fintype.card V).choose 3) * p ^ 3 := by
  classical
  set n : ℕ := Fintype.card V with hn
  set P3 : Finset (Finset V) := powersetCard 3 (univ : Finset V) with hP3
  have hwsum : ∑ E : Finset (Sym2 V), bweight p E = 1 := by
    have h := sum_bweight (α := Sym2 V) p
    rwa [Finset.powerset_univ] at h
  -- second moment, as a sum over pairs
  have hsq : wmean (bweight p) (fun E : Finset (Sym2 V) => (#(triangles E) : ℝ) ^ 2)
      = ∑ t ∈ P3, ∑ t' ∈ P3, p ^ #(spannedEdges t ∪ spannedEdges t') := by
    rw [wmean_eq_sum_powerset]
    exact sum_bweight_mul_card_filter_sq (α := Sym2 V) p P3 spannedEdges
  have hmean : wmean (bweight p) (fun E : Finset (Sym2 V) => (#(triangles E) : ℝ))
      = (n.choose 3) * p ^ 3 := wmean_card_triangles p
  -- `E[X]²` as the same sum with every term `p ^ 6`
  have hconst : ∑ t ∈ P3, ∑ _t' ∈ P3, p ^ 6 = ((n.choose 3 : ℝ) * p ^ 3) ^ 2 := by
    have hcard : #P3 = n.choose 3 := by
      rw [hP3, card_powersetCard, card_univ]
    rw [Finset.sum_const, Finset.sum_const, hcard, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [wvar_eq_wmean_sq_sub _ _ hwsum, hsq, hmean, ← hconst, ← Finset.sum_sub_distrib]
  -- bound the surviving terms
  have hstep : ∀ t ∈ P3,
      (∑ t' ∈ P3, p ^ #(spannedEdges t ∪ spannedEdges t')) - ∑ _t' ∈ P3, p ^ 6
        ≤ 3 * (n : ℝ) * p ^ 3 := by
    intro t ht
    rw [hP3, mem_powersetCard] at ht
    rw [← Finset.sum_sub_distrib]
    have hsplit := Finset.sum_filter_add_sum_filter_not P3
      (fun t' => 2 ≤ #(t ∩ t'))
      (fun t' => p ^ #(spannedEdges t ∪ spannedEdges t') - p ^ 6)
    have hzero : ∑ t' ∈ P3.filter (fun t' => ¬ 2 ≤ #(t ∩ t')),
        (p ^ #(spannedEdges t ∪ spannedEdges t') - p ^ 6) = 0 := by
      refine Finset.sum_eq_zero fun t' ht' => ?_
      rw [mem_filter, hP3, mem_powersetCard] at ht'
      have hj : #(t ∩ t') ≤ 1 := by omega
      have hch : (#(t ∩ t')).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have := (card_union_cases ht.2 ht'.1.2).1
      rw [hch] at this
      rw [show #(spannedEdges t ∪ spannedEdges t') = 6 by omega]
      ring
    have hbound : ∑ t' ∈ P3.filter (fun t' => 2 ≤ #(t ∩ t')),
        (p ^ #(spannedEdges t ∪ spannedEdges t') - p ^ 6) ≤ 3 * (n : ℝ) * p ^ 3 := by
      have hterm : ∀ t' ∈ P3.filter (fun t' => 2 ≤ #(t ∩ t')),
          p ^ #(spannedEdges t ∪ spannedEdges t') - p ^ 6 ≤ p ^ 3 := by
        intro t' ht'
        rw [mem_filter, hP3, mem_powersetCard] at ht'
        have h3 := (card_union_cases ht.2 ht'.1.2).2
        have : p ^ #(spannedEdges t ∪ spannedEdges t') ≤ p ^ 3 :=
          pow_le_pow_of_le_one hp0 hp1 h3
        have hp6 : 0 ≤ p ^ 6 := by positivity
        linarith
      calc ∑ t' ∈ P3.filter (fun t' => 2 ≤ #(t ∩ t')),
            (p ^ #(spannedEdges t ∪ spannedEdges t') - p ^ 6)
          ≤ ∑ _t' ∈ P3.filter (fun t' => 2 ≤ #(t ∩ t')), p ^ 3 :=
            Finset.sum_le_sum hterm
        _ = (#(P3.filter fun t' => 2 ≤ #(t ∩ t')) : ℝ) * p ^ 3 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 3 * (n : ℝ) * p ^ 3 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hpc := card_partners_le (V := V) t
            rw [card_powersetCard, ht.2, ← hn] at hpc
            have h32 : Nat.choose 3 2 = 3 := by decide
            rw [h32] at hpc
            rw [← hP3] at hpc
            exact_mod_cast hpc
    linarith [hsplit, hzero, hbound]
  calc ∑ t ∈ P3, ((∑ t' ∈ P3, p ^ #(spannedEdges t ∪ spannedEdges t'))
        - ∑ _t' ∈ P3, p ^ 6)
      ≤ ∑ _t ∈ P3, 3 * (n : ℝ) * p ^ 3 := Finset.sum_le_sum hstep
    _ = 3 * (n : ℝ) * ((n.choose 3 : ℝ)) * p ^ 3 := by
        rw [Finset.sum_const, hP3, card_powersetCard, card_univ, nsmul_eq_mul]
        push_cast
        ring


/-- **The variance of the triangle count, sharpened** (Zhao, §4.1):

`Var ≤ C(n,3) (p³ + 3n p⁵)`.

`PMC.wvar_card_triangles_le` bounds every overlapping pair's contribution by `p³`, which is
enough for the qualitative statement but loses the threshold: it gives
`P(triangle-free) ≲ 1/(n²p³)`, and that tends to `0` only when `n²p³ → ∞`, whereas the
threshold is at `np → ∞`. Keeping the two overlap classes apart fixes this:

* `t' = t` contributes `p³`, and there is one such term;
* `#(t ∩ t') = 2` contributes `p⁵`, and there are at most `3n` such `t'`.

The resulting bound gives `P(triangle-free) ≲ 1/(np)³ + 1/(n²p)`, which is what
`PMC.tendsto_probTriangleFree_zero` needs. -/
theorem wvar_card_triangles_le' {V : Type*} [Fintype V] [DecidableEq V] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    wvar (bweight p) (fun E : Finset (Sym2 V) => (#(triangles E) : ℝ))
      ≤ ((Fintype.card V).choose 3 : ℝ)
          * (p ^ 3 + 3 * (Fintype.card V : ℝ) * p ^ 5) := by
  classical
  set n : ℕ := Fintype.card V with hn
  set P3 : Finset (Finset V) := powersetCard 3 (univ : Finset V) with hP3
  have hwsum : ∑ E : Finset (Sym2 V), bweight p E = 1 := by
    have h := sum_bweight (α := Sym2 V) p
    rwa [Finset.powerset_univ] at h
  have hsq : wmean (bweight p) (fun E : Finset (Sym2 V) => (#(triangles E) : ℝ) ^ 2)
      = ∑ t ∈ P3, ∑ t' ∈ P3, p ^ #(spannedEdges t ∪ spannedEdges t') := by
    rw [wmean_eq_sum_powerset]
    exact sum_bweight_mul_card_filter_sq (α := Sym2 V) p P3 spannedEdges
  have hmean : wmean (bweight p) (fun E : Finset (Sym2 V) => (#(triangles E) : ℝ))
      = (n.choose 3) * p ^ 3 := wmean_card_triangles p
  have hconst : ∑ t ∈ P3, ∑ _t' ∈ P3, p ^ 6 = ((n.choose 3 : ℝ) * p ^ 3) ^ 2 := by
    have hcard : #P3 = n.choose 3 := by
      rw [hP3, card_powersetCard, card_univ]
    rw [Finset.sum_const, Finset.sum_const, hcard, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [wvar_eq_wmean_sq_sub _ _ hwsum, hsq, hmean, ← hconst, ← Finset.sum_sub_distrib]
  have hstep : ∀ t ∈ P3,
      (∑ t' ∈ P3, p ^ #(spannedEdges t ∪ spannedEdges t')) - ∑ _t' ∈ P3, p ^ 6
        ≤ p ^ 3 + 3 * (n : ℝ) * p ^ 5 := by
    intro t ht
    rw [hP3, mem_powersetCard] at ht
    rw [← Finset.sum_sub_distrib]
    have hsplit := Finset.sum_filter_add_sum_filter_not P3
      (fun t' => 2 ≤ #(t ∩ t'))
      (fun t' => p ^ #(spannedEdges t ∪ spannedEdges t') - p ^ 6)
    have hzero : ∑ t' ∈ P3.filter (fun t' => ¬ 2 ≤ #(t ∩ t')),
        (p ^ #(spannedEdges t ∪ spannedEdges t') - p ^ 6) = 0 := by
      refine Finset.sum_eq_zero fun t' ht' => ?_
      rw [mem_filter, hP3, mem_powersetCard] at ht'
      have hch : (#(t ∩ t')).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have := (card_union_cases ht.2 ht'.1.2).1
      rw [hch] at this
      rw [show #(spannedEdges t ∪ spannedEdges t') = 6 by omega]
      ring
    have htF : t ∈ P3.filter (fun t' => 2 ≤ #(t ∩ t')) := by
      refine mem_filter.mpr ⟨?_, ?_⟩
      · rw [hP3, mem_powersetCard]
        exact ⟨subset_univ _, ht.2⟩
      · rw [Finset.inter_self, ht.2]
        omega
    have hbound : ∑ t' ∈ P3.filter (fun t' => 2 ≤ #(t ∩ t')),
        (p ^ #(spannedEdges t ∪ spannedEdges t') - p ^ 6) ≤ p ^ 3 + 3 * (n : ℝ) * p ^ 5 := by
      rw [← Finset.add_sum_erase _ _ htF]
      have hp6 : (0 : ℝ) ≤ p ^ 6 := by positivity
      have hself : p ^ #(spannedEdges t ∪ spannedEdges t) - p ^ 6 ≤ p ^ 3 := by
        rw [Finset.union_self, card_spannedEdges, ht.2, show Nat.choose 3 2 = 3 from by decide]
        linarith
      have herase : ∑ t' ∈ (P3.filter (fun t' => 2 ≤ #(t ∩ t'))).erase t,
          (p ^ #(spannedEdges t ∪ spannedEdges t') - p ^ 6) ≤ 3 * (n : ℝ) * p ^ 5 := by
        have hterm : ∀ t' ∈ (P3.filter (fun t' => 2 ≤ #(t ∩ t'))).erase t,
            p ^ #(spannedEdges t ∪ spannedEdges t') - p ^ 6 ≤ p ^ 5 := by
          intro t' ht'
          rw [Finset.mem_erase, mem_filter, hP3, mem_powersetCard] at ht'
          obtain ⟨hne, ⟨-, hcard'⟩, h2⟩ := ht'
          have hle3 : #(t ∩ t') ≤ 3 := by
            have := card_le_card (Finset.inter_subset_left : t ∩ t' ⊆ t)
            omega
          have hnot3 : #(t ∩ t') ≠ 3 := by
            intro h3
            have h1 : t ∩ t' = t :=
              Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
            have h2' : t ⊆ t' := by
              rw [← h1]
              exact Finset.inter_subset_right
            exact hne (Finset.eq_of_subset_of_card_le h2' (by omega)).symm
          have h2eq : #(t ∩ t') = 2 := by omega
          have hu := (card_union_cases ht.2 hcard').1
          rw [h2eq, show Nat.choose 2 2 = 1 from by decide] at hu
          rw [show #(spannedEdges t ∪ spannedEdges t') = 5 by omega]
          linarith
        calc ∑ t' ∈ (P3.filter (fun t' => 2 ≤ #(t ∩ t'))).erase t,
              (p ^ #(spannedEdges t ∪ spannedEdges t') - p ^ 6)
            ≤ ∑ _t' ∈ (P3.filter (fun t' => 2 ≤ #(t ∩ t'))).erase t, p ^ 5 :=
              Finset.sum_le_sum hterm
          _ = (#((P3.filter fun t' => 2 ≤ #(t ∩ t')).erase t) : ℝ) * p ^ 5 := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 3 * (n : ℝ) * p ^ 5 := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              have hcard_le : #((P3.filter fun t' => 2 ≤ #(t ∩ t')).erase t)
                  ≤ #(P3.filter fun t' => 2 ≤ #(t ∩ t')) := Finset.card_erase_le
              have hpc := card_partners_le (V := V) t
              rw [card_powersetCard, ht.2, ← hn, show Nat.choose 3 2 = 3 from by decide,
                ← hP3] at hpc
              have : #((P3.filter fun t' => 2 ≤ #(t ∩ t')).erase t) ≤ 3 * n :=
                le_trans hcard_le hpc
              exact_mod_cast this
      linarith
    linarith [hsplit, hzero, hbound]
  calc ∑ t ∈ P3, ((∑ t' ∈ P3, p ^ #(spannedEdges t ∪ spannedEdges t'))
        - ∑ _t' ∈ P3, p ^ 6)
      ≤ ∑ _t ∈ P3, (p ^ 3 + 3 * (n : ℝ) * p ^ 5) := Finset.sum_le_sum hstep
    _ = ((n.choose 3 : ℝ)) * (p ^ 3 + 3 * (n : ℝ) * p ^ 5) := by
        rw [Finset.sum_const, hP3, card_powersetCard, card_univ, nsmul_eq_mul]


end PMC
