import ProbMethods.Basic

/-!
# §1.3 — 2-colourable hypergraphs

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 1.3.1.
-/

open Finset

namespace PMC

variable {V : Type*}

section Counting
variable [DecidableEq V]

/-- At most `2 ^ (#X - #e)` of the subsets of `X` contain `e`. -/
private lemma card_filter_superset_le (X e : Finset V) (he : e ⊆ X) :
    #{T ∈ X.powerset | e ⊆ T} ≤ 2 ^ (#X - #e) := by
  have hc : #((X \ e).powerset) = 2 ^ (#X - #e) := by
    rw [card_powerset, card_sdiff_of_subset he]
  rw [← hc]
  refine card_le_card_of_injOn (fun T => T \ e) ?_ ?_
  · intro T hT
    rw [mem_coe, mem_filter, mem_powerset] at hT
    rw [mem_coe, mem_powerset]
    intro x hx
    rw [mem_sdiff] at hx ⊢
    exact ⟨hT.1 hx.1, hx.2⟩
  · intro T₁ h₁ T₂ h₂ heq
    rw [mem_coe, mem_filter] at h₁ h₂
    simp only at heq
    rw [← sdiff_union_of_subset h₁.2, ← sdiff_union_of_subset h₂.2, heq]

/-- At most `2 ^ (#X - #e)` of the subsets of `X` are disjoint from `e`. -/
private lemma card_filter_disjoint_le (X e : Finset V) (he : e ⊆ X) :
    #{T ∈ X.powerset | e ∩ T = ∅} ≤ 2 ^ (#X - #e) := by
  have hc : #((X \ e).powerset) = 2 ^ (#X - #e) := by
    rw [card_powerset, card_sdiff_of_subset he]
  rw [← hc]
  refine card_le_card fun T hT => ?_
  rw [mem_filter, mem_powerset] at hT
  rw [mem_powerset]
  intro x hx
  refine mem_sdiff.2 ⟨hT.1 hx, fun hxe => ?_⟩
  have : x ∈ e ∩ T := mem_inter.2 ⟨hxe, hx⟩
  rw [hT.2] at this
  exact notMem_empty x this

end Counting

/-- **Erdős' lower bound for property B** (Zhao, Theorem 1.3.1; Erdős 1964).

Every `k`-uniform hypergraph with fewer than `2 ^ (k - 1)` edges is 2-colourable; that is,
`m k ≥ 2 ^ (k - 1)`, where `m k` is the least number of edges of a `k`-uniform hypergraph
that is not 2-colourable.

The book's proof takes a uniformly random 2-colouring of the vertices: each edge is
monochromatic with probability `2 ^ (1 - k)`, so the expected number of monochromatic
edges is `#E * 2 ^ (1 - k) < 1`, and some colouring has none. -/
theorem twoColorable_of_card_lt_two_pow {k : ℕ} {E : Finset (Finset V)}
    (hk : ∀ e ∈ E, #e = k) (hE : #E < 2 ^ (k - 1)) : TwoColorable E := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => false, by simp⟩
  obtain ⟨e₀, he₀⟩ := hne
  -- `k = 0` would force `E = ∅` via `2 ^ (0 - 1) = 1`, so the edges are nonempty.
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · have h1 : 1 ≤ #E := card_pos.mpr ⟨e₀, he₀⟩
      have h2 : (2 : ℕ) ^ (0 - 1) = 1 := rfl
      omega
    · exact h
  -- Only the vertices that actually occur matter.
  set X : Finset V := E.biUnion id with hXdef
  have hsub : ∀ e ∈ E, e ⊆ X := by
    intro e he x hx
    exact mem_biUnion.mpr ⟨e, he, hx⟩
  have hkX : k ≤ #X := by
    have h := card_le_card (hsub e₀ he₀)
    rwa [hk e₀ he₀] at h
  -- A colouring is a `T ⊆ X`, read as the vertices coloured `true`. An edge is
  -- monochromatic exactly when `T` swallows it or misses it entirely.
  set bad : Finset (Finset V) :=
    X.powerset.filter (fun T => ∃ e ∈ E, e ⊆ T ∨ e ∩ T = ∅) with hbaddef
  have hcover : bad ⊆ E.biUnion (fun e => X.powerset.filter (fun T => e ⊆ T ∨ e ∩ T = ∅)) := by
    intro T hT
    rw [hbaddef, mem_filter] at hT
    obtain ⟨e, he, hor⟩ := hT.2
    exact mem_biUnion.mpr ⟨e, he, mem_filter.mpr ⟨hT.1, hor⟩⟩
  have hstep : ∀ e ∈ E,
      #(X.powerset.filter (fun T => e ⊆ T ∨ e ∩ T = ∅)) ≤ 2 * 2 ^ (#X - k) := by
    intro e he
    have hek : #e = k := hk e he
    calc #(X.powerset.filter (fun T => e ⊆ T ∨ e ∩ T = ∅))
        ≤ #(X.powerset.filter (fun T => e ⊆ T))
            + #(X.powerset.filter (fun T => e ∩ T = ∅)) := by
          rw [filter_or]; exact card_union_le _ _
      _ ≤ 2 ^ (#X - k) + 2 ^ (#X - k) := by
          rw [← hek]
          exact Nat.add_le_add (card_filter_superset_le X e (hsub e he))
            (card_filter_disjoint_le X e (hsub e he))
      _ = 2 * 2 ^ (#X - k) := (two_mul _).symm
  have hbadle : #bad ≤ #E * (2 * 2 ^ (#X - k)) := by
    refine (card_le_card hcover).trans (card_biUnion_le.trans ?_)
    calc ∑ e ∈ E, #(X.powerset.filter (fun T => e ⊆ T ∨ e ∩ T = ∅))
        ≤ ∑ _e ∈ E, 2 * 2 ^ (#X - k) := sum_le_sum hstep
      _ = #E * (2 * 2 ^ (#X - k)) := by rw [sum_const, smul_eq_mul]
  -- `#E < 2 ^ (k-1)` is exactly what makes the bad colourings a minority.
  have hlt : #E * (2 * 2 ^ (#X - k)) < 2 ^ #X := by
    have hpow : 2 ^ (k - 1) * 2 = 2 ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel hk1]
    have h1 : #E * 2 < 2 ^ k := by omega
    calc #E * (2 * 2 ^ (#X - k)) = #E * 2 * 2 ^ (#X - k) := (mul_assoc _ _ _).symm
      _ < 2 ^ k * 2 ^ (#X - k) := (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 h1
      _ = 2 ^ #X := by rw [← pow_add, Nat.add_sub_cancel' hkX]
  have hcard : #bad < #(X.powerset) := by
    rw [card_powerset]; omega
  obtain ⟨T, hTX, hTbad⟩ := exists_mem_notMem_of_card_lt_card hcard
  refine ⟨fun v => decide (v ∈ T), fun e he => ?_⟩
  rw [hbaddef, mem_filter, not_and] at hTbad
  have hno := hTbad hTX
  have hnsub : ¬ e ⊆ T := fun h => hno ⟨e, he, Or.inl h⟩
  have hnint : ¬ e ∩ T = ∅ := fun h => hno ⟨e, he, Or.inr h⟩
  obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.mpr hnint
  rw [mem_inter] at hu
  obtain ⟨v, hv, hvT⟩ := not_subset.mp hnsub
  exact ⟨u, hu.1, v, hv, by simp [hu.2, hvT]⟩

end PMC
