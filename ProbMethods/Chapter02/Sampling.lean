import ProbMethods.Basic

/-!
# §2.4 — Sampling

Zhao, *Probabilistic Methods in Combinatorics*, Proposition 2.4.4.

Question 2.4.1 — the exact hypergraph Turán density for the tetrahedron — is a notorious
open problem and is not a node. Only the sampling upper bound is formalized.
-/

open Finset

namespace PMC

section Sampling

variable {n : ℕ}

/-- **Base case of the sampling argument.** A tetrahedron-free 3-graph contains at most
`7` of the `10` triples spanned by any five vertices.

Every one of the `C(5,4) = 5` four-subsets of `S` must omit one of its own triples, or it
would be a tetrahedron; and each triple of `S` lies in exactly `2` of those four-subsets.
Counting the incidences gives `2 * (number of omitted triples) ≥ 5`, so at least `3` of
the ten triples are missing. The bound `7` is attained. -/
private lemma card_filter_le_seven {H : Finset (Finset (Fin n))} (hH : IsThreeGraph H)
    (hfree : ¬ HasTetrahedron H) {S : Finset (Fin n)} (hS : #S = 5) :
    #{e ∈ H | e ⊆ S} ≤ 7 := by
  -- Recast the edges inside `S` as a subfamily of the ten triples of `S`.
  have hEq : {e ∈ H | e ⊆ S} = {e ∈ powersetCard 3 S | e ∈ H} := by
    ext e
    simp only [mem_filter, mem_powersetCard]
    exact ⟨fun h => ⟨⟨h.2, hH e h.1⟩, h.1⟩, fun h => ⟨h.2, h.1.1⟩⟩
  have hsplit : #{e ∈ powersetCard 3 S | e ∈ H}
      + #{e ∈ powersetCard 3 S | e ∉ H} = 10 := by
    rw [card_filter_add_card_filter_not, card_powersetCard, hS]
    rfl
  -- Every four-subset of `S` omits a triple, i.e. contributes an incidence.
  have hT : ∀ T ∈ powersetCard 4 S,
      1 ≤ #{e ∈ {e ∈ powersetCard 3 S | e ∉ H} | e ⊆ T} := by
    intro T hTmem
    rw [mem_powersetCard] at hTmem
    rw [Nat.succ_le_iff, card_pos]
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    refine hfree ⟨T, hTmem.2, fun e he => ?_⟩
    rw [mem_powersetCard] at he
    by_contra hnotH
    have hmem : e ∈ {e ∈ {e ∈ powersetCard 3 S | e ∉ H} | e ⊆ T} := by
      rw [mem_filter, mem_filter, mem_powersetCard]
      exact ⟨⟨⟨he.1.trans hTmem.1, he.2⟩, hnotH⟩, he.1⟩
    rw [hcon] at hmem
    exact notMem_empty e hmem
  -- Each omitted triple lies in exactly two four-subsets of `S`.
  have hpair : ∀ e ∈ {e ∈ powersetCard 3 S | e ∉ H},
      #{T ∈ powersetCard 4 S | e ⊆ T} = 2 := by
    intro e he
    rw [mem_filter, mem_powersetCard] at he
    have hcard3 : #e = 3 := he.1.2
    have h2 := card_filter_powersetCard_subset e S 4 he.1.1 (by omega)
    rw [h2, hS, hcard3]
    rfl
  -- Incidence count in both directions.
  have hincidence : 5 ≤ 2 * #{e ∈ powersetCard 3 S | e ∉ H} := by
    have hdc : ∑ T ∈ powersetCard 4 S,
          #{e ∈ {e ∈ powersetCard 3 S | e ∉ H} | e ⊆ T}
        = ∑ e ∈ {e ∈ powersetCard 3 S | e ∉ H},
            #{T ∈ powersetCard 4 S | e ⊆ T} := by
      simp only [card_filter]
      exact sum_comm
    have hlow : 5 ≤ ∑ T ∈ powersetCard 4 S,
        #{e ∈ {e ∈ powersetCard 3 S | e ∉ H} | e ⊆ T} := by
      calc 5 = ∑ _T ∈ powersetCard 4 S, 1 := by
            rw [sum_const, card_powersetCard, hS, smul_eq_mul, mul_one]
            rfl
        _ ≤ _ := sum_le_sum hT
    have hhigh : ∑ e ∈ {e ∈ powersetCard 3 S | e ∉ H},
        #{T ∈ powersetCard 4 S | e ⊆ T} = 2 * #{e ∈ powersetCard 3 S | e ∉ H} := by
      rw [sum_congr rfl hpair, sum_const, smul_eq_mul, Nat.mul_comm]
    omega
  rw [hEq]
  omega

end Sampling

/-- **Tetrahedron-free 3-graphs are sparse** (Zhao, Proposition 2.4.4).

A tetrahedron-free 3-graph on `n ≥ 5` vertices has at most `(7/10) * C(n, 3)` edges,
stated as `10 * #H ≤ 7 * n.choose 3` to stay in `ℕ` without division.

**The notes state this for `n ≥ 4`, which is off by one.** On four vertices the extremal
tetrahedron-free 3-graph has `3` of the `4` triples — omit any single triple and no
tetrahedron remains — while `(7/10) * C(4,3) = 2.8`. The `n ≥ 5` hypothesis is also what
the argument actually needs, since it samples five vertices at a time.

The proof samples `5` of the `n` vertices: averaging the edge density over all `5`-subsets
reduces the claim to the base case, that a tetrahedron-free 3-graph on `5` vertices has at
most `7` of its `10` triples. That base case is exactly tight. -/
theorem card_le_of_not_hasTetrahedron {n : ℕ} (hn : 5 ≤ n) (H : Finset (Finset (Fin n)))
    (hH : IsThreeGraph H) (hfree : ¬ HasTetrahedron H) :
    10 * #H ≤ 7 * n.choose 3 := by
  -- Double count pairs (five-subset `S`, edge of `H` inside `S`).
  have hdc : ∑ S ∈ powersetCard 5 (univ : Finset (Fin n)), #{e ∈ H | e ⊆ S}
      = ∑ e ∈ H, #{S ∈ powersetCard 5 (univ : Finset (Fin n)) | e ⊆ S} := by
    simp only [card_filter]
    exact sum_comm
  -- Each edge lies in `C(n - 3, 2)` of the five-subsets.
  have hright : ∑ e ∈ H, #{S ∈ powersetCard 5 (univ : Finset (Fin n)) | e ⊆ S}
      = #H * (n - 3).choose 2 := by
    have hconst : ∀ e ∈ H,
        #{S ∈ powersetCard 5 (univ : Finset (Fin n)) | e ⊆ S} = (n - 3).choose 2 := by
      intro e he
      have hcard3 : #e = 3 := hH e he
      have h2 := card_filter_powersetCard_subset e (univ : Finset (Fin n)) 5
        (subset_univ e) (by omega)
      rw [h2, card_univ, Fintype.card_fin, hcard3]
    rw [sum_congr rfl hconst, sum_const, smul_eq_mul]
  -- Each five-subset carries at most seven edges, by the base case.
  have hleft : ∑ S ∈ powersetCard 5 (univ : Finset (Fin n)), #{e ∈ H | e ⊆ S}
      ≤ 7 * n.choose 5 := by
    calc ∑ S ∈ powersetCard 5 (univ : Finset (Fin n)), #{e ∈ H | e ⊆ S}
        ≤ ∑ _S ∈ powersetCard 5 (univ : Finset (Fin n)), 7 := by
          refine sum_le_sum fun S hS => ?_
          rw [mem_powersetCard] at hS
          exact card_filter_le_seven hH hfree hS.2
      _ = 7 * n.choose 5 := by
          rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul,
            Nat.mul_comm]
  have hkey : #H * (n - 3).choose 2 ≤ 7 * n.choose 5 := by
    rw [← hright, ← hdc]; exact hleft
  -- `C(n,5) * C(5,3) = C(n,3) * C(n-3,2)` counts a five-set with a distinguished triple.
  have h53 : (5 : ℕ).choose 3 = 10 := rfl
  have hid : n.choose 5 * 10 = n.choose 3 * (n - 3).choose 2 := by
    have h := Nat.choose_mul (n := n) (k := 5) (s := 3) (by omega)
    rwa [h53] at h
  -- Cancel `C(n - 3, 2)`, which is positive because `5 ≤ n`.
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.choose_pos (by omega : 2 ≤ n - 3))
  rw [mul_assoc, mul_assoc, ← hid]
  calc 10 * (#H * (n - 3).choose 2) ≤ 10 * (7 * n.choose 5) :=
        Nat.mul_le_mul (le_refl 10) hkey
    _ = 7 * (n.choose 5 * 10) := by
        rw [Nat.mul_comm (n.choose 5) 10, mul_left_comm]

end PMC
