import ProbMethods.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# §2.4 — Sampling

Zhao, *Probabilistic Methods in Combinatorics*, Proposition 2.4.4.

Question 2.4.1 — the exact hypergraph Turán density for the tetrahedron — is a notorious
open problem and is not a node. Only the sampling upper bound is formalized.
-/

open Finset

namespace PMC

section SupersetCount

variable {α : Type*} [DecidableEq α]

/-- The `k`-subsets of `X` containing a fixed `T ⊆ X` correspond to the
`(k - #T)`-subsets of `X \ T`. -/
private lemma card_filter_superset (X T : Finset α) (hTX : T ⊆ X) (k : ℕ) (hk : #T ≤ k) :
    #{S ∈ powersetCard k X | T ⊆ S} = (#X - #T).choose (k - #T) := by
  have hXT : #X - #T = #(X \ T) := (card_sdiff_of_subset hTX).symm
  rw [hXT, ← card_powersetCard]
  refine card_bij (fun S _ => S \ T) ?_ ?_ ?_
  · intro S hS
    rw [mem_filter, mem_powersetCard] at hS
    obtain ⟨⟨hSX, hScard⟩, hTS⟩ := hS
    rw [mem_powersetCard]
    refine ⟨sdiff_subset_sdiff hSX Subset.rfl, ?_⟩
    rw [card_sdiff_of_subset hTS, hScard]
  · intro S₁ h₁ S₂ h₂ heq
    rw [mem_filter] at h₁ h₂
    rw [← sdiff_union_of_subset h₁.2, ← sdiff_union_of_subset h₂.2, heq]
  · intro R hR
    rw [mem_powersetCard] at hR
    obtain ⟨hRX, hRcard⟩ := hR
    have hdisj : Disjoint R T := by
      rw [Finset.disjoint_right]
      intro x hxT hxR
      exact (mem_sdiff.mp (hRX hxR)).2 hxT
    refine ⟨R ∪ T, ?_, ?_⟩
    · rw [mem_filter, mem_powersetCard]
      refine ⟨⟨?_, ?_⟩, subset_union_right⟩
      · exact union_subset (hRX.trans sdiff_subset) hTX
      · rw [card_union_of_disjoint hdisj, hRcard]
        omega
    · ext x
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact h1
        · exact absurd h1 h2
      · intro hx
        exact ⟨Or.inl hx, fun hxT => Finset.disjoint_left.mp hdisj hx hxT⟩

end SupersetCount

section BaseCase

variable {n : ℕ}

/-- **The base case.** On five vertices a tetrahedron-free 3-graph has at most `7` of the
`10` triples.

Counting incidences between the `5` four-subsets and the triples *missing* from `H`: every
four-subset must miss at least one of its own triples, or it would be a tetrahedron, and
every missing triple lies in exactly `2` four-subsets. So `2 * #M ≥ 5`, hence `#M ≥ 3`. -/
private lemma card_le_seven_of_card_eq_five (H : Finset (Finset (Fin n)))
    (hH : IsThreeGraph H) (hfree : ¬ HasTetrahedron H) {S : Finset (Fin n)} (hS : #S = 5) :
    #{T ∈ H | T ⊆ S} ≤ 7 := by
  classical
  set M := {T ∈ powersetCard 3 S | T ∉ H} with hMdef
  -- Every four-subset of `S` supplies a missing triple.
  have hQ : ∀ Q ∈ powersetCard 4 S, ∃ T ∈ M, T ⊆ Q := by
    intro Q hQmem
    rw [mem_powersetCard] at hQmem
    by_contra hcon
    push_neg at hcon
    refine hfree ⟨Q, hQmem.2, fun e he => ?_⟩
    rw [mem_powersetCard] at he
    by_contra hne
    exact hcon e (mem_filter.mpr
      ⟨mem_powersetCard.mpr ⟨he.1.trans hQmem.1, he.2⟩, hne⟩) he.1
  -- Each missing triple lies in exactly two four-subsets.
  have hfib : ∀ T ∈ M, #{Q ∈ powersetCard 4 S | T ⊆ Q} = 2 := by
    intro T hT
    rw [hMdef, mem_filter, mem_powersetCard] at hT
    have h := card_filter_superset S T hT.1.1 4 (by omega)
    rw [hS, hT.1.2] at h
    simpa using h
  -- Two ways of counting the (four-subset, missing triple) incidences.
  have hexch : ∑ Q ∈ powersetCard 4 S, #{T ∈ M | T ⊆ Q}
      = ∑ T ∈ M, #{Q ∈ powersetCard 4 S | T ⊆ Q} := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hge : #(powersetCard 4 S) ≤ ∑ Q ∈ powersetCard 4 S, #{T ∈ M | T ⊆ Q} := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun Q hQmem => ?_
    obtain ⟨T, hT, hTQ⟩ := hQ Q hQmem
    exact Finset.card_pos.mpr ⟨T, mem_filter.mpr ⟨hT, hTQ⟩⟩
  have hfive : #(powersetCard 4 S) = 5 := by
    rw [card_powersetCard, hS]
    decide
  have hMge : 3 ≤ #M := by
    rw [hexch, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hge
    omega
  -- The triples of `S` split into those in `H` and those missing.
  have hIn : {T ∈ H | T ⊆ S} = {T ∈ powersetCard 3 S | T ∈ H} := by
    ext T
    simp only [mem_filter, mem_powersetCard]
    exact ⟨fun h => ⟨⟨h.2, hH T h.1⟩, h.1⟩, fun h => ⟨h.2, h.1.1⟩⟩
  have hsplit : #{T ∈ powersetCard 3 S | T ∈ H} + #M = 10 := by
    rw [hMdef]
    have h := Finset.card_filter_add_card_filter_not
      (s := powersetCard 3 S) (p := fun T => T ∈ H)
    rw [card_powersetCard, hS] at h
    norm_num at h
    exact h
  rw [hIn]
  omega

end BaseCase


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
  classical
  -- Count (five-subset, triple of `H` inside it) incidences two ways.
  have hexch : ∑ S ∈ powersetCard 5 (univ : Finset (Fin n)), #{T ∈ H | T ⊆ S}
      = ∑ T ∈ H, #{S ∈ powersetCard 5 (univ : Finset (Fin n)) | T ⊆ S} := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  -- Each triple of `H` lies in `C(n-3, 2)` five-subsets.
  have hfib : ∀ T ∈ H, #{S ∈ powersetCard 5 (univ : Finset (Fin n)) | T ⊆ S}
      = (n - 3).choose 2 := by
    intro T hT
    have h := card_filter_superset (univ : Finset (Fin n)) T (subset_univ T) 5
      (by rw [hH T hT]; omega)
    rw [hH T hT, card_univ, Fintype.card_fin] at h
    simpa using h
  -- Each five-subset carries at most seven of them.
  have hbase : ∑ S ∈ powersetCard 5 (univ : Finset (Fin n)), #{T ∈ H | T ⊆ S}
      ≤ 7 * n.choose 5 := by
    calc ∑ S ∈ powersetCard 5 (univ : Finset (Fin n)), #{T ∈ H | T ⊆ S}
        ≤ ∑ _S ∈ powersetCard 5 (univ : Finset (Fin n)), 7 := by
          refine Finset.sum_le_sum fun S hS => ?_
          rw [mem_powersetCard] at hS
          exact card_le_seven_of_card_eq_five H hH hfree hS.2
      _ = 7 * n.choose 5 := by
          rw [Finset.sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul,
            mul_comm]
  -- Combine: #H * C(n-3,2) ≤ 7 * C(n,5), and C(n,3) * C(n-3,2) = 10 * C(n,5).
  have hleft : #H * (n - 3).choose 2 ≤ 7 * n.choose 5 := by
    rw [hexch, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hbase
    exact hbase
  have hkey : n.choose 3 * (n - 3).choose 2 = 10 * n.choose 5 := by
    have h := Nat.choose_mul (n := n) (k := 5) (s := 3) (by omega)
    rw [show Nat.choose 5 3 = 10 from by decide,
      show (5 : ℕ) - 3 = 2 from rfl] at h
    rw [← h]
    exact Nat.mul_comm _ _
  have hpos : 0 < (n - 3).choose 2 := Nat.choose_pos (by omega)
  have : 10 * #H * (n - 3).choose 2 ≤ 7 * n.choose 3 * (n - 3).choose 2 := by
    calc 10 * #H * (n - 3).choose 2 = 10 * (#H * (n - 3).choose 2) := by
          rw [mul_assoc]
      _ ≤ 10 * (7 * n.choose 5) := Nat.mul_le_mul_left _ hleft
      _ = 7 * (10 * n.choose 5) := mul_left_comm _ _ _
      _ = 7 * (n.choose 3 * (n - 3).choose 2) := by rw [hkey]
      _ = 7 * n.choose 3 * (n - 3).choose 2 := by rw [mul_assoc]
  exact Nat.le_of_mul_le_mul_right this hpos

end PMC
