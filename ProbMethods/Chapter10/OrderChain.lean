import ProbMethods.Chapter10.CondSupport

/-!
# The chain rule along an arbitrary order

§10.1's chain rule splits `H(X, Y)` as `H(X) + H(Y | X)`. Brégman–Minc (§10.2) needs it
iterated along a *chosen order* of the coordinates: for any permutation `τ` of the index set,

    H(X_1, …, X_n) = ∑ᵢ H(Xᵢ | X_j for j revealed before i).

That is the whole content of Radhakrishnan's proof — the identity holds for *every* order,
and the argument then averages the resulting bounds over a uniformly random one.

Formally this is a telescoping sum of `PMC.tupleEntropy` increments over the prefixes of `τ`,
which is why `PMC.tupleEntropy_insert` is proved first: adding one coordinate to a mask adds
exactly the conditional entropy of that coordinate.
-/

open Finset

namespace PMC

section OrderChain

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {β : Type*} [Fintype β] [DecidableEq β]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A mask together with one more coordinate carries exactly the information of the larger
mask. The pair's value type and the mask's have no bijection between them, so this goes
through `PMC.wentropy_congr`, which only needs the two maps to invert each other along the
ranges. -/
theorem wentropy_pair_masked_insert {w : Ω → ℝ} (hsum : ∑ ω, w ω = 1) (X : ι → Ω → β)
    (i : ι) (P : Finset ι) (hi : i ∉ P) :
    wentropy w (fun ω => (masked X P ω, X i ω)) = tupleEntropy w X (insert i P) := by
  classical
  have hΩ : Nonempty Ω := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  have hβ : Nonempty β := ⟨X i (Classical.arbitrary Ω)⟩
  refine wentropy_congr w (fun ω => (masked X P ω, X i ω)) (masked X (insert i P))
    (fun p => fun j => if j = i then some p.2 else p.1 j)
    (fun u => (projMask P u, (u i).getD (Classical.arbitrary β))) ?_ ?_
  · intro ω
    funext j
    simp only [masked, Finset.mem_insert]
    by_cases hj : j = i
    · subst hj
      simp [if_pos rfl]
    · simp only [if_neg hj, masked]
      by_cases hjP : j ∈ P <;> simp [hjP, hj]
  · intro ω
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · exact (projMask_masked X (Finset.subset_insert i P) ω).symm
    · simp only [masked, if_pos (Finset.mem_insert_self i P)]
      rfl

/-- **One coordinate at a time**: extending a mask by a coordinate adds exactly that
coordinate's conditional entropy. -/
theorem tupleEntropy_insert {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (X : ι → Ω → β) (i : ι) (P : Finset ι) (hi : i ∉ P) :
    tupleEntropy w X (insert i P)
      = tupleEntropy w X P + wcondEntropy w (masked X P) (X i) := by
  rw [← wentropy_pair_masked_insert hsum X i P hi, wentropy_chain hw (masked X P) (X i)]
  rfl

/-- The coordinates revealed strictly before `i` by the order `τ`. -/
def predSet {n : ℕ} (τ : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin n) :=
  (univ : Finset (Fin n)).filter fun j => τ j < τ i

/-- **The chain rule along the order `τ`.** For *every* permutation `τ` of the coordinates,

    H(X_univ) = ∑ᵢ H(Xᵢ | X_{predecessors of i}).

A telescoping sum over the prefixes of `τ`. -/
theorem tupleEntropy_univ_eq_sum_predSet {n : ℕ} {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hsum : ∑ ω, w ω = 1) (X : Fin n → Ω → β) (τ : Equiv.Perm (Fin n)) :
    tupleEntropy w X univ = ∑ i : Fin n, wcondEntropy w (masked X (predSet τ i)) (X i) := by
  classical
  -- the prefixes of the order, indexed by how many coordinates have been revealed
  set pre : ℕ → Finset (Fin n) := fun k => (univ : Finset (Fin n)).filter fun j => (τ j : ℕ) < k
    with hpre
  have hpre0 : pre 0 = ∅ := by
    rw [hpre]
    simp
  have hpren : pre n = univ := by
    rw [hpre]
    refine Finset.filter_true_of_mem ?_
    intro j _
    exact (τ j).isLt
  -- one step of the telescope
  have hstep : ∀ (k : Fin n),
      tupleEntropy w X (pre ((k : ℕ) + 1)) - tupleEntropy w X (pre (k : ℕ))
        = wcondEntropy w (masked X (predSet τ (τ.symm k))) (X (τ.symm k)) := by
    intro k
    have hpred : pre (k : ℕ) = predSet τ (τ.symm k) := by
      rw [hpre, predSet]
      refine Finset.filter_congr ?_
      intro j _
      rw [Equiv.apply_symm_apply, Fin.lt_def]
    have hnotmem : τ.symm k ∉ pre (k : ℕ) := by
      rw [hpre]
      simp [Equiv.apply_symm_apply]
    have hinsert : pre ((k : ℕ) + 1) = insert (τ.symm k) (pre (k : ℕ)) := by
      rw [hpre]
      ext j
      simp only [mem_filter, mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact Or.inr h
        · left
          rw [← Equiv.symm_apply_apply τ j]
          congr 1
          exact Fin.ext h
      · rintro (rfl | h)
        · rw [Equiv.apply_symm_apply]
          omega
        · omega
    rw [hinsert, hpred, tupleEntropy_insert hw hsum X _ _ (hpred ▸ hnotmem)]
    ring
  calc tupleEntropy w X univ
      = tupleEntropy w X (pre n) - tupleEntropy w X (pre 0) := by
        rw [hpren, hpre0, tupleEntropy_empty hsum, sub_zero]
    _ = ∑ k ∈ Finset.range n, (tupleEntropy w X (pre (k + 1)) - tupleEntropy w X (pre k)) :=
        (Finset.sum_range_sub (fun k => tupleEntropy w X (pre k)) n).symm
    _ = ∑ k : Fin n, (tupleEntropy w X (pre ((k : ℕ) + 1)) - tupleEntropy w X (pre (k : ℕ))) :=
        (Fin.sum_univ_eq_sum_range
          (fun k => tupleEntropy w X (pre (k + 1)) - tupleEntropy w X (pre k)) n).symm
    _ = ∑ k : Fin n, wcondEntropy w (masked X (predSet τ (τ.symm k))) (X (τ.symm k)) :=
        Finset.sum_congr rfl fun k _ => hstep k
    _ = ∑ i : Fin n, wcondEntropy w (masked X (predSet τ i)) (X i) :=
        Equiv.sum_comp τ.symm fun i => wcondEntropy w (masked X (predSet τ i)) (X i)

end OrderChain

end PMC
