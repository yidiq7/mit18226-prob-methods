import ProbMethods.Chapter09.HammingCube

/-!
# §4.6 — the Dubroff–Fox–Xu bound (Theorem 4.6.6)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 4.6.6 (Dubroff, Fox and Xu 2021): if
some `k`-element subset of `[n]` has distinct subset sums then

    n ≥ C(k, ⌊k/2⌋).

This is the best known leading constant for the Erdős distinct-sums problem, and its proof is
short and entirely combinatorial once Harper's isoperimetric inequality in the cube is
granted:

* let `A` be the set of `ε ∈ {0,1}^k` with `∑ εᵢxᵢ` *below* half the total. Distinctness rules
  out equality, so complementation pairs each subset with exactly one of `A`, `Aᶜ` — hence
  `|A| = 2^{k-1}`, half the cube (`PMC.card_lowHalf`);
* a point of the vertex boundary `∂A` is `S ∪ {i}` for some `S ∈ A`: it cannot be an erasure,
  since erasing only lowers the sum. So its sum lies strictly between `T/2` and `T/2 + n`,
  an interval holding at most `n` integers, and distinctness makes the sum injective on `∂A`.
  Hence `|∂A| ≤ n` (`PMC.card_boundary_lowHalf_le`);
* Harper says a half-cube's boundary is at least `C(k, ⌊k/2⌋)`.

**Harper's inequality is an explicit hypothesis here.** Its ball form is published as a task
(`PMC.card_cubeNbhd_lowBall_le`), and the form this proof needs — a lower bound on the boundary
of *any* set of size `2^{k-1}` — does not follow from the ball form alone when `k` is even,
because then the extremal set is a ball together with part of one level. Taking it as a
hypothesis keeps this file `sorry`-free and puts the missing input in the statement, where the
new mathematics of the theorem (the reduction) is visibly separate from the classical
ingredient (the isoperimetry).

The file imports Chapter 9 for the cube machinery, which is where it lives; the *result* is
§4.6's.
-/

open Finset

namespace PMC

section DubroffFoxXu

variable {k : ℕ}

/-- The subsets whose weighted sum is strictly below half the total. -/
def lowHalf (x : Fin k → ℕ) : Finset (Finset (Fin k)) :=
  (univ : Finset (Finset (Fin k))).filter fun S => 2 * (∑ i ∈ S, x i) < ∑ i, x i

lemma mem_lowHalf {x : Fin k → ℕ} {S : Finset (Fin k)} :
    S ∈ lowHalf x ↔ 2 * (∑ i ∈ S, x i) < ∑ i, x i := by
  rw [lowHalf, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- Distinct subset sums rule out a subset summing to exactly half the total: it would have
the same sum as its complement. -/
lemma two_mul_sum_ne (hk : 1 ≤ k) {x : Fin k → ℕ}
    (hdist : ∀ S T : Finset (Fin k), ∑ i ∈ S, x i = ∑ i ∈ T, x i → S = T)
    (S : Finset (Fin k)) : 2 * (∑ i ∈ S, x i) ≠ ∑ i, x i := by
  intro h
  have hsplit : (∑ i ∈ S, x i) + (∑ i ∈ Sᶜ, x i) = ∑ i, x i :=
    Finset.sum_add_sum_compl S x
  have heq : ∑ i ∈ S, x i = ∑ i ∈ Sᶜ, x i := by omega
  have hSS : S = Sᶜ := hdist S Sᶜ heq
  have hi : (⟨0, by omega⟩ : Fin k) ∈ S ↔ (⟨0, by omega⟩ : Fin k) ∉ S := by
    rw [← Finset.mem_compl, ← hSS]
  by_cases h0 : (⟨0, by omega⟩ : Fin k) ∈ S
  · exact (hi.mp h0) h0
  · exact h0 (hi.mpr h0)

/-- **Half the cube.** Complementation pairs each subset with exactly one of `A`, `Aᶜ`, so
`A` is exactly half of the `2^k` subsets. -/
theorem card_lowHalf (hk : 1 ≤ k) (x : Fin k → ℕ)
    (hdist : ∀ S T : Finset (Fin k), ∑ i ∈ S, x i = ∑ i ∈ T, x i → S = T) :
    2 * #(lowHalf x) = 2 ^ k := by
  classical
  have hne := two_mul_sum_ne hk hdist
  have hsplit : ∀ S : Finset (Fin k), (∑ i ∈ S, x i) + (∑ i ∈ Sᶜ, x i) = ∑ i, x i :=
    fun S => Finset.sum_add_sum_compl S x
  have hone : ∀ S : Finset (Fin k), S ∈ lowHalf x ∨ Sᶜ ∈ lowHalf x := by
    intro S
    rcases lt_or_gt_of_ne (hne S) with h | h
    · exact Or.inl (mem_lowHalf.mpr h)
    · refine Or.inr (mem_lowHalf.mpr ?_)
      have := hsplit S
      omega
  have hnotboth : ∀ S : Finset (Fin k), S ∈ lowHalf x → Sᶜ ∉ lowHalf x := by
    intro S hS hSc
    rw [mem_lowHalf] at hS hSc
    have := hsplit S
    omega
  have himg : #((lowHalf x).image fun S => Sᶜ) = #(lowHalf x) :=
    Finset.card_image_of_injective _ fun S T h => by
      simpa using congrArg (fun U : Finset (Fin k) => Uᶜ) h
  have hdisj : Disjoint (lowHalf x) ((lowHalf x).image fun S => Sᶜ) := by
    refine Finset.disjoint_left.mpr fun S hS hSimg => ?_
    obtain ⟨T, hT, hTS⟩ := Finset.mem_image.mp hSimg
    have hTc : Tᶜ ∈ lowHalf x := by rw [hTS]; exact hS
    exact hnotboth T hT hTc
  have hunion : (lowHalf x) ∪ ((lowHalf x).image fun S => Sᶜ)
      = (univ : Finset (Finset (Fin k))) := by
    refine Finset.eq_univ_of_forall fun S => ?_
    rw [Finset.mem_union]
    rcases hone S with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_image.mpr ⟨Sᶜ, h, by simp⟩)
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, himg, card_univ, Fintype.card_finset, Fintype.card_fin] at hcard
  omega

/-- A step of Hamming distance at most one either changes nothing, inserts a coordinate, or
erases one. -/
lemma eq_or_insert_or_erase {S T : Finset (Fin k)} (h : hamDist S T ≤ 1) :
    S = T ∨ (∃ i ∉ S, T = insert i S) ∨ ∃ i ∈ S, T = S.erase i := by
  classical
  rw [hamDist] at h
  rcases Nat.eq_zero_or_pos #(T \ S) with h1 | h1
  · rcases Nat.eq_zero_or_pos #(S \ T) with h2 | h2
    · refine Or.inl (Finset.Subset.antisymm ?_ ?_)
      · exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h2)
      · exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h1)
    · have hTS : T ⊆ S := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h1)
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (by omega : #(S \ T) = 1)
      have hiS : i ∈ S := (Finset.mem_sdiff.mp (by rw [hi]; exact Finset.mem_singleton_self i)).1
      refine Or.inr (Or.inr ⟨i, hiS, Finset.Subset.antisymm ?_ ?_⟩)
      · intro y hy
        refine Finset.mem_erase.mpr ⟨?_, hTS hy⟩
        intro hyi
        have : y ∈ S \ T := by rw [hi, hyi]; exact Finset.mem_singleton_self i
        exact (Finset.mem_sdiff.mp this).2 hy
      · intro y hy
        rw [Finset.mem_erase] at hy
        by_contra hyT
        have : y ∈ S \ T := Finset.mem_sdiff.mpr ⟨hy.2, hyT⟩
        rw [hi, Finset.mem_singleton] at this
        exact hy.1 this
  · have hST : S ⊆ T := by
      have : #(S \ T) = 0 := by omega
      exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp this)
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (by omega : #(T \ S) = 1)
    have hiT : i ∈ T := (Finset.mem_sdiff.mp (by rw [hi]; exact Finset.mem_singleton_self i)).1
    have hiS : i ∉ S := (Finset.mem_sdiff.mp (by rw [hi]; exact Finset.mem_singleton_self i)).2
    refine Or.inr (Or.inl ⟨i, hiS, Finset.Subset.antisymm ?_ ?_⟩)
    · intro y hy
      by_cases hyi : y = i
      · rw [hyi]
        exact Finset.mem_insert_self i S
      · refine Finset.mem_insert_of_mem ?_
        by_contra hyS
        have : y ∈ T \ S := Finset.mem_sdiff.mpr ⟨hy, hyS⟩
        rw [hi, Finset.mem_singleton] at this
        exact hyi this
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyS
      · exact hiT
      · exact hST hyS

/-- **The boundary of `A` is small.** Every point of the vertex boundary has weighted sum
strictly between `T/2` and `T/2 + n`, and distinct subset sums make that sum injective, so the
boundary has at most `n` points. -/
theorem card_boundary_lowHalf_le {n : ℕ} (hk : 1 ≤ k) {x : Fin k → ℕ} (hle : ∀ i, x i ≤ n)
    (hdist : ∀ S T : Finset (Fin k), ∑ i ∈ S, x i = ∑ i ∈ T, x i → S = T) :
    #(cubeNbhd 1 (lowHalf x) \ lowHalf x) ≤ n := by
  classical
  have hne := two_mul_sum_ne hk hdist
  -- each boundary point's sum lands in an interval of `n` integers
  have hmaps : ∀ T ∈ cubeNbhd 1 (lowHalf x) \ lowHalf x,
      (∑ i ∈ T, x i) ∈ Finset.Icc ((∑ i, x i) / 2 + 1) ((∑ i, x i) / 2 + n) := by
    intro T hT
    rw [Finset.mem_sdiff, mem_cubeNbhd] at hT
    obtain ⟨⟨S, hS, hdistST⟩, hTnot⟩ := hT
    rw [mem_lowHalf] at hS
    have hTlow : ¬ (2 * (∑ i ∈ T, x i) < ∑ i, x i) := fun h => hTnot (mem_lowHalf.mpr h)
    have hTup : ∑ i, x i < 2 * (∑ i ∈ T, x i) := by
      rcases Nat.lt_or_ge (∑ i, x i) (2 * (∑ i ∈ T, x i)) with h | h
      · exact h
      · exact absurd (le_antisymm h (by omega)) (hne T)
    -- the step must be an insertion
    have hins : ∃ i ∉ S, T = insert i S := by
      rcases eq_or_insert_or_erase hdistST with rfl | hins | ⟨i, hiS, rfl⟩
      · exact absurd (mem_lowHalf.mpr hS) hTnot
      · exact hins
      · exfalso
        have : ∑ i ∈ S.erase i, x i ≤ ∑ i ∈ S, x i :=
          Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
        omega
    obtain ⟨i, hiS, rfl⟩ := hins
    have hsum : ∑ j ∈ insert i S, x j = x i + ∑ j ∈ S, x j := Finset.sum_insert hiS
    have hxi := hle i
    rw [Finset.mem_Icc]
    omega
  have hinj : Set.InjOn (fun T => ∑ i ∈ T, x i)
      (cubeNbhd 1 (lowHalf x) \ lowHalf x : Finset (Finset (Fin k))) := by
    intro S _ T _ h
    exact hdist S T h
  calc #(cubeNbhd 1 (lowHalf x) \ lowHalf x)
      ≤ #(Finset.Icc ((∑ i, x i) / 2 + 1) ((∑ i, x i) / 2 + n)) :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = n := by rw [Nat.card_Icc]; omega

/-- **Theorem 4.6.6** (Dubroff, Fox and Xu 2021). If some `k` positive integers bounded by `n`
have distinct subset sums, then `C(k, ⌊k/2⌋) ≤ n`.

`harper` is Harper's isoperimetric inequality in the cube, in the form this proof needs: a set
of size **exactly** `2^{k-1}` has at least `C(k, ⌊k/2⌋)` points on its boundary. Its ball form
is task #46; see the file header for why the boundary form is taken as a hypothesis rather
than derived.

The `=` is not cosmetic. With `2^{k-1} ≤ #A` the hypothesis would be *false* — at `A = univ`
the boundary is empty — and the theorem would be vacuous. Checked by brute force for
`k ≤ 4`, where the equality form holds with equality: the minimum boundary of a half-cube-sized
set is exactly `C(k, ⌊k/2⌋)`. -/
theorem choose_le_of_distinct_subset_sums {n : ℕ} (hk : 1 ≤ k) (x : Fin k → ℕ)
    (hle : ∀ i, x i ≤ n)
    (hdist : ∀ S T : Finset (Fin k), ∑ i ∈ S, x i = ∑ i ∈ T, x i → S = T)
    (harper : ∀ A : Finset (Finset (Fin k)), #A = 2 ^ (k - 1) →
      #A + Nat.choose k (k / 2) ≤ #(cubeNbhd 1 A)) :
    Nat.choose k (k / 2) ≤ n := by
  classical
  have hhalf := card_lowHalf hk x hdist
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hA : #(lowHalf x) = 2 ^ (k - 1) := by omega
  have hharper := harper (lowHalf x) hA
  have hsub : lowHalf x ⊆ cubeNbhd 1 (lowHalf x) := by
    intro S hS
    exact mem_cubeNbhd.mpr ⟨S, hS, by simp [hamDist]⟩
  have hbdry : #(cubeNbhd 1 (lowHalf x) \ lowHalf x)
      = #(cubeNbhd 1 (lowHalf x)) - #(lowHalf x) := Finset.card_sdiff_of_subset hsub
  have hle' := card_boundary_lowHalf_le hk hle hdist
  omega

end DubroffFoxXu

end PMC
