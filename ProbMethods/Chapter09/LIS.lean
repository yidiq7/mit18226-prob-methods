import ProbMethods.Chapter09.Talagrand

/-!
# §9.5 — the longest increasing subsequence

Corollary 9.5.23 concentrates the length of the longest increasing subsequence. The notes
state it asymptotically (`P(|X - M X| ≤ C n^{1/4}) ≥ 1 - ε`), but its **content** is the tail
bound that Theorem 9.5.21 gives directly, and that is finite:

    #{x : lis x ≤ k - t} · #{x : lis x ≥ k} ≤ |β|^{2n} · e^{-t²/(4k)}.

The two hypotheses of Theorem 9.5.21 hold for `lis` for clean reasons, and both are recorded
here as lemmas:

* **Lipschitz** — changing one coordinate changes `lis` by at most one, because deleting that
  index from a witness leaves an increasing subsequence of the other point;
* **certifiable** — `{lis ≥ k}` is `k`-certifiable, with the certificate being `k` indices of
  a witnessing subsequence: any point agreeing there has the same subsequence increasing.

The second is the reason the notes' `s`-certifiability hypothesis is the right one: it is
exactly what a "witness of size `s`" means.
-/

open Finset

namespace PMC

section LIS

variable {β : Type*} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β] {n : ℕ}

/-- `S` indexes an increasing subsequence of `x`. -/
def IsIncreasing (x : Fin n → β) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i < j → x i < x j

lemma isIncreasing_subset {x : Fin n → β} {S T : Finset (Fin n)} (hST : S ⊆ T)
    (hT : IsIncreasing x T) : IsIncreasing x S :=
  fun i hi j hj hij => hT i (hST hi) j (hST hj) hij

/-- The length of the longest increasing subsequence. -/
noncomputable def lisLength (x : Fin n → β) : ℕ := by
  classical
  exact ((univ : Finset (Finset (Fin n))).filter fun S => IsIncreasing x S).sup Finset.card

lemma le_lisLength {x : Fin n → β} {S : Finset (Fin n)} (hS : IsIncreasing x S) :
    #S ≤ lisLength x := by
  classical
  rw [lisLength]
  exact Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_univ _, hS⟩)

lemma exists_witness (x : Fin n → β) :
    ∃ S : Finset (Fin n), IsIncreasing x S ∧ #S = lisLength x := by
  classical
  have hne : ((univ : Finset (Finset (Fin n))).filter fun S => IsIncreasing x S).Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    intro i hi
    exact absurd hi (Finset.notMem_empty i)
  obtain ⟨S, hS, hval⟩ := Finset.exists_mem_eq_sup' hne Finset.card
  refine ⟨S, (mem_filter.mp hS).2, ?_⟩
  rw [lisLength, Finset.sup'_eq_sup hne] at *
  exact hval.symm

/-- **Changing one coordinate changes the length by at most one**: drop that index from a
witness and the rest is still increasing for the other point. -/
lemma lisLength_le_succ {x y : Fin n → β} {i : Fin n} (hxy : ∀ j, j ≠ i → x j = y j) :
    lisLength x ≤ lisLength y + 1 := by
  classical
  obtain ⟨S, hS, hcard⟩ := exists_witness x
  have hSy : IsIncreasing y (S.erase i) := by
    intro a ha b hb hab
    have hane : a ≠ i := (Finset.mem_erase.mp ha).1
    have hbne : b ≠ i := (Finset.mem_erase.mp hb).1
    rw [← hxy a hane, ← hxy b hbne]
    exact hS a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2 hab
  have h1 : #(S.erase i) ≤ lisLength y := le_lisLength hSy
  have h2 : #S ≤ #(S.erase i) + 1 := by
    by_cases hi : i ∈ S
    · rw [Finset.card_erase_of_mem hi]
      omega
    · rw [Finset.erase_eq_of_notMem hi]
      omega
  omega

/-- `lisLength` is `1`-Lipschitz for the Hamming distance. -/
lemma hammingLipschitz_lisLength :
    HammingLipschitz (fun x : Fin n → β => (lisLength x : ℝ)) := by
  classical
  intro x y
  rcases eq_or_ne x y with rfl | hne
  · rw [sub_self, abs_zero]
    positivity
  · -- the two points differ somewhere, so the Hamming distance is at least one
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hcon
      push_neg at hcon
      exact hne (funext hcon)
    have hone : (1 : ℝ) ≤ #((univ : Finset (Fin n)).filter fun j => x j ≠ y j) := by
      have : (1 : ℕ) ≤ #((univ : Finset (Fin n)).filter fun j => x j ≠ y j) := by
        refine Finset.card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
      exact_mod_cast this
    -- and changing one coordinate at a time moves the length by at most one
    have hxy : ∀ j, j ≠ i → x j = y j ∨ True := fun j _ => Or.inr trivial
    have hd : ∀ u v : Fin n → β, (∀ j, j ≠ i → u j = v j) →
        (lisLength u : ℝ) ≤ lisLength v + 1 := by
      intro u v huv
      have := lisLength_le_succ huv
      exact_mod_cast this
    -- the general bound: `|lis x - lis y| ≤ #{j : x j ≠ y j}` follows from monotone deletion
    have hgen : ∀ u v : Fin n → β,
        (lisLength u : ℝ) ≤ lisLength v + #((univ : Finset (Fin n)).filter fun j => u j ≠ v j) := by
      intro u v
      classical
      obtain ⟨S, hS, hcard⟩ := exists_witness u
      set D : Finset (Fin n) := (univ : Finset (Fin n)).filter fun j => u j ≠ v j with hD
      have hSv : IsIncreasing v (S \ D) := by
        intro a ha b hb hab
        have hau : u a = v a := by
          have := (Finset.mem_sdiff.mp ha).2
          rw [hD, mem_filter] at this
          by_contra hcon
          exact this ⟨mem_univ _, hcon⟩
        have hbu : u b = v b := by
          have := (Finset.mem_sdiff.mp hb).2
          rw [hD, mem_filter] at this
          by_contra hcon
          exact this ⟨mem_univ _, hcon⟩
        rw [← hau, ← hbu]
        exact hS a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1 hab
      have h1 : #(S \ D) ≤ lisLength v := le_lisLength hSv
      have h2 : #S ≤ #(S \ D) + #D := by
        have := Finset.card_sdiff_add_card_inter S D
        have h3 : #(S ∩ D) ≤ #D := Finset.card_le_card Finset.inter_subset_right
        omega
      have : lisLength u ≤ lisLength v + #D := by omega
      exact_mod_cast this
    have hsym : ((univ : Finset (Fin n)).filter fun j => y j ≠ x j)
        = (univ : Finset (Fin n)).filter fun j => x j ≠ y j := by
      refine Finset.filter_congr fun j _ => ?_
      exact ⟨fun h hcon => h hcon.symm, fun h hcon => h hcon.symm⟩
    have hxy1 := hgen x y
    have hyx1 := hgen y x
    rw [hsym] at hyx1
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩

/-- **`{lis ≥ k}` is `k`-certifiable**: `k` indices of a witnessing subsequence certify it. -/
lemma certifiable_lisLength (k : ℕ) :
    Certifiable (fun x : Fin n → β => (k : ℝ) ≤ (lisLength x : ℝ)) k := by
  classical
  intro y hy
  obtain ⟨S, hS, hcard⟩ := exists_witness y
  have hk : k ≤ #S := by
    have : (k : ℝ) ≤ lisLength y := hy
    have hk' : k ≤ lisLength y := by exact_mod_cast this
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hk
  refine ⟨T, le_of_eq hTcard, fun z hz => ?_⟩
  have hTz : IsIncreasing z T := by
    intro a ha b hb hab
    rw [hz a ha, hz b hb]
    exact (isIncreasing_subset hTsub hS) a ha b hb hab
  have : k ≤ lisLength z := by
    rw [← hTcard]
    exact le_lisLength hTz
  exact_mod_cast this

/-- **The concentration of the longest increasing subsequence** (Corollary 9.5.23's content),
given Talagrand's inequality:

    #{x : lis x ≤ k - t} · #{x : lis x ≥ k} ≤ |β|^{2n} · e^{-t²/(4k)}.

The notes wrap this in an asymptotic statement about the median; the inequality itself is
finite and is what Theorem 9.5.21 delivers. -/
theorem card_mul_card_lisLength_le
    (talagrand : ∀ (A : Finset (Fin n → β)) (t' : ℝ), 0 ≤ t' →
      (#A : ℝ) * #((univ : Finset (Fin n → β)).filter fun x => t' ≤ convexDist A x)
        ≤ ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t' ^ 2) / 4))
    (hn : 0 < n) {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : 0 < t) :
    (#((univ : Finset (Fin n → β)).filter fun x => (lisLength x : ℝ) ≤ k - t) : ℝ)
        * #((univ : Finset (Fin n → β)).filter fun y => (k : ℝ) ≤ (lisLength y : ℝ))
      ≤ ((Fintype.card β : ℝ) ^ n) ^ 2 * Real.exp (-(t ^ 2) / (4 * k)) :=
  card_mul_card_certifiable_le talagrand hn hammingLipschitz_lisLength ht hk
    (certifiable_lisLength k)

end LIS

end PMC
