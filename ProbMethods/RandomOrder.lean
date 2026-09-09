import ProbMethods.Permutation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Revealing in a uniformly random order

§10.2's proof of the Brégman–Minc inequality turns on one distributional fact, which the
notes state and leave as an exercise ("(Why?)"): if the rows are revealed in a uniformly
random order, then for each row the number of *greedily available* choices is uniform on
`{1, …, d}`, where `d` is that row's degree.

Stripped of its setting, the fact is about a uniformly random permutation `τ` and a fixed
`S`: the **rank** of `i` inside `S` — how many members of `S` are revealed at or after `i` —
is uniform on `{1, …, #S}`.

**The proof needs no order machinery**, which is worth recording because the obvious route
(pick out the `k`-th smallest element of `τ(S)` and swap) does. Two observations suffice:

* For each `τ`, *exactly one* element of `S` has rank `k` — the rank is a bijection from `S`
  onto `{1, …, #S}`, by strict monotonicity.
* The ranks are equidistributed across the elements of `S`: right-multiplying `τ` by
  `Equiv.swap i i'` exchanges the roles of `i` and `i'`, and preserves `S`.

Summing the first over `i ∈ S` and using the second gives `#S` classes of equal size, so each
has probability `1/#S`.
-/

open Finset

namespace PMC

section RandomOrder

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- How many members of `S` the order `τ` reveals at or after `i` — the number of choices
still "greedily available" to `i`. -/
def tauRank (S : Finset α) (τ : Equiv.Perm α) (i : α) : ℕ :=
  #(S.filter fun j => τ i ≤ τ j)

lemma tauRank_pos {S : Finset α} {i : α} (hi : i ∈ S) (τ : Equiv.Perm α) :
    0 < tauRank S τ i :=
  Finset.card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, le_refl _⟩⟩

lemma tauRank_le_card (S : Finset α) (τ : Equiv.Perm α) (i : α) : tauRank S τ i ≤ #S :=
  Finset.card_filter_le _ _

/-- The rank is strictly decreasing in `τ i`: later members of `S` have fewer choices left. -/
lemma tauRank_lt_of_lt {S : Finset α} {i i' : α} (hi : i ∈ S) (τ : Equiv.Perm α)
    (h : τ i < τ i') : tauRank S τ i' < tauRank S τ i := by
  refine Finset.card_lt_card ⟨fun j hj => ?_, ?_⟩
  · rw [mem_filter] at hj ⊢
    exact ⟨hj.1, le_trans (le_of_lt h) hj.2⟩
  · intro hsub
    have := hsub (mem_filter.mpr ⟨hi, le_refl _⟩)
    rw [mem_filter] at this
    exact absurd this.2 (not_le.mpr h)

/-- The rank is injective on `S`. -/
lemma tauRank_injOn (S : Finset α) (τ : Equiv.Perm α) :
    Set.InjOn (tauRank S τ) S := by
  intro i hi i' hi' heq
  rcases lt_trichotomy (τ i) (τ i') with h | h | h
  · exact absurd heq.symm (ne_of_lt (tauRank_lt_of_lt (by exact_mod_cast hi) τ h))
  · exact τ.injective h
  · exact absurd heq (ne_of_lt (tauRank_lt_of_lt (by exact_mod_cast hi') τ h))

/-- **Exactly one member of `S` has each rank.** The rank is a bijection from `S` onto
`{1, …, #S}`, so for `1 ≤ k ≤ #S` precisely one element of `S` has `k` choices available. -/
theorem card_filter_tauRank_eq_one (S : Finset α) (τ : Equiv.Perm α) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ #S) :
    #(S.filter fun i => tauRank S τ i = k) = 1 := by
  classical
  -- the rank maps `S` into `Icc 1 #S`, injectively, and both have `#S` elements
  have hmaps : ∀ i ∈ S, tauRank S τ i ∈ Finset.Icc 1 #S := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨tauRank_pos hi τ, tauRank_le_card S τ i⟩
  have himg : S.image (tauRank S τ) = Finset.Icc 1 #S := by
    refine Finset.eq_of_subset_of_card_le (fun m hm => ?_) ?_
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
      exact hmaps i hi
    · rw [Finset.card_image_of_injOn (tauRank_injOn S τ), Nat.card_Icc]
      simp
  -- so `k` is hit, and injectivity makes the preimage a singleton
  have hk' : k ∈ S.image (tauRank S τ) := by
    rw [himg]
    exact Finset.mem_Icc.mpr ⟨hk1, hk⟩
  obtain ⟨i, hiS, hik⟩ := Finset.mem_image.mp hk'
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  rw [mem_filter, Finset.mem_singleton]
  refine ⟨fun h => tauRank_injOn S τ h.1 hiS (h.2.trans hik.symm), fun h => ?_⟩
  subst h
  exact ⟨hiS, hik⟩

/-- Swapping two members of `S` permutes `S`. -/
private lemma swap_mem_of_mem {S : Finset α} {i i' : α} (hi : i ∈ S) (hi' : i' ∈ S) {j : α}
    (hj : j ∈ S) : Equiv.swap i i' j ∈ S := by
  rcases eq_or_ne j i with rfl | h1
  · rwa [Equiv.swap_apply_left]
  · rcases eq_or_ne j i' with rfl | h2
    · rwa [Equiv.swap_apply_right]
    · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- Counting inside `S` is unaffected by precomposing the condition with a swap of two of its
members. -/
private lemma card_filter_comp_swap {S : Finset α} {i i' : α} (hi : i ∈ S) (hi' : i' ∈ S)
    (P : α → Prop) [DecidablePred P] :
    #(S.filter fun j => P (Equiv.swap i i' j)) = #(S.filter P) := by
  classical
  refine Finset.card_bij' (fun j _ => Equiv.swap i i' j) (fun j _ => Equiv.swap i i' j)
    ?_ ?_ ?_ ?_
  · intro j hj
    rw [mem_filter] at hj ⊢
    exact ⟨swap_mem_of_mem hi hi' hj.1, hj.2⟩
  · intro j hj
    rw [mem_filter] at hj ⊢
    refine ⟨swap_mem_of_mem hi hi' hj.1, ?_⟩
    rw [Equiv.swap_apply_self]
    exact hj.2
  · intro j _
    exact Equiv.swap_apply_self i i' j
  · intro j _
    exact Equiv.swap_apply_self i i' j

/-- The ranks are equidistributed across the members of `S`: right-multiplying by
`Equiv.swap i i'` exchanges the roles of `i` and `i'` and preserves `S`. -/
theorem card_filter_tauRank_congr {S : Finset α} {i i' : α} (hi : i ∈ S) (hi' : i' ∈ S)
    (k : ℕ) :
    #((univ : Finset (Equiv.Perm α)).filter fun τ => tauRank S τ i = k)
      = #((univ : Finset (Equiv.Perm α)).filter fun τ => tauRank S τ i' = k) := by
  classical
  have hswap : ∀ a b : α, a ∈ S → b ∈ S → ∀ τ : Equiv.Perm α,
      tauRank S (τ * Equiv.swap a b) b = tauRank S τ a := by
    intro a b ha hb τ
    rw [tauRank, tauRank]
    have hval : (τ * Equiv.swap a b) b = τ a := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    simp only [hval, Equiv.Perm.mul_apply]
    exact card_filter_comp_swap ha hb (fun j => τ a ≤ τ j)
  refine Finset.card_bij' (fun τ _ => τ * Equiv.swap i i') (fun τ _ => τ * Equiv.swap i i')
    ?_ ?_ ?_ ?_
  · intro τ hτ
    rw [mem_filter] at hτ ⊢
    exact ⟨mem_univ _, (hswap i i' hi hi' τ).trans hτ.2⟩
  · intro τ hτ
    rw [mem_filter] at hτ ⊢
    refine ⟨mem_univ _, ?_⟩
    have h := hswap i' i hi' hi τ
    rw [Equiv.swap_comm i' i] at h
    exact h.trans hτ.2
  · intro τ _
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  · intro τ _
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]

/-! ### The rank is uniform -/

/-- Double counting: `#S` classes of equal size, one for each member of `S`, partition the
permutations. -/
theorem card_mul_card_filter_tauRank {S : Finset α} {i : α} (hi : i ∈ S) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ #S) :
    #S * #((univ : Finset (Equiv.Perm α)).filter fun τ => tauRank S τ i = k)
      = Fintype.card (Equiv.Perm α) := by
  classical
  calc #S * #((univ : Finset (Equiv.Perm α)).filter fun τ => tauRank S τ i = k)
      = ∑ _i' ∈ S, #((univ : Finset (Equiv.Perm α)).filter fun τ => tauRank S τ i = k) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = ∑ i' ∈ S, #((univ : Finset (Equiv.Perm α)).filter fun τ => tauRank S τ i' = k) :=
        Finset.sum_congr rfl fun i' hi' => (card_filter_tauRank_congr hi' hi k).symm
    _ = ∑ τ : Equiv.Perm α, #(S.filter fun i' => tauRank S τ i' = k) := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
    _ = Fintype.card (Equiv.Perm α) := by
        rw [Finset.sum_congr rfl fun τ _ => card_filter_tauRank_eq_one S τ hk1 hk,
          Finset.sum_const, card_univ, smul_eq_mul, mul_one]

/-- **The rank of a member of `S` under a uniformly random order is uniform on `{1, …, #S}`.**
This is the notes' "(Why?)" step in the proof of Brégman–Minc: revealing the rows in a random
order leaves each row a uniformly random number of available choices. -/
theorem wprob_tauRank_eq {S : Finset α} {i : α} (hi : i ∈ S) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ #S) :
    wprob (unifPerm α) ((univ : Finset (Equiv.Perm α)).filter fun τ => tauRank S τ i = k)
      = 1 / #S := by
  have hSpos : (0 : ℝ) < #S := by
    have : 0 < #S := lt_of_lt_of_le hk1 hk
    exact_mod_cast this
  have hPpos : (0 : ℝ) < Fintype.card (Equiv.Perm α) := by
    exact_mod_cast card_perm_pos (α := α)
  have hcount : (#S : ℝ)
      * #((univ : Finset (Equiv.Perm α)).filter fun τ => tauRank S τ i = k)
      = Fintype.card (Equiv.Perm α) := by
    exact_mod_cast card_mul_card_filter_tauRank hi hk1 hk
  have hcne : (#((univ : Finset (Equiv.Perm α)).filter fun τ => tauRank S τ i = k) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcount
    exact absurd hcount.symm (ne_of_gt hPpos)
  rw [wprob_unifPerm, ← hcount, mul_comm, ← div_div, div_self hcne]

/-- The expectation of any function of the rank: an average over `{1, …, #S}`. -/
theorem wmean_comp_tauRank {S : Finset α} {i : α} (hi : i ∈ S) (f : ℕ → ℝ) :
    wmean (unifPerm α) (fun τ => f (tauRank S τ i))
      = (∑ k ∈ Finset.Icc 1 #S, f k) / #S := by
  classical
  have hSpos : (0 : ℝ) < #S := by
    have : 0 < #S := Finset.card_pos.mpr ⟨i, hi⟩
    exact_mod_cast this
  have hPpos : (0 : ℝ) < Fintype.card (Equiv.Perm α) := by
    exact_mod_cast card_perm_pos (α := α)
  have hmaps : ∀ τ ∈ (univ : Finset (Equiv.Perm α)), tauRank S τ i ∈ Finset.Icc 1 #S :=
    fun τ _ => Finset.mem_Icc.mpr ⟨tauRank_pos hi τ, tauRank_le_card S τ i⟩
  -- the raw sum, grouped by the rank
  have key : ∑ τ : Equiv.Perm α, f (tauRank S τ i)
      = (Fintype.card (Equiv.Perm α) / (#S : ℝ)) * ∑ k ∈ Finset.Icc 1 #S, f k := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun τ => f (tauRank S τ i)), Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hcount : (#S : ℝ)
        * #((univ : Finset (Equiv.Perm α)).filter fun τ => tauRank S τ i = k)
        = Fintype.card (Equiv.Perm α) := by
      exact_mod_cast card_mul_card_filter_tauRank hi hk1 hk2
    have hpt : ∀ τ ∈ (univ : Finset (Equiv.Perm α)).filter (fun τ => tauRank S τ i = k),
        f (tauRank S τ i) = f k := by
      intro τ hτ
      rw [(mem_filter.mp hτ).2]
    have hcard : (#((univ : Finset (Equiv.Perm α)).filter fun τ => tauRank S τ i = k) : ℝ)
        = Fintype.card (Equiv.Perm α) / (#S : ℝ) := by
      rw [eq_div_iff (ne_of_gt hSpos), mul_comm]
      exact hcount
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, hcard]
  have hunif : ∀ τ : Equiv.Perm α, unifPerm α τ * f (tauRank S τ i)
      = (1 / (Fintype.card (Equiv.Perm α) : ℝ)) * f (tauRank S τ i) :=
    fun τ => by rw [unifPerm_apply]
  rw [wmean, Finset.sum_congr rfl fun τ _ => hunif τ, ← Finset.mul_sum, key]
  field_simp

/-- `∏ k ∈ Icc 1 n, k = n !`, over the reals. -/
private lemma prod_Icc_one_cast (n : ℕ) :
    ∏ k ∈ Finset.Icc 1 n, (k : ℝ) = Nat.factorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
      push_cast
      ring

/-- **The expected log of the rank is `log (#S !) / #S`**, which is exactly the per-row bound
in Brégman–Minc: averaging `log k` over `k = 1, …, d` gives `log (d!) / d`. -/
theorem wmean_log_tauRank {S : Finset α} {i : α} (hi : i ∈ S) :
    wmean (unifPerm α) (fun τ => Real.log (tauRank S τ i))
      = Real.log (Nat.factorial #S) / #S := by
  rw [wmean_comp_tauRank hi (fun m => Real.log m)]
  congr 1
  rw [← prod_Icc_one_cast #S, Real.log_prod]
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have : (0 : ℝ) < k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith
  exact ne_of_gt this

end RandomOrder

end PMC
