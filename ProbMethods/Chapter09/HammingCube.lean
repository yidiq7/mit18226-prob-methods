import ProbMethods.Chapter05.Chernoff

/-!
# §9.4 — isoperimetry in the Hamming cube

The cube is `Finset (Fin n)` — a point of `{0,1}ⁿ` is the set of coordinates where it is `1`,
the same encoding Chapter 5 uses — and `PMC.hamDist` is the number of coordinates where two
points differ.

Two of the section's three ingredients are proved here:

* `PMC.cubeNbhd_lowBall` — **the `t`-neighbourhood of a Hamming ball is a Hamming ball**, with
  the radius grown by exactly `t`. This is the fact Theorem 9.4.5's proof uses to evaluate
  `|Bₜ|`, and it holds exactly, not approximately.
* `PMC.card_lowBall_ge` — the Chernoff estimate `|{x : |x| < n/2 + t}| ≥ (1 - e^{-2t²/n})2ⁿ`.
  This needs nothing new: Chapter 5's `PMC.card_filter_sign_sum_le` at `λ = 2t/√n` gives
  `exp(-λ²/2) = exp(-2t²/n)` on the nose.

The third is Harper's inequality (Theorem 9.4.3), that a Hamming ball minimises the
neighbourhood among sets of its size. The notes state it without proof, and it is genuinely
the hard input — a compression argument — so it is published as a task rather than assumed
silently. Theorem 9.4.5 is stated here **with Harper's conclusion as an explicit hypothesis**
(`PMC.card_cubeNbhd_ge_of_harper`), which keeps the derivation honest and `sorry`-free: the
part that follows from the two lemmas above is proved outright, and what is missing is
visible in the statement.
-/

open Finset

namespace PMC

section HammingCube

variable {n : ℕ}

/-- The Hamming distance: the number of coordinates where `S` and `T` differ. -/
def hamDist (S T : Finset (Fin n)) : ℕ := #(S \ T) + #(T \ S)

/-- The `t`-neighbourhood of a set of points of the cube. -/
def cubeNbhd (t : ℕ) (A : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (univ : Finset (Finset (Fin n))).filter fun T => ∃ S ∈ A, hamDist S T ≤ t

/-- The Hamming ball of radius `k` about the empty set: the points of weight less than `k`. -/
def lowBall (n k : ℕ) : Finset (Finset (Fin n)) :=
  (univ : Finset (Finset (Fin n))).filter fun T => #T < k

lemma mem_cubeNbhd {t : ℕ} {A : Finset (Finset (Fin n))} {T : Finset (Fin n)} :
    T ∈ cubeNbhd t A ↔ ∃ S ∈ A, hamDist S T ≤ t := by
  rw [cubeNbhd, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

lemma mem_lowBall {k : ℕ} {T : Finset (Fin n)} : T ∈ lowBall n k ↔ #T < k := by
  rw [lowBall, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- Moving `t` steps changes the weight by at most `t`. -/
lemma card_le_card_add_hamDist (S T : Finset (Fin n)) : #T ≤ #S + hamDist S T := by
  classical
  have hsplit : #(T \ S) + #(T ∩ S) = #T := Finset.card_sdiff_add_card_inter T S
  rw [hamDist]
  have h1 : #(T ∩ S) ≤ #S := Finset.card_le_card Finset.inter_subset_right
  omega

/-- **The `t`-neighbourhood of a Hamming ball is the ball of radius `t` larger.** Exactly:
the weight can grow by at most `t`, and any point of weight below `k + t` is reached from a
subset of itself of weight below `k`.

`1 ≤ k` is needed: the ball of radius `0` is empty, and the empty set expands to nothing. -/
theorem cubeNbhd_lowBall (t : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    cubeNbhd t (lowBall n k) = lowBall n (k + t) := by
  classical
  ext T
  rw [mem_cubeNbhd, mem_lowBall]
  constructor
  · rintro ⟨S, hS, hd⟩
    rw [mem_lowBall] at hS
    have := card_le_card_add_hamDist S T
    omega
  · intro hT
    by_cases hsmall : #T < k
    · exact ⟨T, mem_lowBall.mpr hsmall, by rw [hamDist]; simp⟩
    · -- trim `T` down to weight `k - 1`
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := T) (n := k - 1)
        (by omega)
      refine ⟨S, mem_lowBall.mpr (by omega), ?_⟩
      have hdiff : #(T \ S) = #T - #S := Finset.card_sdiff_of_subset hSsub
      have hempty : #(S \ T) = 0 := by
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
        exact hSsub
      rw [hamDist, hempty, hdiff, hScard]
      omega

/-! ### The Chernoff estimate for a ball -/

/-- **At least `(1 - e^{-2t²/n})2ⁿ` points of the cube have weight below `n/2 + t`.**

Chapter 5's Chernoff bound at `λ = 2t/√n`, where `exp(-λ²/2) = exp(-2t²/n)` exactly — the
constant in Theorem 9.4.5 is the Chernoff constant, with nothing lost. -/
theorem card_lowBall_ge (hn : 0 < n) {t : ℝ} (ht : 0 < t) {k : ℕ}
    (hk : (n : ℝ) / 2 + t ≤ k) :
    (2 : ℝ) ^ n * (1 - Real.exp (-(2 * t ^ 2) / n)) ≤ #(lowBall n k) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hcardA : #(univ : Finset (Fin n)) = n := by rw [card_univ, Fintype.card_fin]
  set lam : ℝ := 2 * t / Real.sqrt n with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hlamsq : lam * Real.sqrt (n : ℝ) = 2 * t := by
    rw [hlamdef, div_mul_cancel₀]
    exact ne_of_gt hsq
  have hexp : Real.exp (-(lam ^ 2) / 2) = Real.exp (-(2 * t ^ 2) / n) := by
    congr 1
    rw [hlamdef, div_pow, Real.sq_sqrt (le_of_lt hnR)]
    field_simp
  have hchern := card_filter_sign_sum_le (univ : Finset (Fin n)) (by rw [hcardA]; exact hn) hlam
  rw [hcardA, hlamsq, hexp, Finset.powerset_univ] at hchern
  -- everything below the threshold lies in the ball
  set B : Finset (Finset (Fin n)) :=
    (univ : Finset (Finset (Fin n))).filter fun T => 2 * t ≤ 2 * (#T : ℝ) - n with hBdef
  have hsub : (univ : Finset (Finset (Fin n))) \ B ⊆ lowBall n k := by
    intro T hT
    rw [Finset.mem_sdiff, hBdef, mem_filter] at hT
    rw [mem_lowBall]
    have hnot : ¬ (2 * t ≤ 2 * (#T : ℝ) - n) := fun hcon => hT.2 ⟨mem_univ _, hcon⟩
    have hlt : (#T : ℝ) < k := by
      push_neg at hnot
      linarith
    exact_mod_cast hlt
  have hcardcube : #(univ : Finset (Finset (Fin n))) = 2 ^ n := by
    rw [card_univ, Fintype.card_finset, Fintype.card_fin]
  have hBle : (#B : ℝ) ≤ 2 ^ n * Real.exp (-(2 * t ^ 2) / n) := hchern
  have hBsub : B ⊆ (univ : Finset (Finset (Fin n))) := Finset.subset_univ _
  have hcount : (2 : ℝ) ^ n - #B ≤ #((univ : Finset (Finset (Fin n))) \ B) := by
    rw [Finset.card_sdiff_of_subset hBsub, Nat.cast_sub (Finset.card_le_card hBsub), hcardcube]
    push_cast
    linarith
  calc (2 : ℝ) ^ n * (1 - Real.exp (-(2 * t ^ 2) / n))
      = (2 : ℝ) ^ n - 2 ^ n * Real.exp (-(2 * t ^ 2) / n) := by ring
    _ ≤ (2 : ℝ) ^ n - #B := by linarith
    _ ≤ #((univ : Finset (Finset (Fin n))) \ B) := hcount
    _ ≤ #(lowBall n k) := by exact_mod_cast Finset.card_le_card hsub

/-- **The half-cube ball has at most `2^{n-1}` points**, which is what makes Harper's
inequality applicable to any `A` with `|A| ≥ 2^{n-1}`.

Complementation `T ↦ Tᶜ` is injective and maps the ball into its own complement, so twice
the ball's size is at most `2ⁿ`. -/
theorem card_lowBall_half_le (hn : 0 < n) :
    2 * #(lowBall n ((n + 1) / 2)) ≤ 2 ^ n := by
  classical
  have hcardcube : #(univ : Finset (Finset (Fin n))) = 2 ^ n := by
    rw [card_univ, Fintype.card_finset, Fintype.card_fin]
  have himg : (lowBall n ((n + 1) / 2)).image (fun T => (univ : Finset (Fin n)) \ T)
      ⊆ (univ : Finset (Finset (Fin n))) \ lowBall n ((n + 1) / 2) := by
    intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨S, hS, rfl⟩ := hT
    rw [mem_lowBall] at hS
    rw [Finset.mem_sdiff, mem_lowBall]
    refine ⟨mem_univ _, ?_⟩
    have hSle : #S ≤ n := by
      have := Finset.card_le_card (Finset.subset_univ S)
      rwa [card_univ, Fintype.card_fin] at this
    have hcompl : #((univ : Finset (Fin n)) \ S) = n - #S := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), card_univ, Fintype.card_fin]
    rw [hcompl]
    omega
  have hinj : Set.InjOn (fun T => (univ : Finset (Fin n)) \ T) (lowBall n ((n + 1) / 2)) := by
    intro S hS S' hS' h
    calc S = (univ : Finset (Fin n)) \ ((univ : Finset (Fin n)) \ S) :=
          (Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)).symm
      _ = (univ : Finset (Fin n)) \ ((univ : Finset (Fin n)) \ S') := by
          rw [show (univ : Finset (Fin n)) \ S = (univ : Finset (Fin n)) \ S' from h]
      _ = S' := Finset.sdiff_sdiff_eq_self (Finset.subset_univ S')
  have hcard : #(lowBall n ((n + 1) / 2))
      ≤ #((univ : Finset (Finset (Fin n))) \ lowBall n ((n + 1) / 2)) := by
    calc #(lowBall n ((n + 1) / 2))
        = #((lowBall n ((n + 1) / 2)).image (fun T => (univ : Finset (Fin n)) \ T)) :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ _ := Finset.card_le_card himg
  have hsub : lowBall n ((n + 1) / 2) ⊆ (univ : Finset (Finset (Fin n))) := Finset.subset_univ _
  rw [Finset.card_sdiff_of_subset hsub, hcardcube] at hcard
  have hle : #(lowBall n ((n + 1) / 2)) ≤ 2 ^ n := by
    rw [← hcardcube]
    exact Finset.card_le_card hsub
  omega

/-! ### Harper's inequality, and Theorem 9.4.5 -/

/-- **Harper's isoperimetric inequality in the Hamming cube** (Theorem 9.4.3): among sets of
a given size, a Hamming ball has the smallest `t`-neighbourhood.

Balls centred at `∅` suffice: translation by any point of the cube is an isometry, so a ball
about any centre has a neighbourhood of the same size as the corresponding ball about `∅`.

The notes state this without proof — it is the hard input of §9.4, proved by a compression
argument — so it is published as a task rather than assumed silently. -/
theorem card_cubeNbhd_lowBall_le (t k : ℕ) (A : Finset (Finset (Fin n)))
    (hA : #(lowBall n k) ≤ #A) :
    #(cubeNbhd t (lowBall n k)) ≤ #(cubeNbhd t A) := by
  sorry

/-- **Theorem 9.4.5 (rapid expansion from half), conditional on Harper's inequality.**

If `|A| ≥ 2^{n-1}` then `|Aₜ| ≥ (1 - e^{-2t²/n})2ⁿ`: starting from half the cube and expanding
by `t` covers all but an `e^{-2t²/n}` fraction.

Harper's conclusion for the half-cube ball is taken as an explicit hypothesis, so that what is
proved here is exactly the part that follows from `PMC.cubeNbhd_lowBall` and
`PMC.card_lowBall_ge` — and what is missing is visible in the statement rather than hidden in
a `sorry`. -/
theorem card_cubeNbhd_ge_of_harper (hn : 0 < n) {t : ℕ} (ht : 0 < t)
    (A : Finset (Finset (Fin n))) (hA : 2 ^ (n - 1) ≤ #A)
    (harper : #(cubeNbhd t (lowBall n ((n + 1) / 2))) ≤ #(cubeNbhd t A)) :
    (2 : ℝ) ^ n * (1 - Real.exp (-(2 * (t : ℝ) ^ 2) / n)) ≤ #(cubeNbhd t A) := by
  have hk : 1 ≤ (n + 1) / 2 := by omega
  have hball : cubeNbhd t (lowBall n ((n + 1) / 2)) = lowBall n ((n + 1) / 2 + t) :=
    cubeNbhd_lowBall t hk
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hkge : (n : ℝ) / 2 + t ≤ ((n + 1) / 2 + t : ℕ) := by
    have h2 : (n : ℝ) / 2 ≤ (((n + 1) / 2 : ℕ) : ℝ) := by
      rcases Nat.even_or_odd n with he | ho
      · obtain ⟨j, hj⟩ := he
        have hj' : (n + 1) / 2 = j := by omega
        rw [hj']
        rw [hj]
        push_cast
        linarith
      · obtain ⟨j, hj⟩ := ho
        have hj' : (n + 1) / 2 = j + 1 := by omega
        rw [hj']
        rw [hj]
        push_cast
        linarith
    push_cast
    linarith
  calc (2 : ℝ) ^ n * (1 - Real.exp (-(2 * (t : ℝ) ^ 2) / n))
      ≤ #(lowBall n ((n + 1) / 2 + t)) := card_lowBall_ge hn htR hkge
    _ = #(cubeNbhd t (lowBall n ((n + 1) / 2))) := by rw [hball]
    _ ≤ #(cubeNbhd t A) := by exact_mod_cast harper


end HammingCube

end PMC
