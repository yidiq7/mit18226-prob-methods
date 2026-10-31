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

/-! ### Proof of Harper's inequality

The proof is by induction on the dimension, carried by a numerical profile rather than by
compressions. `HarperNum.psi n` is the piecewise-linear function through the points
`(|B_k|, |B_{k+1}|)`, where `B_k = lowBall n k`; it is written as the minimum of its pieces,
so it is concave and monotone for free.

* `HarperCube.psi_le_card_cubeNbhd_one`: every nonempty `A` has `psi n |A| ≤ |N₁(A)|`.
  Splitting the cube on the last coordinate into halves `A₀, A₁` gives
  `|N₁(A)| ≥ max(|N₁(A₀)|, |A₁|) + max(|N₁(A₁)|, |A₀|)`, and
  `HarperNum.psi_succ_le` shows the induction hypothesis on the halves bounds this below by
  `psi (n+1) |A|`. That numerical step uses the intermediate value theorem, the concavity of
  `psi n`, and the identity `psi (n+1) (z + psi n z) = psi n z + psi n (psi n z)`, which is
  Pascal's rule on the ball sizes (`HarperNum.psi_succ_shift`).
* Since `psi n |B_k| ≥ |B_{k+1}|` and `N_{t+1}(A) ⊇ N₁(N_t(A))`, induction on `t` gives
  `|N_t(A)| ≥ |B_{k+t}| = |N_t(B_k)|` whenever `|A| ≥ |B_k|`.
-/

namespace HarperNum

/-- `vol n k = ∑_{i<k} C(n,i)`, the size of the Hamming ball of radius `k` about `∅`. -/
private noncomputable def vol (n k : ℕ) : ℝ := ∑ i ∈ range k, (n.choose i : ℝ)

/-- The line through `(vol n k, vol n (k+1))` and `(vol n (k+1), vol n (k+2))`. -/
private noncomputable def line (n k : ℕ) (x : ℝ) : ℝ :=
  vol n (k + 1) + (x - vol n k) * ((n.choose (k + 1) : ℝ) / n.choose k)

/-- The piecewise-linear interpolation of `vol n k ↦ vol n (k+1)`, as the minimum of its
pieces. -/
private noncomputable def psi (n : ℕ) (x : ℝ) : ℝ :=
  (range (n + 1)).inf' ⟨0, mem_range.2 (Nat.succ_pos n)⟩ fun k => line n k x

private lemma vol_zero (n : ℕ) : vol n 0 = 0 := by simp [vol]

private lemma vol_succ (n k : ℕ) : vol n (k + 1) = vol n k + n.choose k := by
  simp [vol, sum_range_succ]

private lemma vol_one (n : ℕ) : vol n 1 = 1 := by simp [vol]

private lemma vol_top (n : ℕ) : vol n (n + 1) = 2 ^ n := by
  rw [vol]
  exact_mod_cast Nat.sum_range_choose n

private lemma vol_mono (n : ℕ) {k m : ℕ} (h : k ≤ m) : vol n k ≤ vol n m := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => rw [vol_succ]; have : (0 : ℝ) ≤ n.choose m := by positivity
                   linarith

private lemma vol_pascal (n k : ℕ) : vol (n + 1) (k + 1) = vol n (k + 1) + vol n k := by
  induction k with
  | zero => simp [vol]
  | succ k ih =>
    rw [vol_succ, ih, vol_succ n (k + 1), vol_succ n k, Nat.choose_succ_succ]
    push_cast
    ring

private lemma choose_pos_real {n k : ℕ} (h : k ≤ n) : (0 : ℝ) < n.choose k := by
  exact_mod_cast Nat.choose_pos h

/-- The ratio `C(n,m+1)/C(n,m)` is non-increasing in `m`. -/
private lemma choose_ratio_anti (n : ℕ) {l m : ℕ} (h : l ≤ m) :
    ((n.choose (m + 1) : ℝ) * n.choose l) ≤ n.choose m * n.choose (l + 1) := by
  have h1 := Nat.choose_succ_right_eq n m
  have h2 := Nat.choose_succ_right_eq n l
  have key : (n.choose (m + 1) * n.choose l) * ((m + 1) * (l + 1))
      ≤ (n.choose m * n.choose (l + 1)) * ((m + 1) * (l + 1)) := by
    have e1 : (n.choose (m + 1) * n.choose l) * ((m + 1) * (l + 1))
        = (n.choose m * n.choose l) * ((n - m) * (l + 1)) := by
      calc _ = (n.choose (m + 1) * (m + 1)) * n.choose l * (l + 1) := by ring
        _ = (n.choose m * (n - m)) * n.choose l * (l + 1) := by rw [h1]
        _ = _ := by ring
    have e2 : (n.choose m * n.choose (l + 1)) * ((m + 1) * (l + 1))
        = (n.choose m * n.choose l) * ((n - l) * (m + 1)) := by
      calc _ = n.choose m * (n.choose (l + 1) * (l + 1)) * (m + 1) := by ring
        _ = n.choose m * (n.choose l * (n - l)) * (m + 1) := by rw [h2]
        _ = _ := by ring
    rw [e1, e2]
    apply Nat.mul_le_mul_left
    rcases le_or_gt m n with hm | hm
    · have hl : l ≤ n := h.trans hm
      zify [hm, hl]
      nlinarith
    · rw [Nat.sub_eq_zero_of_le hm.le]
      simp
  have hpos : 0 < (m + 1) * (l + 1) := by positivity
  exact_mod_cast Nat.le_of_mul_le_mul_right key hpos

private lemma line_vol_self (n k : ℕ) : line n k (vol n k) = vol n (k + 1) := by
  simp [line]

private lemma line_vol_succ {n k : ℕ} (hk : k ≤ n) : line n k (vol n (k + 1)) = vol n (k + 2) := by
  have hc := choose_pos_real hk
  rw [line, vol_succ n (k + 1), vol_succ n k]
  field_simp
  ring

private lemma line_mono (n k : ℕ) {x y : ℝ} (h : x ≤ y) : line n k x ≤ line n k y := by
  unfold line
  have : (0 : ℝ) ≤ (n.choose (k + 1) : ℝ) / n.choose k := by positivity
  nlinarith

/-- An affine function nonnegative at both ends of an interval is nonnegative on it. -/
private lemma affine_nonneg {p q u v x : ℝ} (hu : 0 ≤ p + q * u) (hv : 0 ≤ p + q * v)
    (h1 : u ≤ x) (h2 : x ≤ v) : 0 ≤ p + q * x := by
  rcases eq_or_lt_of_le (h1.trans h2) with huv | huv
  · have : x = u := by linarith
    rw [this]; exact hu
  · by_contra hneg
    rw [not_le] at hneg
    have e : (v - u) * (p + q * x) = (v - x) * (p + q * u) + (x - u) * (p + q * v) := by ring
    have : (v - u) * (p + q * x) < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
    nlinarith [mul_nonneg (sub_nonneg.2 h2) hu, mul_nonneg (sub_nonneg.2 h1) hv]

/-- Each line lies above every ball value: `vol n (m+1) ≤ line n i (vol n m)`. -/
private lemma vol_succ_le_line {n i : ℕ} (hi : i ≤ n) (m : ℕ) : vol n (m + 1) ≤ line n i (vol n m) := by
  have hc := choose_pos_real hi
  set s : ℝ := (n.choose (i + 1) : ℝ) / n.choose i with hs
  have hD : ∀ m, line n i (vol n (m + 1)) - vol n (m + 2)
      = (line n i (vol n m) - vol n (m + 1)) + (s * n.choose m - n.choose (m + 1)) := by
    intro m
    simp only [line, vol_succ]
    rw [← hs]
    ring
  -- upward from `i`
  have hup : ∀ d, 0 ≤ line n i (vol n (i + d)) - vol n (i + d + 1) := by
    intro d
    induction d with
    | zero => rw [add_zero, line_vol_self, sub_self]
    | succ d ih =>
      have hr := choose_ratio_anti n (Nat.le_add_right i d)
      have : (n.choose (i + d + 1) : ℝ) ≤ s * n.choose (i + d) := by
        rw [hs, div_mul_eq_mul_div, le_div_iff₀ hc]
        linarith
      have := hD (i + d)
      rw [show i + (d + 1) = i + d + 1 by ring, show i + d + 1 + 1 = i + d + 2 by ring]
      linarith
  -- downward from `i`
  have hdown : ∀ d, ∀ m, m + d = i → 0 ≤ line n i (vol n m) - vol n (m + 1) := by
    intro d
    induction d with
    | zero =>
      intro m hm
      rw [add_zero] at hm
      subst hm
      rw [line_vol_self, sub_self]
    | succ d ih =>
      intro m hm
      have h' := ih (m + 1) (by omega)
      have hr := choose_ratio_anti n (show m ≤ i by omega)
      have : s * n.choose m ≤ (n.choose (m + 1) : ℝ) := by
        rw [hs, div_mul_eq_mul_div, div_le_iff₀ hc]
        linarith
      have := hD m
      linarith
  rcases le_total i m with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    linarith [hup d]
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
    linarith [hdown d m hd.symm]

private lemma psi_le_line {n k : ℕ} (hk : k ≤ n) (x : ℝ) : psi n x ≤ line n k x :=
  inf'_le _ (mem_range.2 (Nat.lt_succ_of_le hk))

private lemma psi_vol (n m : ℕ) : vol n (m + 1) ≤ psi n (vol n m) :=
  le_inf' _ _ fun _ hi => vol_succ_le_line (Nat.lt_succ_iff.1 (mem_range.1 hi)) m

private lemma psi_mono (n : ℕ) : Monotone (psi n) := fun _ _ h =>
  le_inf' _ _ fun i hi => (inf'_le _ hi).trans (line_mono n i h)

private lemma psi_zero_le (n : ℕ) : psi n 0 ≤ 1 := by
  have := psi_le_line (Nat.zero_le n) 0
  simpa [line, vol_one, vol_zero] using this

private lemma psi_eq_line {n j : ℕ} (hj : j ≤ n) {x : ℝ} (h1 : vol n j ≤ x) (h2 : x ≤ vol n (j + 1)) :
    psi n x = line n j x := by
  refine le_antisymm (psi_le_line hj x) (le_inf' _ _ fun i hi => ?_)
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
  have hci := choose_pos_real hi'
  have hcj := choose_pos_real hj
  have e : ∀ y, line n i y - line n j y
      = (vol n (i + 1) - vol n i * (n.choose (i + 1) / n.choose i)
          - (vol n (j + 1) - vol n j * (n.choose (j + 1) / n.choose j)))
        + ((n.choose (i + 1) / n.choose i) - (n.choose (j + 1) / n.choose j)) * y := by
    intro y; simp only [line]; ring
  have hu := vol_succ_le_line hi' j
  have hv := vol_succ_le_line hi' (j + 1)
  have hu' : 0 ≤ line n i (vol n j) - line n j (vol n j) := by
    rw [line_vol_self]; linarith
  have hv' : 0 ≤ line n i (vol n (j + 1)) - line n j (vol n (j + 1)) := by
    rw [line_vol_succ hj]; linarith
  rw [e] at hu' hv'
  have := affine_nonneg hu' hv' h1 h2
  rw [← e] at this
  linarith

/-- Every point of `[0, 2^n]` lies on some piece. -/
private lemma exists_piece (n : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 2 ^ n) :
    ∃ j ≤ n, vol n j ≤ x ∧ x ≤ vol n (j + 1) := by
  classical
  let P : ℕ → Prop := fun j => vol n j ≤ x
  have hP0 : P 0 := by simp only [P, vol_zero]; exact h0
  refine ⟨Nat.findGreatest P n, Nat.findGreatest_le n,
    Nat.findGreatest_spec (P := P) (Nat.zero_le n) hP0, ?_⟩
  rcases lt_or_eq_of_le (Nat.findGreatest_le (P := P) n) with hlt | heq
  · have := Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self _) hlt
    simp only [P, not_le] at this
    exact this.le
  · rw [heq, vol_top]; exact h1

private lemma le_psi (n : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 2 ^ n) : x ≤ psi n x := by
  obtain ⟨j, hj, hx1, hx2⟩ := exists_piece n h0 h1
  rw [psi_eq_line hj hx1 hx2]
  have e : ∀ y, line n j y - y = (vol n (j + 1) - vol n j * (n.choose (j + 1) / n.choose j))
      + ((n.choose (j + 1) / n.choose j) - 1) * y := by
    intro y; simp only [line]; ring
  have hu : 0 ≤ line n j (vol n j) - vol n j := by
    rw [line_vol_self]; linarith [vol_mono n (Nat.le_succ j)]
  have hv : 0 ≤ line n j (vol n (j + 1)) - vol n (j + 1) := by
    rw [line_vol_succ hj]; linarith [vol_mono n (Nat.le_succ (j + 1))]
  rw [e] at hu hv
  have := affine_nonneg hu hv hx1 hx2
  rw [← e] at this
  linarith

/-- Concavity of `psi`, in the form used below. -/
private lemma psi_concave (n : ℕ) {a b U W : ℝ} (hWb : W ≤ b) (hba : b ≤ a) (haU : a ≤ U)
    (hsum : a + b = U + W) : psi n U + psi n W ≤ psi n a + psi n b := by
  -- each line is affine, so `(U - W) f(y) = (y - W) f(U) + (U - y) f(W)`
  have key : ∀ y, W ≤ y → y ≤ U →
      (y - W) * psi n U + (U - y) * psi n W ≤ (U - W) * psi n y := by
    intro y h1 h2
    obtain ⟨i, hi, hiy⟩ := exists_mem_eq_inf' (s := range (n + 1))
      ⟨0, mem_range.2 (Nat.succ_pos n)⟩ (fun k => line n k y)
    have hy : psi n y = line n i y := hiy
    have hU : psi n U ≤ line n i U := inf'_le _ hi
    have hW : psi n W ≤ line n i W := inf'_le _ hi
    have e : (U - W) * line n i y = (y - W) * line n i U + (U - y) * line n i W := by
      simp only [line]; ring
    rw [hy, e]
    have := mul_le_mul_of_nonneg_left hU (sub_nonneg.2 h1)
    have := mul_le_mul_of_nonneg_left hW (sub_nonneg.2 h2)
    linarith
  rcases eq_or_lt_of_le (hWb.trans (hba.trans haU)) with hUW | hUW
  · have ha : a = U := by linarith
    have hb : b = W := by linarith
    rw [ha, hb]
  · have h1 := key a (by linarith) haU
    have h2 := key b hWb (by linarith)
    have hb' : b = U + W - a := by linarith
    have : (U - W) * (psi n U + psi n W) ≤ (U - W) * (psi n a + psi n b) := by
      calc (U - W) * (psi n U + psi n W)
          = (a - W) * psi n U + (U - a) * psi n W
            + ((b - W) * psi n U + (U - b) * psi n W) := by rw [hb']; ring
        _ ≤ (U - W) * psi n a + (U - W) * psi n b := add_le_add h1 h2
        _ = (U - W) * (psi n a + psi n b) := by ring
    exact le_of_mul_le_mul_left this (by linarith)

private lemma psi_continuous (n : ℕ) : Continuous (psi n) := by
  unfold psi
  apply Continuous.finset_inf'_apply
  intro k _
  unfold line
  fun_prop

/-- Shifting the radius by one: `psi (n+1) (z + psi n z) ≤ psi n z + psi n (psi n z)`. -/
private lemma psi_succ_shift (n : ℕ) {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 2 ^ n) :
    psi (n + 1) (z + psi n z) ≤ psi n z + psi n (psi n z) := by
  obtain ⟨j, hj, hz1, hz2⟩ := exists_piece n h0 h1
  rw [psi_eq_line hj hz1 hz2]
  rcases lt_or_eq_of_le hj with hjn | rfl
  · -- `line n j z` lies on piece `j + 1`
    have hw1 : vol n (j + 1) ≤ line n j z := by
      rw [← line_vol_self]; exact line_mono n j hz1
    have hw2 : line n j z ≤ vol n (j + 1 + 1) := by
      rw [← line_vol_succ hj]; exact line_mono n j hz2
    rw [psi_eq_line hjn hw1 hw2]
    refine (psi_le_line (show j + 1 ≤ n + 1 by omega) _).trans (le_of_eq ?_)
    have hc0 := choose_pos_real hj
    have hc1 := choose_pos_real hjn
    simp only [line]
    rw [vol_pascal n (j + 1), vol_pascal n j, Nat.choose_succ_succ n (j + 1),
      Nat.choose_succ_succ n j]
    push_cast
    rw [vol_succ n (j + 1), vol_succ n j]
    field_simp
    ring
  · have hw : line j j z = 2 ^ j := by
      simp [line, vol_top]
    rw [hw]
    have h2 := le_psi j (by positivity) (le_refl ((2 : ℝ) ^ j))
    refine (psi_le_line (le_refl (j + 1)) _).trans ?_
    simp only [line, Nat.choose_succ_self, Nat.cast_zero, zero_div, mul_zero, add_zero]
    rw [vol_top, pow_succ]
    linarith

/-- The numerical heart of the induction step. -/
private lemma psi_succ_le (n : ℕ) {a b : ℝ} (hba : b ≤ a) (ha1 : 1 ≤ a)
    (ha : a ≤ 2 ^ n) : psi (n + 1) (a + b) ≤ psi n a + max a (psi n b) := by
  have hcont := psi_continuous n
  -- a point `y ∈ [0, a]` with `psi n y = a`
  obtain ⟨y, ⟨hy0, hya⟩, hy⟩ : ∃ y ∈ Set.Icc 0 a, psi n y = a := by
    have := intermediate_value_Icc (show (0 : ℝ) ≤ a by linarith) hcont.continuousOn
    exact this ⟨(psi_zero_le n).trans ha1, le_psi n (by linarith) ha⟩
  have hy2 : y ≤ 2 ^ n := hya.trans ha
  rcases le_or_gt b y with hby | hyb
  · calc psi (n + 1) (a + b) ≤ psi (n + 1) (y + psi n y) := by
          rw [hy]; exact psi_mono _ (by linarith)
      _ ≤ psi n y + psi n (psi n y) := psi_succ_shift n hy0 hy2
      _ = a + psi n a := by rw [hy]
      _ ≤ psi n a + max a (psi n b) := by linarith [le_max_left a (psi n b)]
  · -- a point `z ∈ [y, b]` with `z + psi n z = a + b`
    have hgc : Continuous fun z => z + psi n z := continuous_id.add hcont
    have hab : a ≤ psi n b := hy ▸ psi_mono n hyb.le
    obtain ⟨z, ⟨hz0, hzb⟩, hz⟩ : ∃ z ∈ Set.Icc y b, z + psi n z = a + b := by
      have := intermediate_value_Icc hyb.le hgc.continuousOn
      exact this ⟨by simp only [hy]; linarith, show a + b ≤ b + psi n b by linarith⟩
    have hzU : a ≤ psi n z := hy ▸ psi_mono n hz0
    have hcv := psi_concave n hzb hba hzU (by linarith)
    calc psi (n + 1) (a + b) = psi (n + 1) (z + psi n z) := by rw [hz]
      _ ≤ psi n z + psi n (psi n z) :=
          psi_succ_shift n (hy0.trans hz0) (hzb.trans (hba.trans ha))
      _ ≤ psi n a + psi n b := by linarith
      _ ≤ psi n a + max a (psi n b) := by linarith [le_max_right a (psi n b)]

end HarperNum

namespace HarperCube

/-- The copy of the `n`-cube inside the `(n+1)`-cube omitting the last coordinate. -/
private def emb (S : Finset (Fin n)) : Finset (Fin (n + 1)) := S.map Fin.castSuccEmb

/-- The restriction of a point of the `(n+1)`-cube to its first `n` coordinates. -/
private def res (T : Finset (Fin (n + 1))) : Finset (Fin n) := univ.filter fun i => i.castSucc ∈ T

/-- The lower half of a set of the `(n+1)`-cube. -/
private def lo (A : Finset (Finset (Fin (n + 1)))) : Finset (Finset (Fin n)) :=
  univ.filter fun S => emb S ∈ A

/-- The upper half of a set of the `(n+1)`-cube. -/
private def hi (A : Finset (Finset (Fin (n + 1)))) : Finset (Finset (Fin n)) :=
  univ.filter fun S => insert (Fin.last n) (emb S) ∈ A

private lemma mem_emb {S : Finset (Fin n)} {x : Fin (n + 1)} :
    x ∈ emb S ↔ ∃ i ∈ S, i.castSucc = x := by
  simp [emb]

private lemma castSucc_mem_emb {S : Finset (Fin n)} {i : Fin n} : i.castSucc ∈ emb S ↔ i ∈ S := by
  simp [emb]

private lemma last_not_mem_emb (S : Finset (Fin n)) : Fin.last n ∉ emb S := by
  simp [emb, Fin.castSucc_ne_last]

private lemma res_emb (S : Finset (Fin n)) : res (emb S) = S := by
  ext i; simp [res, castSucc_mem_emb]

private lemma res_insert_emb (S : Finset (Fin n)) : res (insert (Fin.last n) (emb S)) = S := by
  ext i; simp [res, castSucc_mem_emb, Fin.castSucc_ne_last]

private lemma emb_res {T : Finset (Fin (n + 1))} (h : Fin.last n ∉ T) : emb (res T) = T := by
  ext x
  induction x using Fin.lastCases with
  | last => simp [last_not_mem_emb, h]
  | cast i => simp [castSucc_mem_emb, res]

private lemma insert_emb_res {T : Finset (Fin (n + 1))} (h : Fin.last n ∈ T) :
    insert (Fin.last n) (emb (res T)) = T := by
  ext x
  induction x using Fin.lastCases with
  | last => simp [h]
  | cast i => simp [castSucc_mem_emb, res, Fin.castSucc_ne_last]

private lemma card_lo (A : Finset (Finset (Fin (n + 1)))) :
    #(lo A) = #(A.filter fun T => Fin.last n ∉ T) := by
  refine card_nbij' emb res ?_ ?_ ?_ ?_
  · intro S hS
    simp only [lo, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS
    simp only [coe_filter, Set.mem_ofPred_eq]
    exact ⟨hS, last_not_mem_emb S⟩
  · intro T hT
    simp only [coe_filter, Set.mem_ofPred_eq] at hT
    simp only [lo, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    rw [emb_res hT.2]; exact hT.1
  · intro S _; exact res_emb S
  · intro T hT
    simp only [coe_filter, Set.mem_ofPred_eq] at hT
    exact emb_res hT.2

private lemma card_hi (A : Finset (Finset (Fin (n + 1)))) :
    #(hi A) = #(A.filter fun T => Fin.last n ∈ T) := by
  refine card_nbij' (fun S => insert (Fin.last n) (emb S)) res ?_ ?_ ?_ ?_
  · intro S hS
    simp only [hi, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS
    simp only [coe_filter, Set.mem_ofPred_eq]
    exact ⟨hS, mem_insert_self _ _⟩
  · intro T hT
    simp only [coe_filter, Set.mem_ofPred_eq] at hT
    simp only [hi, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    rw [insert_emb_res hT.2]; exact hT.1
  · intro S _; exact res_insert_emb S
  · intro T hT
    simp only [coe_filter, Set.mem_ofPred_eq] at hT
    exact insert_emb_res hT.2

private lemma card_lo_add_hi (A : Finset (Finset (Fin (n + 1)))) : #(lo A) + #(hi A) = #A := by
  rw [card_lo, card_hi, add_comm]
  exact card_filter_add_card_filter_not _

private lemma hamDist_emb (R S : Finset (Fin n)) : hamDist (emb R) (emb S) = hamDist R S := by
  simp [hamDist, emb, ← map_sdiff]

private lemma emb_sdiff_insert (R S : Finset (Fin n)) :
    insert (Fin.last n) (emb R) \ insert (Fin.last n) (emb S) = emb (R \ S) := by
  ext x
  induction x using Fin.lastCases with
  | last => simp [last_not_mem_emb]
  | cast i => simp [castSucc_mem_emb, Fin.castSucc_ne_last]

private lemma hamDist_insert_emb (R S : Finset (Fin n)) :
    hamDist (insert (Fin.last n) (emb R)) (insert (Fin.last n) (emb S)) = hamDist R S := by
  rw [hamDist, emb_sdiff_insert, emb_sdiff_insert, hamDist, emb, emb, card_map, card_map]

private lemma card_insert_sdiff_le {m : ℕ} (x : Fin m) (T : Finset (Fin m)) : #(insert x T \ T) ≤ 1 := by
  have : insert x T \ T ⊆ {x} := by
    intro y hy
    simp only [mem_sdiff, mem_insert] at hy
    simp only [mem_singleton]
    tauto
  simpa using card_le_card this

private lemma hamDist_self_insert_le {m : ℕ} (x : Fin m) (T : Finset (Fin m)) :
    hamDist T (insert x T) ≤ 1 := by
  have h1 : T \ insert x T = ∅ := sdiff_eq_empty_iff_subset.2 (subset_insert _ _)
  rw [hamDist, h1, card_empty, zero_add]
  exact card_insert_sdiff_le x T

private lemma hamDist_insert_self_le {m : ℕ} (x : Fin m) (T : Finset (Fin m)) :
    hamDist (insert x T) T ≤ 1 := by
  have h1 : T \ insert x T = ∅ := sdiff_eq_empty_iff_subset.2 (subset_insert _ _)
  rw [hamDist, h1, card_empty, add_zero]
  exact card_insert_sdiff_le x T

private lemma hamDist_self {m : ℕ} (T : Finset (Fin m)) : hamDist T T = 0 := by
  simp [hamDist]

private lemma hamDist_le_add {m : ℕ} (R S T : Finset (Fin m)) :
    hamDist R T ≤ hamDist R S + hamDist S T := by
  have h1 : R \ T ⊆ (R \ S) ∪ (S \ T) := by
    intro x; simp only [mem_sdiff, mem_union]; tauto
  have h2 : T \ R ⊆ (T \ S) ∪ (S \ R) := by
    intro x; simp only [mem_sdiff, mem_union]; tauto
  have := (card_le_card h1).trans (card_union_le _ _)
  have := (card_le_card h2).trans (card_union_le _ _)
  simp only [hamDist]
  omega

/-- The lower half of the neighbourhood contains the neighbourhood of the lower half, and the
upper half. -/
private lemma nbhd_lo_union_hi_subset (A : Finset (Finset (Fin (n + 1)))) :
    cubeNbhd 1 (lo A) ∪ hi A ⊆ lo (cubeNbhd 1 A) := by
  intro S hS
  simp only [lo, mem_filter, mem_univ, true_and, mem_union, hi, mem_cubeNbhd] at hS ⊢
  rcases hS with ⟨R, hR, hd⟩ | hS
  · exact ⟨emb R, hR, by rw [hamDist_emb]; exact hd⟩
  · exact ⟨_, hS, hamDist_insert_self_le _ _⟩

private lemma nbhd_hi_union_lo_subset (A : Finset (Finset (Fin (n + 1)))) :
    cubeNbhd 1 (hi A) ∪ lo A ⊆ hi (cubeNbhd 1 A) := by
  intro S hS
  simp only [lo, mem_filter, mem_univ, true_and, mem_union, hi, mem_cubeNbhd] at hS ⊢
  rcases hS with ⟨R, hR, hd⟩ | hS
  · exact ⟨_, hR, by rw [hamDist_insert_emb]; exact hd⟩
  · exact ⟨_, hS, hamDist_self_insert_le _ _⟩

/-- The neighbourhood of `A` is at least as large as the two halves' contributions. -/
private lemma card_nbhd_split (A : Finset (Finset (Fin (n + 1)))) :
    #(cubeNbhd 1 (lo A) ∪ hi A) + #(cubeNbhd 1 (hi A) ∪ lo A) ≤ #(cubeNbhd 1 A) := by
  rw [← card_lo_add_hi (cubeNbhd 1 A)]
  exact add_le_add (card_le_card (nbhd_lo_union_hi_subset A))
    (card_le_card (nbhd_hi_union_lo_subset A))

private lemma subset_cubeNbhd {m : ℕ} (t : ℕ) (A : Finset (Finset (Fin m))) : A ⊆ cubeNbhd t A := by
  intro S hS
  rw [mem_cubeNbhd]
  exact ⟨S, hS, by rw [hamDist_self]; exact Nat.zero_le t⟩

private lemma cubeNbhd_one_cubeNbhd_subset {m : ℕ} (t : ℕ) (A : Finset (Finset (Fin m))) :
    cubeNbhd 1 (cubeNbhd t A) ⊆ cubeNbhd (t + 1) A := by
  intro T hT
  rw [mem_cubeNbhd] at hT ⊢
  obtain ⟨S, hS, hST⟩ := hT
  rw [mem_cubeNbhd] at hS
  obtain ⟨R, hR, hRS⟩ := hS
  exact ⟨R, hR, (hamDist_le_add R S T).trans (by omega)⟩

/-- `#(lowBall n (m+1)) = #(lowBall n m) + C(n,m)`. -/
private lemma card_lowBall_succ (m : ℕ) : #(lowBall n (m + 1)) = #(lowBall n m) + n.choose m := by
  classical
  have h := card_filter_add_card_filter_not (s := lowBall n (m + 1))
    (fun T : Finset (Fin n) => #T = m)
  have e1 : (lowBall n (m + 1)).filter (fun T => #T = m) = powersetCard m univ := by
    ext T; simp only [lowBall, mem_filter, mem_univ, true_and, mem_powersetCard,
      subset_univ]; omega
  have e2 : (lowBall n (m + 1)).filter (fun T => ¬ #T = m) = lowBall n m := by
    ext T; simp only [lowBall, mem_filter, mem_univ, true_and]; omega
  rw [e1, e2, card_powersetCard, card_univ, Fintype.card_fin] at h
  omega

private lemma card_lowBall_eq_vol (m : ℕ) : (#(lowBall n m) : ℝ) = HarperNum.vol n m := by
  induction m with
  | zero =>
    have : lowBall n 0 = ∅ := by ext T; simp [lowBall]
    rw [this, HarperNum.vol_zero, card_empty, Nat.cast_zero]
  | succ m ih => rw [card_lowBall_succ, HarperNum.vol_succ]; push_cast; rw [ih]

private lemma step_aux (ih : ∀ B : Finset (Finset (Fin n)), B.Nonempty →
      HarperNum.psi n #B ≤ #(cubeNbhd 1 B))
    (A0 A1 : Finset (Finset (Fin n))) (hle : #A1 ≤ #A0) (hpos : 1 ≤ #A0 + #A1) :
    HarperNum.psi (n + 1) ((#A0 + #A1 : ℕ) : ℝ)
      ≤ #(cubeNbhd 1 A0 ∪ A1) + #(cubeNbhd 1 A1 ∪ A0) := by
  have ha1 : 1 ≤ #A0 := by omega
  have hA0 : A0.Nonempty := card_pos.1 (by omega)
  have ha2 : (#A0 : ℝ) ≤ 2 ^ n := by
    have := card_le_univ A0
    rw [Fintype.card_finset, Fintype.card_fin] at this
    exact_mod_cast this
  have key := HarperNum.psi_succ_le n (a := #A0) (b := #A1)
    (by exact_mod_cast hle) (by exact_mod_cast ha1) ha2
  have h0 : HarperNum.psi n #A0 ≤ #(cubeNbhd 1 A0 ∪ A1) :=
    (ih A0 hA0).trans (by exact_mod_cast card_le_card subset_union_left)
  have h1 : max (#A0 : ℝ) (HarperNum.psi n #A1) ≤ #(cubeNbhd 1 A1 ∪ A0) := by
    apply max_le
    · exact_mod_cast card_le_card subset_union_right
    · rcases Nat.eq_zero_or_pos #A1 with h | h
      · rw [h, Nat.cast_zero]
        refine (HarperNum.psi_zero_le n).trans ?_
        exact_mod_cast ha1.trans (card_le_card subset_union_right)
      · exact (ih A1 (card_pos.1 h)).trans (by exact_mod_cast card_le_card subset_union_left)
  push_cast
  linarith

/-- **Vertex isoperimetry with the interpolated ball profile**: a nonempty set `A` of the
`n`-cube has `|N₁(A)| ≥ psi n |A|`. -/
private theorem psi_le_card_cubeNbhd_one : ∀ (n : ℕ) (A : Finset (Finset (Fin n))), A.Nonempty →
    HarperNum.psi n #A ≤ #(cubeNbhd 1 A)
  | 0, A, hA => by
    have h1 : HarperNum.psi 0 #A ≤ 1 := by
      refine (HarperNum.psi_le_line (Nat.zero_le 0) _).trans ?_
      simp [HarperNum.line, HarperNum.vol_one]
    have h2 : (1 : ℝ) ≤ #(cubeNbhd 1 A) := by
      exact_mod_cast (hA.card_pos).trans_le (card_le_card (subset_cubeNbhd 1 A))
    linarith
  | n + 1, A, hA => by
    have ih := psi_le_card_cubeNbhd_one n
    have hsplit := card_nbhd_split A
    have hcard := card_lo_add_hi A
    have hApos := hA.card_pos
    rcases le_total #(hi A) #(lo A) with h | h
    · calc HarperNum.psi (n + 1) #A
          = HarperNum.psi (n + 1) ((#(lo A) + #(hi A) : ℕ) : ℝ) := by rw [hcard]
        _ ≤ #(cubeNbhd 1 (lo A) ∪ hi A) + #(cubeNbhd 1 (hi A) ∪ lo A) :=
          step_aux ih (lo A) (hi A) h (by omega)
        _ ≤ #(cubeNbhd 1 A) := by exact_mod_cast hsplit
    · calc HarperNum.psi (n + 1) #A
          = HarperNum.psi (n + 1) ((#(hi A) + #(lo A) : ℕ) : ℝ) := by rw [Nat.add_comm #(hi A), hcard]
        _ ≤ #(cubeNbhd 1 (hi A) ∪ lo A) + #(cubeNbhd 1 (lo A) ∪ hi A) :=
          step_aux ih (hi A) (lo A) h (by omega)
        _ ≤ #(cubeNbhd 1 A) := by rw [add_comm]; exact_mod_cast hsplit

private lemma card_lowBall_le_cubeNbhd {k : ℕ} (hk : 1 ≤ k) (A : Finset (Finset (Fin n)))
    (hA : #(lowBall n k) ≤ #A) : ∀ t, #(lowBall n (k + t)) ≤ #(cubeNbhd t A)
  | 0 => hA.trans (card_le_card (subset_cubeNbhd 0 A))
  | t + 1 => by
    have ih := card_lowBall_le_cubeNbhd hk A hA t
    have hpos : 1 ≤ #(lowBall n (k + t)) := by
      have : (∅ : Finset (Fin n)) ∈ lowBall n (k + t) := by
        rw [mem_lowBall, card_empty]; omega
      exact card_pos.2 ⟨_, this⟩
    have hne : (cubeNbhd t A).Nonempty := card_pos.1 (by omega)
    have h1 := psi_le_card_cubeNbhd_one n (cubeNbhd t A) hne
    have h2 : (#(lowBall n (k + t + 1)) : ℝ) ≤ HarperNum.psi n #(lowBall n (k + t)) := by
      rw [card_lowBall_eq_vol, card_lowBall_eq_vol]; exact HarperNum.psi_vol n (k + t)
    have h3 : HarperNum.psi n #(lowBall n (k + t)) ≤ HarperNum.psi n #(cubeNbhd t A) :=
      HarperNum.psi_mono n (by exact_mod_cast ih)
    have h4 : (#(cubeNbhd 1 (cubeNbhd t A)) : ℝ) ≤ #(cubeNbhd (t + 1) A) := by
      exact_mod_cast card_le_card (cubeNbhd_one_cubeNbhd_subset t A)
    have : (#(lowBall n (k + (t + 1))) : ℝ) ≤ #(cubeNbhd (t + 1) A) := by
      rw [← add_assoc]; linarith
    exact_mod_cast this

end HarperCube

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
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : lowBall n 0 = ∅ := by ext T; simp [lowBall]
    have h1 : cubeNbhd t (∅ : Finset (Finset (Fin n))) = ∅ := by ext T; simp [cubeNbhd]
    rw [h0, h1, card_empty]
    exact Nat.zero_le _
  rw [cubeNbhd_lowBall t hk]
  exact HarperCube.card_lowBall_le_cubeNbhd hk A hA t

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


/-! ### The cube metric, and expansion from `ε` to `1 - ε` -/

/-- The Hamming distance satisfies the triangle inequality. -/
theorem hamDist_triangle (S T U : Finset (Fin n)) :
    hamDist S U ≤ hamDist S T + hamDist T U := by
  classical
  have h1 : S \ U ⊆ (S \ T) ∪ (T \ U) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
    by_cases hT : x ∈ T
    · exact Or.inr ⟨hT, hx.2⟩
    · exact Or.inl ⟨hx.1, hT⟩
  have h2 : U \ S ⊆ (U \ T) ∪ (T \ S) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
    by_cases hT : x ∈ T
    · exact Or.inr ⟨hT, hx.2⟩
    · exact Or.inl ⟨hx.1, hT⟩
  have hc1 : #(S \ U) ≤ #(S \ T) + #(T \ U) :=
    le_trans (Finset.card_le_card h1) (Finset.card_union_le _ _)
  have hc2 : #(U \ S) ≤ #(U \ T) + #(T \ S) :=
    le_trans (Finset.card_le_card h2) (Finset.card_union_le _ _)
  rw [hamDist, hamDist, hamDist]
  omega

/-- Expanding twice expands by the sum of the radii. -/
theorem cubeNbhd_cubeNbhd_subset (s t : ℕ) (A : Finset (Finset (Fin n))) :
    cubeNbhd s (cubeNbhd t A) ⊆ cubeNbhd (t + s) A := by
  intro T hT
  rw [mem_cubeNbhd] at hT
  obtain ⟨S, hS, hdS⟩ := hT
  rw [mem_cubeNbhd] at hS
  obtain ⟨R, hR, hdR⟩ := hS
  rw [mem_cubeNbhd]
  refine ⟨R, hR, ?_⟩
  exact le_trans (hamDist_triangle R S T) (by omega)

/-- **Theorem 9.4.6 (rapid expansion from `ε` to `1 - ε`), conditional on Harper.**

Writing `ε = e^{-2t²/n}` — the notes' `t = √(n log(1/ε)/2)` — a set with more than `ε 2ⁿ`
points expands in `2t` steps to more than `(1 - ε) 2ⁿ`.

Harper's inequality enters as the hypothesis `harper`, in exactly the form task #46 will
prove, so this derivation is `sorry`-free and the missing input is visible.

**The hypothesis is strict where the notes write `≥`, and that is needed.** With `|A| = ε 2ⁿ`
exactly, the counting step gives `2ⁿ ≤ 2ⁿ` and no contradiction; the notes' own proof quietly
uses a strict Chernoff bound at that point. -/
theorem card_cubeNbhd_two_mul_ge_of_harper
    (harper : ∀ (t k : ℕ) (A : Finset (Finset (Fin n))), #(lowBall n k) ≤ #A →
      #(cubeNbhd t (lowBall n k)) ≤ #(cubeNbhd t A))
    (hn : 0 < n) {t : ℕ} (ht : 0 < t) (A : Finset (Finset (Fin n)))
    (hA : (2 : ℝ) ^ n * Real.exp (-(2 * (t : ℝ) ^ 2) / n) < #A) :
    (2 : ℝ) ^ n * (1 - Real.exp (-(2 * (t : ℝ) ^ 2) / n)) ≤ #(cubeNbhd (2 * t) A) := by
  classical
  set ε : ℝ := Real.exp (-(2 * (t : ℝ) ^ 2) / n) with hεdef
  have hcardcube : #(univ : Finset (Finset (Fin n))) = 2 ^ n := by
    rw [card_univ, Fintype.card_finset, Fintype.card_fin]
  have hhalf : 2 * #(lowBall n ((n + 1) / 2)) ≤ 2 ^ n := card_lowBall_half_le hn
  -- the complement of the first expansion is small
  set A' : Finset (Finset (Fin n)) := (univ : Finset (Finset (Fin n))) \ cubeNbhd t A with hA'def
  have hdisj : ∀ T ∈ cubeNbhd t A', T ∉ A := by
    intro T hT hTA
    rw [mem_cubeNbhd] at hT
    obtain ⟨S, hS, hd⟩ := hT
    rw [hA'def, Finset.mem_sdiff] at hS
    refine hS.2 ?_
    rw [mem_cubeNbhd]
    exact ⟨T, hTA, by rw [hamDist] at hd ⊢; omega⟩
  have hsmall : (#A' : ℝ) < 2 ^ (n - 1) := by
    by_contra hcon
    push_neg at hcon
    -- Harper applies to `A'`, so its expansion is large
    have hballle : #(lowBall n ((n + 1) / 2)) ≤ #A' := by
      have h1 : (#(lowBall n ((n + 1) / 2)) : ℝ) ≤ 2 ^ (n - 1) := by
        have h2 : (2 : ℝ) * #(lowBall n ((n + 1) / 2)) ≤ 2 ^ n := by exact_mod_cast hhalf
        have h3 : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [h3] at h2
        linarith
      exact_mod_cast le_trans h1 hcon
    have hbig := card_cubeNbhd_ge_of_harper hn ht A' (by exact_mod_cast hcon)
      (harper t ((n + 1) / 2) A' hballle)
    -- but `A` and the expansion of `A'` are disjoint
    have hle : #A + #(cubeNbhd t A') ≤ 2 ^ n := by
      rw [← hcardcube]
      have hdisjoint : Disjoint A (cubeNbhd t A') := by
        rw [Finset.disjoint_right]
        exact fun T hT => hdisj T hT
      rw [← Finset.card_union_of_disjoint hdisjoint]
      exact Finset.card_le_card (Finset.subset_univ _)
    have hleR : (#A : ℝ) + #(cubeNbhd t A') ≤ 2 ^ n := by exact_mod_cast hle
    rw [← hεdef] at hbig
    linarith
  -- so the first expansion is at least half the cube
  have hhalfA : (2 : ℝ) ^ (n - 1) ≤ #(cubeNbhd t A) := by
    have hsub : cubeNbhd t A ⊆ (univ : Finset (Finset (Fin n))) := Finset.subset_univ _
    have hcard : #A' = 2 ^ n - #(cubeNbhd t A) := by
      rw [hA'def, Finset.card_sdiff_of_subset hsub, hcardcube]
    have hle : #(cubeNbhd t A) ≤ 2 ^ n := by
      rw [← hcardcube]
      exact Finset.card_le_card hsub
    have hcardR : (#A' : ℝ) = 2 ^ n - #(cubeNbhd t A) := by
      rw [hcard, Nat.cast_sub hle]
      push_cast
      ring
    have h3 : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hcardR] at hsmall
    linarith
  -- expand a second time
  have hballle2 : #(lowBall n ((n + 1) / 2)) ≤ #(cubeNbhd t A) := by
    have h1 : (#(lowBall n ((n + 1) / 2)) : ℝ) ≤ 2 ^ (n - 1) := by
      have h2 : (2 : ℝ) * #(lowBall n ((n + 1) / 2)) ≤ 2 ^ n := by exact_mod_cast hhalf
      have h3 : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h3] at h2
      linarith
    exact_mod_cast le_trans h1 hhalfA
  have hsecond := card_cubeNbhd_ge_of_harper hn ht (cubeNbhd t A) (by exact_mod_cast hhalfA)
    (harper t ((n + 1) / 2) (cubeNbhd t A) hballle2)
  rw [← hεdef] at hsecond
  calc (2 : ℝ) ^ n * (1 - ε) ≤ #(cubeNbhd t (cubeNbhd t A)) := hsecond
    _ ≤ #(cubeNbhd (2 * t) A) := by
        have hsub := cubeNbhd_cubeNbhd_subset t t A
        have : t + t = 2 * t := by ring
        rw [this] at hsub
        exact_mod_cast Finset.card_le_card hsub


end HammingCube

end PMC
