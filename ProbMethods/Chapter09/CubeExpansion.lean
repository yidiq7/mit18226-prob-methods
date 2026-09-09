import ProbMethods.Chapter09.BoundedDifferences

/-!
# §9.4 — rapid expansion again, this time without Harper

`Chapter09/HammingCube.lean` follows the notes' *first* proof of Theorem 9.4.6, through
Harper's isoperimetric inequality, which the notes state without proof and which is published
here as task #46. The notes then give a **second proof** that uses only the bounded
differences inequality — and §9.1 now supplies that, so the theorem can be had outright.

The cube is written here as `Fin n → Bool`, the shape §9.1's development is stated for, rather
than as `Finset (Fin n)` as in `HammingCube.lean`. The two are the same object; keeping both
encodings avoids a transfer layer whose only purpose would be to restate a theorem already
proved.

The argument, in the notes' words: apply concentration to `f = dist(·, A)`, which has bounded
differences `1`. Since `f = 0` on `A`, which is more than an `ε` fraction, the lower tail
forces `E f < t`; the upper tail then puts all but an `ε` fraction within `2t` of `A`.
-/

open Finset

namespace PMC

section CubeExpansion

variable {n : ℕ}

/-- The Hamming distance on the cube `Fin n → Bool`. -/
def fHamDist (x y : Fin n → Bool) : ℕ :=
  #((univ : Finset (Fin n)).filter fun i => x i ≠ y i)

/-- The `t`-neighbourhood of a set of cube points. -/
def fNbhd (t : ℕ) (A : Finset (Fin n → Bool)) : Finset (Fin n → Bool) :=
  (univ : Finset (Fin n → Bool)).filter fun y => ∃ x ∈ A, fHamDist x y ≤ t

lemma mem_fNbhd {t : ℕ} {A : Finset (Fin n → Bool)} {y : Fin n → Bool} :
    y ∈ fNbhd t A ↔ ∃ x ∈ A, fHamDist x y ≤ t := by
  rw [fNbhd, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- Changing one coordinate changes the distance to a fixed point by at most one. -/
lemma fHamDist_le_succ {a x y : Fin n → Bool} {i : Fin n} (hxy : ∀ j, j ≠ i → x j = y j) :
    fHamDist a x ≤ fHamDist a y + 1 := by
  classical
  have hsub : ((univ : Finset (Fin n)).filter fun j => a j ≠ x j)
      ⊆ insert i ((univ : Finset (Fin n)).filter fun j => a j ≠ y j) := by
    intro j hj
    rw [mem_filter] at hj
    rw [Finset.mem_insert]
    by_cases hji : j = i
    · exact Or.inl hji
    · refine Or.inr ?_
      rw [mem_filter, ← hxy j hji]
      exact ⟨mem_univ _, hj.2⟩
  calc fHamDist a x ≤ #(insert i ((univ : Finset (Fin n)).filter fun j => a j ≠ y j)) :=
        Finset.card_le_card hsub
    _ ≤ #((univ : Finset (Fin n)).filter fun j => a j ≠ y j) + 1 := Finset.card_insert_le _ _

/-- The distance from a point to a nonempty set. -/
noncomputable def distToSet (A : Finset (Fin n → Bool)) (y : Fin n → Bool) : ℝ :=
  if h : A.Nonempty then ((A.inf' h fun a => fHamDist a y : ℕ) : ℝ) else 0

lemma distToSet_eq_zero_of_mem {A : Finset (Fin n → Bool)} {y : Fin n → Bool} (hy : y ∈ A) :
    distToSet A y = 0 := by
  have hne : A.Nonempty := ⟨y, hy⟩
  rw [distToSet, dif_pos hne]
  have hzero : (A.inf' hne fun a => fHamDist a y) = 0 := by
    refine Nat.le_zero.mp ?_
    have := Finset.inf'_le (fun a => fHamDist a y) hy
    have hself : fHamDist y y = 0 := by
      rw [fHamDist, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _
      simp
    rwa [hself] at this
  rw [hzero, Nat.cast_zero]

lemma exists_mem_of_distToSet_lt {A : Finset (Fin n → Bool)} (hne : A.Nonempty)
    {y : Fin n → Bool} {t : ℕ} (h : distToSet A y < t + 1) :
    ∃ x ∈ A, fHamDist x y ≤ t := by
  rw [distToSet, dif_pos hne] at h
  obtain ⟨a, ha, hval⟩ := Finset.exists_mem_eq_inf' hne (fun a => fHamDist a y)
  refine ⟨a, ha, ?_⟩
  have : ((fHamDist a y : ℕ) : ℝ) < t + 1 := by rw [← hval]; exact h
  have hlt : fHamDist a y < t + 1 := by exact_mod_cast this
  omega

/-- **The distance to a set has bounded differences `1`.** -/
lemma bddDiff_distToSet (A : Finset (Fin n → Bool)) (hne : A.Nonempty) :
    BddDiff (distToSet A) (fun _ => 1) := by
  classical
  have key : ∀ (x y : Fin n → Bool) (i : Fin n), (∀ j, j ≠ i → x j = y j) →
      distToSet A x ≤ distToSet A y + 1 := by
    intro x y i hxy
    rw [distToSet, distToSet, dif_pos hne, dif_pos hne]
    obtain ⟨a, ha, hval⟩ := Finset.exists_mem_eq_inf' hne (fun a => fHamDist a y)
    have hle : (A.inf' hne fun a => fHamDist a x) ≤ fHamDist a y + 1 := by
      refine le_trans (Finset.inf'_le (fun a => fHamDist a x) ha) ?_
      exact fHamDist_le_succ hxy
    have : ((A.inf' hne fun a => fHamDist a x : ℕ) : ℝ) ≤ ((fHamDist a y : ℕ) : ℝ) + 1 := by
      exact_mod_cast hle
    rw [hval]
    exact this
  intro i x y hxy
  show |distToSet A x - distToSet A y| ≤ (1 : ℝ)
  rw [abs_le]
  have h1 := key x y i hxy
  have h2 := key y x i (fun j hj => (hxy j hj).symm)
  exact ⟨by linarith, by linarith⟩

/-! ### Theorem 9.4.6 without Harper -/

/-- **Theorem 9.4.6 (rapid expansion from `ε` to `1 - ε`), Harper-free.** With
`ε = e^{-2t²/n}`, a set of more than `ε 2ⁿ` cube points expands in `2t` steps to at least
`(1 - ε) 2ⁿ`.

This is the notes' *second* proof, which uses only the bounded differences inequality. Apply
concentration to `f = dist(·, A)`: it has bounded differences `1`, it vanishes on `A`, and `A`
is more than an `ε` fraction, so the lower tail forces `E f < t`; the upper tail then puts all
but an `ε` fraction within `2t` of `A`.

Compare `PMC.card_cubeNbhd_two_mul_ge_of_harper`, the same statement in the subset encoding,
which follows the notes' first proof and therefore needs Harper's inequality as a
hypothesis. **This version needs no such hypothesis** — only Hoeffding's lemma, via §9.1. -/
theorem card_fNbhd_ge (hoeff : HoeffdingUnif Bool) (hn : 0 < n) {t : ℕ} (ht : 0 < t)
    (A : Finset (Fin n → Bool))
    (hA : (2 : ℝ) ^ n * Real.exp (-(2 * (t : ℝ) ^ 2) / n) < #A) :
    (2 : ℝ) ^ n * (1 - Real.exp (-(2 * (t : ℝ) ^ 2) / n)) ≤ #(fNbhd (2 * t) A) := by
  classical
  set ε : ℝ := Real.exp (-(2 * (t : ℝ) ^ 2) / n) with hεdef
  have hεpos : 0 < ε := Real.exp_pos _
  have hcard2 : (Fintype.card Bool : ℝ) = 2 := by rw [Fintype.card_bool]; norm_num
  have hcube : #(univ : Finset (Fin n → Bool)) = 2 ^ n := by
    rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  -- `A` is nonempty, since it is larger than a positive quantity
  have hne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hcon
    rw [hcon, Finset.card_empty, Nat.cast_zero] at hA
    have : (0 : ℝ) < 2 ^ n * ε := by positivity
    linarith
  set f : (Fin n → Bool) → ℝ := distToSet A with hfdef
  have hbd : BddDiff f (fun _ => 1) := bddDiff_distToSet A hne
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hS : (0 : ℝ) < ∑ _i : Fin n, (1 : ℝ) ^ 2 := by
    rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hSval : ∑ _i : Fin n, (1 : ℝ) ^ 2 = (n : ℝ) := by
    rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- both tails, at `t`
  have hup := card_filter_ge_le hoeff f (fun _ => 1) hbd htR hS
  have hlo := card_filter_le_le hoeff f (fun _ => 1) hbd htR hS
  rw [hSval, hcard2] at hup hlo
  rw [← hεdef] at hup hlo
  -- the mean is small: `f` vanishes on `A`, which is too big for the lower tail
  have hmean : pAvg f < t := by
    by_contra hcon
    push_neg at hcon
    have hsub : A ⊆ (univ : Finset (Fin n → Bool)).filter fun x => f x ≤ pAvg f - t := by
      intro x hx
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [hfdef, distToSet_eq_zero_of_mem hx]
      linarith
    have : (#A : ℝ) ≤ 2 ^ n * ε := le_trans (by exact_mod_cast Finset.card_le_card hsub) hlo
    linarith
  -- everything outside the `2t`-neighbourhood is in the upper tail
  have hout : ((univ : Finset (Fin n → Bool)) \ fNbhd (2 * t) A)
      ⊆ (univ : Finset (Fin n → Bool)).filter fun x => pAvg f + t ≤ f x := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have hfar : ¬ (f x < (2 * t : ℕ) + 1) := by
      intro hlt
      obtain ⟨a, ha, hd⟩ := exists_mem_of_distToSet_lt hne (by rw [hfdef] at hlt; exact hlt)
      exact hx.2 (mem_fNbhd.mpr ⟨a, ha, hd⟩)
    push_neg at hfar
    have h2t : ((2 * t : ℕ) : ℝ) = 2 * t := by push_cast; ring
    rw [h2t] at hfar
    linarith
  have hcompl : (2 : ℝ) ^ n - #(fNbhd (2 * t) A) ≤ 2 ^ n * ε := by
    have hsub : fNbhd (2 * t) A ⊆ (univ : Finset (Fin n → Bool)) := Finset.subset_univ _
    have hc1 : #((univ : Finset (Fin n → Bool)) \ fNbhd (2 * t) A)
        = 2 ^ n - #(fNbhd (2 * t) A) := by
      rw [Finset.card_sdiff_of_subset hsub, hcube]
    have hc2 : (#((univ : Finset (Fin n → Bool)) \ fNbhd (2 * t) A) : ℝ)
        = 2 ^ n - #(fNbhd (2 * t) A) := by
      rw [hc1, Nat.cast_sub (by rw [← hcube]; exact Finset.card_le_card hsub)]
      push_cast
      ring
    calc (2 : ℝ) ^ n - #(fNbhd (2 * t) A)
        = #((univ : Finset (Fin n → Bool)) \ fNbhd (2 * t) A) := hc2.symm
      _ ≤ #((univ : Finset (Fin n → Bool)).filter fun x => pAvg f + t ≤ f x) := by
          exact_mod_cast Finset.card_le_card hout
      _ ≤ 2 ^ n * ε := hup
  calc (2 : ℝ) ^ n * (1 - ε) = 2 ^ n - 2 ^ n * ε := by ring
    _ ≤ #(fNbhd (2 * t) A) := by linarith


end CubeExpansion

end PMC
