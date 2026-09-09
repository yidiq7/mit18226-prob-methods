import ProbMethods.Chapter09.Hoeffding

/-!
# §9.2 — Azuma's inequality in the finite framework (Theorems 9.2.7, 9.2.8)

Zhao, *Probabilistic Methods in Combinatorics*, Theorems 9.2.7 and 9.2.8: for a martingale
`Z₀, …, Z_n` with `|Zᵢ - Zᵢ₋₁| ≤ cᵢ`,

    P(Z_n - Z₀ ≥ λ) ≤ exp(-λ²/(2 ∑ cᵢ²)).

§9.1's bounded-differences inequality is the *Doob* case of this — the martingale there is the
sequence of partial averages of a function on a product space — and the applications in §9.3
use that case. What this file adds is the general statement, for an arbitrary finite
filtration.

## Conditioning by reweighting

The one design decision. A filtration step is a map `π : Ω → K`, and conditioning on it is
usually done by restricting to a fibre, which in Lean means subtypes and a change of sample
space at every step. Instead, conditioning here **reweights**: `PMC.fibreWeight w π k` is the
weight `w` renormalised on the fibre `π⁻¹(k)` and zero off it. That is again a weight on the
same `Ω`, so every lemma about weights — in particular `PMC.wmean_exp_le_of_mem_Icc`,
Hoeffding's lemma, which is what the martingale step needs fibrewise — applies with no
transport at all.

`PMC.wmean_eq_sum_fibre` is then the only structural fact required: a mean is the fibre-weighted
average of the conditional means. Zero-weight fibres need no side condition, since the
conditional mean against the zero weight is `0` and the fibre's own weight is `0` too.
-/

open Finset

namespace PMC

section Fibre

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {K : Type*} [Fintype K] [DecidableEq K]

/-- The total weight of the fibre of `π` over `k`. -/
def fibreMass (w : Ω → ℝ) (π : Ω → K) (k : K) : ℝ :=
  ∑ ω ∈ (univ : Finset Ω).filter fun ω => π ω = k, w ω

/-- The weight `w` conditioned on the fibre `π⁻¹(k)`: renormalised there, zero elsewhere. -/
noncomputable def fibreWeight (w : Ω → ℝ) (π : Ω → K) (k : K) : Ω → ℝ :=
  fun ω => if π ω = k then w ω / fibreMass w π k else 0

@[simp] lemma fibreWeight_apply (w : Ω → ℝ) (π : Ω → K) (k : K) (ω : Ω) :
    fibreWeight w π k ω = if π ω = k then w ω / fibreMass w π k else 0 := rfl

lemma fibreMass_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (π : Ω → K) (k : K) :
    0 ≤ fibreMass w π k :=
  Finset.sum_nonneg fun ω _ => hw ω

lemma fibreWeight_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (π : Ω → K) (k : K) (ω : Ω) :
    0 ≤ fibreWeight w π k ω := by
  rw [fibreWeight_apply]
  by_cases h : π ω = k
  · rw [if_pos h]
    exact div_nonneg (hw ω) (fibreMass_nonneg hw π k)
  · rw [if_neg h]

lemma sum_fibreWeight {w : Ω → ℝ} (π : Ω → K) {k : K} (hk : fibreMass w π k ≠ 0) :
    ∑ ω, fibreWeight w π k ω = 1 := by
  classical
  simp only [fibreWeight_apply]
  rw [← Finset.sum_filter, ← Finset.sum_div]
  rw [show ∑ ω ∈ (univ : Finset Ω).filter (fun ω => π ω = k), w ω = fibreMass w π k from rfl,
    div_self hk]

/-- **A mean is the fibre-weighted average of the conditional means.** -/
theorem wmean_eq_sum_fibre {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (π : Ω → K) (f : Ω → ℝ) :
    wmean w f = ∑ k, fibreMass w π k * wmean (fibreWeight w π k) f := by
  classical
  have hterm : ∀ k : K, fibreMass w π k * wmean (fibreWeight w π k) f
      = ∑ ω ∈ (univ : Finset Ω).filter fun ω => π ω = k, w ω * f ω := by
    intro k
    by_cases hk : fibreMass w π k = 0
    · rw [hk, zero_mul]
      -- a zero-mass fibre contributes nothing on either side: its weights all vanish
      refine (Finset.sum_eq_zero fun ω hω => ?_).symm
      have hzero : w ω = 0 := by
        have hle : w ω ≤ fibreMass w π k := Finset.single_le_sum (f := w) (fun x _ => hw x) hω
        have := hw ω
        rw [hk] at hle
        linarith
      rw [hzero, zero_mul]
    · rw [wmean, Finset.mul_sum]
      simp only [fibreWeight_apply, mul_ite, ite_mul, mul_zero, zero_mul]
      rw [← Finset.sum_filter]
      refine Finset.sum_congr rfl fun ω hω => ?_
      rw [mem_filter] at hω
      field_simp
  rw [Finset.sum_congr rfl fun k _ => hterm k, wmean]
  exact (Finset.sum_fiberwise_of_maps_to (fun ω _ => mem_univ (π ω)) fun ω => w ω * f ω).symm


/-- Two functions agreeing on the fibre have the same conditional mean. -/
lemma wmean_fibreWeight_congr (w : Ω → ℝ) (π : Ω → K) (k : K) {g h : Ω → ℝ}
    (hgh : ∀ ω, π ω = k → g ω = h ω) :
    wmean (fibreWeight w π k) g = wmean (fibreWeight w π k) h := by
  rw [wmean, wmean]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : π ω = k
  · rw [hgh ω hω]
  · rw [fibreWeight_apply, if_neg hω, zero_mul, zero_mul]

/-- A conditional mean of a constant is that constant. -/
lemma wmean_fibreWeight_const {w : Ω → ℝ} (π : Ω → K) {k : K} (hk : fibreMass w π k ≠ 0)
    (a : ℝ) : wmean (fibreWeight w π k) (fun _ => a) = a := by
  rw [wmean, ← Finset.sum_mul, sum_fibreWeight π hk, one_mul]

lemma wmean_fibreWeight_const_mul (w : Ω → ℝ) (π : Ω → K) (k : K) (a : ℝ) (g : Ω → ℝ) :
    wmean (fibreWeight w π k) (fun ω => a * g ω) = a * wmean (fibreWeight w π k) g := by
  rw [wmean, wmean, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  ring

/-- **One step of Azuma's induction.** With `Y` measurable for the current step of the
filtration (the past), `Z` a bounded increment of conditional mean zero,

    E[exp (λ (Y + Z))] ≤ exp(λ²(2c)²/8) · E[exp (λ Y)].

Fibrewise this is Hoeffding's lemma (`PMC.wmean_exp_le_of_mem_Icc`) applied to the conditioned
weight, with `exp (λ Y)` pulled out because `Y` is constant on the fibre. -/
theorem wmean_exp_step {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (π : Ω → K) (Y Z : Ω → ℝ) {c : ℝ}
    (hmeas : ∀ ω ω', π ω = π ω' → Y ω = Y ω') (hbdd : ∀ ω, Z ω ∈ Set.Icc (-c) c)
    (hmart : ∀ k, fibreMass w π k ≠ 0 → wmean (fibreWeight w π k) Z = 0) (lam : ℝ) :
    wmean w (fun ω => Real.exp (lam * (Y ω + Z ω)))
      ≤ Real.exp (lam ^ 2 * (2 * c) ^ 2 / 8) * wmean w (fun ω => Real.exp (lam * Y ω)) := by
  classical
  rw [wmean_eq_sum_fibre hw π, wmean_eq_sum_fibre hw π, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : fibreMass w π k = 0
  · rw [hk, zero_mul, zero_mul, mul_zero]
  -- a representative of the fibre, on which `Y` is constant
  have hne : ((univ : Finset Ω).filter fun ω => π ω = k).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [fibreMass, hempty, Finset.sum_empty] at hk
    exact hk rfl
  obtain ⟨ω₀, hω₀⟩ := hne
  rw [mem_filter] at hω₀
  have hYconst : ∀ ω, π ω = k → Y ω = Y ω₀ := fun ω hω =>
    hmeas ω ω₀ (by rw [hω, hω₀.2])
  have hmass : 0 ≤ fibreMass w π k := fibreMass_nonneg hw π k
  -- the two conditional means
  have hright : wmean (fibreWeight w π k) (fun ω => Real.exp (lam * Y ω))
      = Real.exp (lam * Y ω₀) := by
    rw [wmean_fibreWeight_congr w π k (g := fun ω => Real.exp (lam * Y ω))
      (h := fun _ => Real.exp (lam * Y ω₀)) fun ω hω => by rw [hYconst ω hω],
      wmean_fibreWeight_const π hk]
  have hleft : wmean (fibreWeight w π k) (fun ω => Real.exp (lam * (Y ω + Z ω)))
      ≤ Real.exp (lam ^ 2 * (2 * c) ^ 2 / 8) * Real.exp (lam * Y ω₀) := by
    have hcongr : wmean (fibreWeight w π k) (fun ω => Real.exp (lam * (Y ω + Z ω)))
        = Real.exp (lam * Y ω₀) * wmean (fibreWeight w π k) (fun ω => Real.exp (lam * Z ω)) := by
      rw [← wmean_fibreWeight_const_mul w π k (Real.exp (lam * Y ω₀))
        (fun ω => Real.exp (lam * Z ω))]
      refine wmean_fibreWeight_congr w π k fun ω hω => ?_
      rw [hYconst ω hω, ← Real.exp_add]
      congr 1
      ring
    rw [hcongr, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hhoeff := wmean_exp_le_of_mem_Icc (fibreWeight_nonneg hw π k)
      (sum_fibreWeight π hk) Z hbdd (hmart k hk) lam
    rw [show c - -c = 2 * c from by ring] at hhoeff
    exact hhoeff
  calc fibreMass w π k * wmean (fibreWeight w π k) (fun ω => Real.exp (lam * (Y ω + Z ω)))
      ≤ fibreMass w π k * (Real.exp (lam ^ 2 * (2 * c) ^ 2 / 8) * Real.exp (lam * Y ω₀)) :=
        mul_le_mul_of_nonneg_left hleft hmass
    _ = Real.exp (lam ^ 2 * (2 * c) ^ 2 / 8) * (fibreMass w π k * Real.exp (lam * Y ω₀)) := by
        ring
    _ = Real.exp (lam ^ 2 * (2 * c) ^ 2 / 8)
          * (fibreMass w π k * wmean (fibreWeight w π k) (fun ω => Real.exp (lam * Y ω))) := by
        rw [hright]

end Fibre


section Martingale

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {K : Type*} [Fintype K] [DecidableEq K]

/-- A filtration refines backwards: if two points are not separated at step `j`, they are not
separated at any earlier step. -/
lemma filtration_mono {π : ℕ → Ω → K}
    (hfilt : ∀ i ω ω', π (i + 1) ω = π (i + 1) ω' → π i ω = π i ω') :
    ∀ i j, i ≤ j → ∀ ω ω', π j ω = π j ω' → π i ω = π i ω' := by
  intro i j hij
  induction j with
  | zero =>
    intro ω ω' h
    rw [show i = 0 from by omega]
    exact h
  | succ j ih =>
    intro ω ω' h
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact ih (by omega) ω ω' (hfilt j ω ω' h)
    · rw [show i = j + 1 from by omega]
      exact h

/-- **The moment generating function of a martingale with bounded increments**:

    E[exp (λ (Z_n - Z_0))] ≤ exp (λ² ∑_{i<n} (2cᵢ)² / 8).

`PMC.wmean_exp_step` applied `n` times. -/
theorem wmean_exp_martingale {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (π : ℕ → Ω → K) (Z : ℕ → Ω → ℝ) (c : ℕ → ℝ)
    (hmeas : ∀ i ω ω', π i ω = π i ω' → Z i ω = Z i ω')
    (hfilt : ∀ i ω ω', π (i + 1) ω = π (i + 1) ω' → π i ω = π i ω')
    (hbdd : ∀ i ω, Z (i + 1) ω - Z i ω ∈ Set.Icc (-(c i)) (c i))
    (hmart : ∀ i k, fibreMass w (π i) k ≠ 0 →
      wmean (fibreWeight w (π i) k) (fun ω => Z (i + 1) ω - Z i ω) = 0)
    (lam : ℝ) (n : ℕ) :
    wmean w (fun ω => Real.exp (lam * (Z n ω - Z 0 ω)))
      ≤ Real.exp (lam ^ 2 * (∑ i ∈ Finset.range n, (2 * c i) ^ 2) / 8) := by
  induction n with
  | zero =>
    have hone : wmean w (fun ω => Real.exp (lam * (Z 0 ω - Z 0 ω))) = 1 := by
      rw [wmean, Finset.sum_congr rfl fun ω (_ : ω ∈ (univ : Finset Ω)) => by
        rw [sub_self, mul_zero, Real.exp_zero, mul_one]]
      exact hsum
    rw [hone, Finset.range_zero, Finset.sum_empty, mul_zero, zero_div, Real.exp_zero]
  | succ n ih =>
    -- the past `Y = Z n - Z 0` is measurable for step `n`
    have hY : ∀ ω ω', π n ω = π n ω' → Z n ω - Z 0 ω = Z n ω' - Z 0 ω' := by
      intro ω ω' h
      rw [hmeas n ω ω' h, hmeas 0 ω ω' (filtration_mono hfilt 0 n (by omega) ω ω' h)]
    have hstep := wmean_exp_step hw (π n) (fun ω => Z n ω - Z 0 ω)
      (fun ω => Z (n + 1) ω - Z n ω) hY (hbdd n) (hmart n) lam
    have hsplit : ∀ ω, Z (n + 1) ω - Z 0 ω = (Z n ω - Z 0 ω) + (Z (n + 1) ω - Z n ω) := by
      intro ω
      ring
    have hexp : ∀ ω, Real.exp (lam * (Z (n + 1) ω - Z 0 ω))
        = Real.exp (lam * ((Z n ω - Z 0 ω) + (Z (n + 1) ω - Z n ω))) := by
      intro ω
      rw [hsplit ω]
    calc wmean w (fun ω => Real.exp (lam * (Z (n + 1) ω - Z 0 ω)))
        = wmean w (fun ω => Real.exp (lam * ((Z n ω - Z 0 ω) + (Z (n + 1) ω - Z n ω)))) := by
          rw [wmean, wmean]
          exact Finset.sum_congr rfl fun ω _ => by rw [hexp ω]
      _ ≤ Real.exp (lam ^ 2 * (2 * c n) ^ 2 / 8)
            * wmean w (fun ω => Real.exp (lam * (Z n ω - Z 0 ω))) := hstep
      _ ≤ Real.exp (lam ^ 2 * (2 * c n) ^ 2 / 8)
            * Real.exp (lam ^ 2 * (∑ i ∈ Finset.range n, (2 * c i) ^ 2) / 8) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = Real.exp (lam ^ 2 * (∑ i ∈ Finset.range (n + 1), (2 * c i) ^ 2) / 8) := by
          rw [← Real.exp_add, Finset.sum_range_succ]
          congr 1
          ring

/-- **Azuma's inequality** (Zhao, Theorems 9.2.7 and 9.2.8). For a martingale `Z` with
`|Zᵢ₊₁ - Zᵢ| ≤ cᵢ`,

    P(Z_n - Z_0 ≥ t) ≤ exp(-t² / (2 ∑_{i<n} cᵢ²)).

Markov applied to `PMC.wmean_exp_martingale` at `λ = t / ∑ cᵢ²`. Theorem 9.2.7 is the case
`cᵢ = 1`, where the bound reads `exp(-t²/(2n))`.

The martingale hypothesis is `hmart`: each increment has conditional mean zero on every fibre
of positive weight. `hmeas` says each `Zᵢ` is measurable for its step, and `hfilt` that the
filtration refines. -/
theorem wprob_martingale_ge_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (π : ℕ → Ω → K) (Z : ℕ → Ω → ℝ) (c : ℕ → ℝ)
    (hmeas : ∀ i ω ω', π i ω = π i ω' → Z i ω = Z i ω')
    (hfilt : ∀ i ω ω', π (i + 1) ω = π (i + 1) ω' → π i ω = π i ω')
    (hbdd : ∀ i ω, Z (i + 1) ω - Z i ω ∈ Set.Icc (-(c i)) (c i))
    (hmart : ∀ i k, fibreMass w (π i) k ≠ 0 →
      wmean (fibreWeight w (π i) k) (fun ω => Z (i + 1) ω - Z i ω) = 0)
    {n : ℕ} {t : ℝ} (ht : 0 < t) (hS : 0 < ∑ i ∈ Finset.range n, (c i) ^ 2) :
    wprob w ((univ : Finset Ω).filter fun ω => t ≤ Z n ω - Z 0 ω)
      ≤ Real.exp (-(t ^ 2) / (2 * ∑ i ∈ Finset.range n, (c i) ^ 2)) := by
  classical
  set S : ℝ := ∑ i ∈ Finset.range n, (c i) ^ 2 with hSdef
  set lam : ℝ := t / S with hlam
  have hlampos : 0 < lam := by
    rw [hlam]
    positivity
  -- Markov
  have hmark : wprob w ((univ : Finset Ω).filter fun ω => t ≤ Z n ω - Z 0 ω)
      * Real.exp (lam * t) ≤ wmean w (fun ω => Real.exp (lam * (Z n ω - Z 0 ω))) := by
    rw [wprob, Finset.sum_mul, wmean]
    refine le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
    · intro ω hω
      rw [mem_filter] at hω
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hw ω)
      exact mul_le_mul_of_nonneg_left hω.2 (le_of_lt hlampos)
    · intro ω _ _
      exact mul_nonneg (hw ω) (Real.exp_pos _).le
  have hmgf := wmean_exp_martingale hw hsum π Z c hmeas hfilt hbdd hmart lam n
  -- the sum of squares of the ranges is `4S`
  have hfour : ∑ i ∈ Finset.range n, (2 * c i) ^ 2 = 4 * S := by
    rw [hSdef, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfour] at hmgf
  have hpos : (0 : ℝ) < Real.exp (lam * t) := Real.exp_pos _
  have hkey : wprob w ((univ : Finset Ω).filter fun ω => t ≤ Z n ω - Z 0 ω)
      * Real.exp (lam * t) ≤ Real.exp (lam ^ 2 * (4 * S) / 8) := le_trans hmark hmgf
  rw [← le_div_iff₀ hpos] at hkey
  refine le_trans hkey (le_of_eq ?_)
  rw [← Real.exp_sub]
  congr 1
  rw [hlam]
  field_simp
  ring


/-- **Theorem 9.2.7**, the all-ones case of Azuma: for a martingale with unit increments,

    P(Z_n - Z_0 ≥ λ√n) ≤ e^{-λ²/2}. -/
theorem wprob_martingale_ge_sqrt_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (π : ℕ → Ω → K) (Z : ℕ → Ω → ℝ)
    (hmeas : ∀ i ω ω', π i ω = π i ω' → Z i ω = Z i ω')
    (hfilt : ∀ i ω ω', π (i + 1) ω = π (i + 1) ω' → π i ω = π i ω')
    (hbdd : ∀ i ω, Z (i + 1) ω - Z i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmart : ∀ i k, fibreMass w (π i) k ≠ 0 →
      wmean (fibreWeight w (π i) k) (fun ω => Z (i + 1) ω - Z i ω) = 0)
    {n : ℕ} {lam : ℝ} (hlam : 0 < lam) (hn : 0 < n) :
    wprob w ((univ : Finset Ω).filter fun ω => lam * Real.sqrt n ≤ Z n ω - Z 0 ω)
      ≤ Real.exp (-(lam ^ 2) / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : (0 : ℝ) < ∑ _i ∈ Finset.range n, (1 : ℝ) ^ 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_pow, mul_one]
    exact hnR
  have ht : 0 < lam * Real.sqrt n := by
    have : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
    positivity
  have hmain := wprob_martingale_ge_le hw hsum π Z (fun _ => 1) hmeas hfilt hbdd hmart ht hS
  refine le_trans hmain (Real.exp_le_exp.mpr (le_of_eq ?_))
  have hsum1 : ∑ _i ∈ Finset.range n, (1 : ℝ) ^ 2 = (n : ℝ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_pow, mul_one]
  rw [hsum1, mul_pow, Real.sq_sqrt (le_of_lt hnR)]
  field_simp

end Martingale

end PMC
