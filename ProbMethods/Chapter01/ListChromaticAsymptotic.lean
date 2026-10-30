import ProbMethods.Chapter01.ListChromatic
import ProbMethods.Chapter01.PropertyBUpper
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# §1.4 — Corollary 1.4.4, `ch(K_{n,n}) = (1 + o(1)) log₂ n`

Zhao, *Probabilistic Methods in Combinatorics*, Corollary 1.4.4. The list chromatic number of
`K_{n,n}` is `log₂ n` to leading order. Both bounds are already in this development, and the
corollary is the statement that they meet.

`PMC.listChromaticBipartite n` is the least `k` for which `K_{n,n}` is `k`-choosable; it is
well defined because `K_{n,n}` is `2n`-choosable (give every vertex its own colours), so the
set of admissible `k` is nonempty.

## The route

* **Upper bound, from Theorem 1.4.2** (`PMC.completeBipartiteChoosable_of_lt_two_pow`):
  `n < 2^{k-1}` implies `k`-choosable, so `listChromaticBipartite n ≤ ⌈log₂ n⌉ + 1`.
* **Lower bound, from Theorem 1.4.3 and Theorem 1.3.3.** `PMC.not_completeBipartiteChoosable_of_not_twoColorable`
  turns a non-2-colourable `k`-uniform hypergraph with `n` edges into a failure of
  `k`-choosability. Theorem 1.3.3 (task #56, `PMC.exists_not_twoColorable_card_le`) supplies one
  with at most `2k²2^k` edges, and edges may be *added* to a non-2-colourable hypergraph without
  making it 2-colourable — there are `C(k², k) ≫ 2k²2^k` available `k`-subsets of `[k²]`, so it
  can be padded to exactly `n` edges whenever `n ≥ 2k²2^k`. Hence
  `listChromaticBipartite n ≥ k + 1` for every `k` with `2k²2^k ≤ n`, i.e.
  `≥ log₂ n - 2log₂ k - O(1) = (1 - o(1)) log₂ n`.

The two together give the limit. Note the shape: the corollary is `o(1)`-asymptotic, but neither
input is — the asymptotics are entirely in the final squeeze, which is why this is publishable
as one bounded task on top of #56.
-/

open Finset

namespace PMC

section ListChromaticAsymptotic

/-- The list chromatic number of `K_{n,n}`: the least number of colours per list that always
suffices.

Defined as an `sInf` so that it is total with no side condition; the set is nonempty for every
`n` by Theorem 1.4.2 (`PMC.completeBipartiteChoosable_of_lt_two_pow` at any `k` with
`n < 2^{k-1}`), which is what keeps the value meaningful rather than the `sInf`-of-empty
default. -/
noncomputable def listChromaticBipartite (n : ℕ) : ℕ :=
  sInf {k | CompleteBipartiteChoosable n k}

/-- Choosability only gets easier with longer lists: shrink each `k`-list to a `j`-subset. A
colour from the sublist lies in the list. -/
private theorem choosable_mono_listSize {n j k : ℕ} (hjk : j ≤ k)
    (h : CompleteBipartiteChoosable n j) : CompleteBipartiteChoosable n k := by
  intro L hL
  choose L' hsub hcard using fun v => exists_subset_card_eq (hjk.trans_eq (hL v).symm)
  obtain ⟨f, hf, hne⟩ := h L' hcard
  exact ⟨f, fun v => hsub v (hf v), hne⟩

/-- Choosability passes to smaller complete bipartite graphs: give the extra vertices the list
`range k`, apply choosability, and restrict the colouring along `Fin.castLE`. This takes the
place of padding a hypergraph up to exactly `n` edges. -/
private theorem choosable_mono_vertices {m n k : ℕ} (hmn : m ≤ n)
    (h : CompleteBipartiteChoosable n k) : CompleteBipartiteChoosable m k := by
  intro L hL
  obtain ⟨L', hL'l, hL'r, hL'⟩ :
      ∃ L' : Fin n ⊕ Fin n → Finset ℕ,
        (∀ i : Fin m, L' (Sum.inl (Fin.castLE hmn i)) = L (Sum.inl i)) ∧
        (∀ i : Fin m, L' (Sum.inr (Fin.castLE hmn i)) = L (Sum.inr i)) ∧
        ∀ v, #(L' v) = k := by
    refine ⟨Sum.elim (fun i => if hi : (i : ℕ) < m then L (Sum.inl ⟨i, hi⟩) else range k)
      (fun i => if hi : (i : ℕ) < m then L (Sum.inr ⟨i, hi⟩) else range k),
      fun i => dif_pos i.2, fun i => dif_pos i.2, ?_⟩
    rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> split_ifs
    · exact hL _
    · exact card_range k
    · exact hL _
    · exact card_range k
  obtain ⟨f, hf, hne⟩ := h L' hL'
  refine ⟨Sum.elim (fun i => f (Sum.inl (Fin.castLE hmn i)))
    (fun i => f (Sum.inr (Fin.castLE hmn i))), ?_, fun i j => hne _ _⟩
  rintro (i | i)
  · exact hL'l i ▸ hf (Sum.inl (Fin.castLE hmn i))
  · exact hL'r i ▸ hf (Sum.inr (Fin.castLE hmn i))

/-- Theorem 1.4.2 at the first `k` it reaches: `n < 2 ^ (Nat.log 2 n + 1)`. -/
private theorem choosable_natLog_add_two (n : ℕ) :
    CompleteBipartiteChoosable n (Nat.log 2 n + 2) :=
  completeBipartiteChoosable_of_lt_two_pow (Nat.lt_pow_succ_log_self one_lt_two n)

/-- The upper bound in natural numbers. -/
private theorem listChromaticBipartite_le_natLog (n : ℕ) :
    listChromaticBipartite n ≤ Nat.log 2 n + 2 :=
  Nat.sInf_le (choosable_natLog_add_two n)

/-- The lower bound: `listChromaticBipartite n ≥ k + 1` whenever `2 k² 2^k ≤ n`, given
non-2-colourable `k`-uniform hypergraphs with at most `2 k² 2^k` edges. -/
private theorem lt_listChromaticBipartite_of_le
    (h : ∀ k : ℕ, 2 ≤ k → ∃ E : Finset (Finset (Fin (k * k))),
      (∀ e ∈ E, #e = k) ∧ #E ≤ 2 * (k * k) * 2 ^ k ∧ ¬ TwoColorable E)
    {n k : ℕ} (hk : 2 ≤ k) (hn : 2 * (k * k) * 2 ^ k ≤ n) : k < listChromaticBipartite n := by
  by_contra hle
  have hmem : CompleteBipartiteChoosable n (listChromaticBipartite n) :=
    Nat.sInf_mem (s := {k | CompleteBipartiteChoosable n k}) ⟨_, choosable_natLog_add_two n⟩
  obtain ⟨E, hEk, hEcard, hE⟩ := h k hk
  exact not_completeBipartiteChoosable_of_not_twoColorable hEk rfl hE
    (choosable_mono_vertices (hEcard.trans hn) (choosable_mono_listSize (not_lt.1 hle) hmem))

/-- From `L = 16` on, `L` leaves room for twice its own logarithm and a constant. -/
private theorem two_mul_natLog_add_five_le {L : ℕ} (hL : 16 ≤ L) : 2 * Nat.log 2 L + 5 ≤ L := by
  have hpow : ∀ a, 4 ≤ a → 2 * a + 5 ≤ 2 ^ a := by
    intro a ha
    induction a, ha using Nat.le_induction with
    | base => norm_num
    | succ a _ ih => rw [pow_succ]; omega
  have ha : 4 ≤ Nat.log 2 L := Nat.le_log_of_pow_le one_lt_two (by simpa using hL)
  exact (hpow _ ha).trans (Nat.pow_log_le_self 2 (by omega))

/-- The lower bound with `k = L - 2 log₂ L - 3` for `L = Nat.log 2 n`: since
`k ≤ L < 2 ^ (log₂ L + 1)`, this `k` satisfies `2 k² 2^k ≤ 2^L ≤ n`. -/
private theorem natLog_le_listChromaticBipartite_add
    (h : ∀ k : ℕ, 2 ≤ k → ∃ E : Finset (Finset (Fin (k * k))),
      (∀ e ∈ E, #e = k) ∧ #E ≤ 2 * (k * k) * 2 ^ k ∧ ¬ TwoColorable E)
    {n : ℕ} (hn : 2 ^ 16 ≤ n) :
    Nat.log 2 n ≤ listChromaticBipartite n + 2 * Nat.log 2 (Nat.log 2 n) + 2 := by
  have hL16 : 16 ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two hn
  have haL := two_mul_natLog_add_five_le hL16
  have hLlt : Nat.log 2 n < 2 ^ (Nat.log 2 (Nat.log 2 n) + 1) :=
    Nat.lt_pow_succ_log_self one_lt_two _
  obtain ⟨k, hk⟩ : ∃ k, Nat.log 2 n = k + (2 * Nat.log 2 (Nat.log 2 n) + 3) :=
    ⟨Nat.log 2 n - (2 * Nat.log 2 (Nat.log 2 n) + 3), by omega⟩
  have hkpow : k ≤ 2 ^ (Nat.log 2 (Nat.log 2 n) + 1) := by omega
  have hbound : 2 * (k * k) * 2 ^ k ≤ n := by
    calc 2 * (k * k) * 2 ^ k
        ≤ 2 * (2 ^ (Nat.log 2 (Nat.log 2 n) + 1) * 2 ^ (Nat.log 2 (Nat.log 2 n) + 1)) * 2 ^ k := by
          gcongr
      _ = 2 ^ (k + (2 * Nat.log 2 (Nat.log 2 n) + 3)) := by ring
      _ = 2 ^ Nat.log 2 n := by rw [← hk]
      _ ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hlt := lt_listChromaticBipartite_of_le h (by omega) hbound
  omega

/-- `log₂ n` is less than `Nat.log 2 n + 1`. -/
private theorem logb_lt_natLog_add_one {n : ℕ} (hn : 0 < n) :
    Real.logb 2 n < Nat.log 2 n + 1 := by
  rw [Real.logb_lt_iff_lt_rpow one_lt_two (by exact_mod_cast hn)]
  have hlt : (n : ℝ) < 2 ^ (Nat.log 2 n + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two n
  have hcast : (Nat.log 2 n : ℝ) + 1 = ((Nat.log 2 n + 1 : ℕ) : ℝ) := by push_cast; rfl
  rwa [hcast, Real.rpow_natCast]

/-- `Nat.log 2 n` is at most `log₂ n`. -/
private theorem natLog_le_logb_two (n : ℕ) : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by
  simpa using Real.natLog_le_logb n 2

/-- The real-variable limit behind the lower bound. -/
private theorem tendsto_sub_logb_div :
    Filter.Tendsto (fun y : ℝ => (y - 2 * Real.logb 2 y - 3) / y) Filter.atTop (nhds 1) := by
  have hlog : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Filter.Tendsto (fun y : ℝ => 3 / y) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have hlim : Filter.Tendsto (fun y : ℝ => 1 - 2 * (Real.log y / y / Real.log 2) - 3 / y)
      Filter.atTop (nhds (1 - 2 * (0 / Real.log 2) - 0)) :=
    (tendsto_const_nhds.sub ((hlog.div_const _).const_mul 2)).sub hinv
  rw [zero_div, mul_zero, sub_zero, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with y hy
  rw [Real.logb]
  field_simp

/-- The real-variable limit behind the upper bound. -/
private theorem tendsto_add_two_div :
    Filter.Tendsto (fun y : ℝ => (y + 2) / y) Filter.atTop (nhds 1) := by
  have hinv : Filter.Tendsto (fun y : ℝ => 2 / y) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have hlim : Filter.Tendsto (fun y : ℝ => 1 + 2 / y) Filter.atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hinv
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with y hy
  field_simp

/-- The squeeze, with the bound of Theorem 1.3.3 as an explicit hypothesis. Both bounds sit
within `O(log₂ log₂ n)` of `log₂ n`, and only the eventual behaviour of the ratio matters. -/
theorem tendsto_of_exists_not_twoColorable
    (h : ∀ k : ℕ, 2 ≤ k → ∃ E : Finset (Finset (Fin (k * k))),
      (∀ e ∈ E, #e = k) ∧ #E ≤ 2 * (k * k) * 2 ^ k ∧ ¬ TwoColorable E) :
    Filter.Tendsto (fun n => (listChromaticBipartite n : ℝ) / Real.logb 2 n)
      Filter.atTop (nhds 1) := by
  have hx : Filter.Tendsto (fun n : ℕ => Real.logb 2 n) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_sub_logb_div.comp hx)
    (tendsto_add_two_div.comp hx) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (2 ^ 16), hx.eventually_gt_atTop 0] with n hn hpos
    have hL16 : 16 ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two hn
    have hlower := natLog_le_listChromaticBipartite_add h hn
    have hlowerR : (Nat.log 2 n : ℝ) ≤ listChromaticBipartite n +
        2 * (Nat.log 2 (Nat.log 2 n) : ℕ) + 2 := by exact_mod_cast hlower
    have hlt := logb_lt_natLog_add_one (n := n) (by omega)
    have hlogL : Real.logb 2 (Nat.log 2 n) ≤ Real.logb 2 (Real.logb 2 n) :=
      Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast (by omega : 0 < Nat.log 2 n))
        (natLog_le_logb_two n)
    have haL := natLog_le_logb_two (Nat.log 2 n)
    rw [Function.comp_apply]
    gcongr
    linarith
  · filter_upwards [hx.eventually_gt_atTop 0] with n hpos
    have hupper : (listChromaticBipartite n : ℝ) ≤ Nat.log 2 n + 2 := by
      exact_mod_cast listChromaticBipartite_le_natLog n
    have hlog := natLog_le_logb_two n
    rw [Function.comp_apply]
    gcongr
    linarith

/-- The Weierstrass product estimate, by induction on the number of factors: with `L = k(k-1)`,
`∏_{i<j} (k² - i) · (2L - j(j-1)) ≤ ∏_{i<j} 2(s - i) · 2L` whenever `2s ≥ k²` and `j ≤ k`. -/
private lemma descFactorial_weierstrass {k s : ℕ} (hk : 2 ≤ k) (hs : k * k ≤ 2 * s) :
    ∀ j ≤ k, ((k * k).descFactorial j : ℤ) * (2 * (k * (k - 1)) - j * (j - 1)) ≤
      2 ^ j * s.descFactorial j * (2 * (k * (k - 1))) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp
  | succ j ih =>
    intro hj
    have hjk : j < k := hj
    have ih := ih hjk.le
    have hk2 : 2 * k ≤ k * k := Nat.mul_le_mul_right k hk
    have hjv : j ≤ k * k := by omega
    have hjs : j ≤ s := by omega
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
    push_cast [Nat.cast_sub hjv, Nat.cast_sub hjs]
    have hB0 : (0 : ℤ) ≤ ((k * k).descFactorial j : ℤ) := Int.natCast_nonneg _
    have hS0 : (0 : ℤ) ≤ (s.descFactorial j : ℤ) := Int.natCast_nonneg _
    have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    have hjj : (j : ℤ) ≤ j * j := by exact_mod_cast Nat.le_mul_self j
    have hjkZ : (j : ℤ) + 1 ≤ k := by exact_mod_cast hjk
    have hsZ : (k : ℤ) * k ≤ 2 * s := by exact_mod_cast hs
    have hk2Z : 2 * (k : ℤ) ≤ k * k := by exact_mod_cast hk2
    generalize ((k * k).descFactorial j : ℤ) = B at ih hB0 ⊢
    generalize (s.descFactorial j : ℤ) = S at ih hS0 ⊢
    have hL0 : (0 : ℤ) ≤ 2 * ((k : ℤ) * (k - 1)) :=
      Int.mul_nonneg (by omega) (Int.mul_nonneg (by omega) (by omega))
    have hA0 : (0 : ℤ) ≤ 2 ^ j * S * (2 * ((k : ℤ) * (k - 1))) :=
      Int.mul_nonneg (Int.mul_nonneg (Int.pow_nonneg (by omega)) hS0) hL0
    have hfac : (0 : ℤ) ≤ (k : ℤ) * k - 2 * j := by omega
    have hstep : ((k : ℤ) * k - j) * (2 * ((k : ℤ) * (k - 1)) - j * (j - 1) - 2 * j) ≤
        (2 * ((k : ℤ) * (k - 1)) - j * (j - 1)) * ((k : ℤ) * k - 2 * j) := by
      have hd : (0 : ℤ) ≤ j * (2 * ((k : ℤ) - j) + (j * j - j)) :=
        Int.mul_nonneg hj0 (by omega)
      grind
    calc ((k : ℤ) * k - j) * B * (2 * ((k : ℤ) * (k - 1)) - (j + 1) * (j + 1 - 1))
        = B * (((k : ℤ) * k - j) * (2 * ((k : ℤ) * (k - 1)) - j * (j - 1) - 2 * j)) := by grind
      _ ≤ B * ((2 * ((k : ℤ) * (k - 1)) - j * (j - 1)) * ((k : ℤ) * k - 2 * j)) :=
          Int.mul_le_mul_of_nonneg_left hstep hB0
      _ = (B * (2 * ((k : ℤ) * (k - 1)) - j * (j - 1))) * ((k : ℤ) * k - 2 * j) := by grind
      _ ≤ (2 ^ j * S * (2 * ((k : ℤ) * (k - 1)))) * ((k : ℤ) * k - 2 * j) :=
          Int.mul_le_mul_of_nonneg_right ih hfac
      _ ≤ (2 ^ j * S * (2 * ((k : ℤ) * (k - 1)))) * (2 * ((s : ℤ) - j)) :=
          Int.mul_le_mul_of_nonneg_left (by omega) hA0
      _ = 2 ^ (j + 1) * (((s : ℤ) - j) * S) * (2 * ((k : ℤ) * (k - 1))) := by grind

/-- A set of at least half of `k²` vertices contains at least a `2^{-k-1}` fraction of the
`k`-subsets of `[k²]`. -/
private lemma choose_le_choose_mul_two_pow {k s : ℕ} (hk : 2 ≤ k) (hs : k * k ≤ 2 * s) :
    (k * k).choose k ≤ s.choose k * 2 ^ (k + 1) := by
  have h := descFactorial_weierstrass hk hs k le_rfl
  have hL : (0 : ℤ) < (k : ℤ) * (k - 1) := Int.mul_pos (by omega) (by omega)
  have hd : (k * k).descFactorial k ≤ s.descFactorial k * 2 ^ (k + 1) := by
    have h' : ((k * k).descFactorial k : ℤ) ≤ s.descFactorial k * 2 ^ (k + 1) := by
      refine Int.le_of_mul_le_mul_right ?_ hL
      calc ((k * k).descFactorial k : ℤ) * ((k : ℤ) * (k - 1))
          = ((k * k).descFactorial k : ℤ) * (2 * ((k : ℤ) * (k - 1)) - k * (k - 1)) := by grind
        _ ≤ 2 ^ k * s.descFactorial k * (2 * ((k : ℤ) * (k - 1))) := h
        _ = s.descFactorial k * 2 ^ (k + 1) * ((k : ℤ) * (k - 1)) := by grind
    exact_mod_cast h'
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.mul_assoc] at hd
  exact Nat.le_of_mul_le_mul_left hd (Nat.factorial_pos k)

/-- Bernoulli's inequality in the form `x ^ n (x + n) ≤ x (x + 1) ^ n`. -/
private lemma pow_mul_add_le_mul_succ_pow (x n : ℕ) :
    x ^ n * (x + n) ≤ x * (x + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc x ^ (n + 1) * (x + (n + 1))
        ≤ x ^ (n + 1) * (x + (n + 1)) + x ^ n * n := Nat.le_add_right _ _
      _ = (x + 1) * (x ^ n * (x + n)) := by grind
      _ ≤ (x + 1) * (x * (x + 1) ^ n) := Nat.mul_le_mul_left _ ih
      _ = x * (x + 1) ^ (n + 1) := by grind

/-- If `g ≤ (1 - 1/D) N` with `D > 0`, `N > 0` and `v > 0`, then `2 ^ v g ^ (D v) < N ^ (D v)`:
this is `(1 - 1/D) ^ D < 1/2`. -/
private lemma two_pow_mul_pow_lt {g N D v : ℕ} (hN : 0 < N) (hD : 0 < D) (hv : v ≠ 0)
    (hg : g * D + N ≤ N * D) : 2 ^ v * g ^ (D * v) < N ^ (D * v) := by
  obtain ⟨x, rfl⟩ : ∃ x, D = x + 1 := ⟨D - 1, by omega⟩
  have hgx : g * (x + 1) ≤ N * x := by
    rw [Nat.mul_add_one N x] at hg
    omega
  have hbern : 2 * x ^ (x + 1) < (x + 1) ^ (x + 1) := by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have h := pow_mul_add_le_mul_succ_pow x (x + 1)
      have hxx : 0 < x ^ (x + 1) := pow_pos hx _
      have heq : x ^ (x + 1) * (x + (x + 1)) = x * (2 * x ^ (x + 1)) + x ^ (x + 1) := by grind
      exact Nat.lt_of_mul_lt_mul_left (a := x) (by omega)
  have hbase : 2 * g ^ (x + 1) < N ^ (x + 1) := by
    have hpow : g ^ (x + 1) * (x + 1) ^ (x + 1) ≤ N ^ (x + 1) * x ^ (x + 1) := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left hgx _
    refine Nat.lt_of_mul_lt_mul_right (a := (x + 1) ^ (x + 1)) ?_
    calc 2 * g ^ (x + 1) * (x + 1) ^ (x + 1)
        = 2 * (g ^ (x + 1) * (x + 1) ^ (x + 1)) := Nat.mul_assoc _ _ _
      _ ≤ 2 * (N ^ (x + 1) * x ^ (x + 1)) := Nat.mul_le_mul_left _ hpow
      _ = N ^ (x + 1) * (2 * x ^ (x + 1)) := by grind
      _ < N ^ (x + 1) * (x + 1) ^ (x + 1) := Nat.mul_lt_mul_of_pos_left hbern (pow_pos hN _)
  calc 2 ^ v * g ^ ((x + 1) * v) = (2 * g ^ (x + 1)) ^ v := by rw [mul_pow, pow_mul]
    _ < (N ^ (x + 1)) ^ v := Nat.pow_lt_pow_left hbase hv
    _ = N ^ ((x + 1) * v) := by rw [pow_mul]

/-- The union bound over a finite family: if each `G c` has `#ι * #(G c) ^ m < #P ^ m`, then
some `m`-tuple from `P` leaves every `G c`. -/
private lemma exists_tuple_forall_exists_notMem {ι α : Type*} [Fintype ι] [Nonempty ι]
    (P : Finset α) (G : ι → Finset α) (m : ℕ)
    (h : ∀ c, Fintype.card ι * #(G c) ^ m < #P ^ m) :
    ∃ f : Fin m → α, (∀ j, f j ∈ P) ∧ ∀ c, ∃ j, f j ∉ G c := by
  classical
  have hlt : #(univ.biUnion fun c => Fintype.piFinset fun _ : Fin m => G c) <
      #(Fintype.piFinset fun _ : Fin m => P) := by
    refine Nat.lt_of_mul_lt_mul_left (a := Fintype.card ι) ?_
    calc Fintype.card ι * #(univ.biUnion fun c => Fintype.piFinset fun _ : Fin m => G c)
        ≤ Fintype.card ι * ∑ c, #(G c) ^ m := by
          refine Nat.mul_le_mul_left _ (card_biUnion_le.trans_eq ?_)
          simp
      _ = ∑ c, Fintype.card ι * #(G c) ^ m := by
          simp only [← smul_eq_mul, sum_nsmul]
      _ < ∑ _c : ι, #P ^ m := sum_lt_sum_of_nonempty univ_nonempty fun c _ => h c
      _ = Fintype.card ι * #(Fintype.piFinset fun _ : Fin m => P) := by
          simp [card_univ]
  obtain ⟨f, hfP, hf⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨f, Fintype.mem_piFinset.1 hfP, fun c => ?_⟩
  by_contra hc
  exact hf (mem_biUnion.2 ⟨c, mem_univ c, Fintype.mem_piFinset.2 (not_exists_not.1 hc)⟩)

/-- **Theorem 1.3.3**, with the proof from task #56 (open PR #72). This task's pinned commit
still has `PMC.exists_not_twoColorable_card_le` as a placeholder, and this project's gate refuses
a proof that inherits one, so the argument is carried here to keep the corollary unconditional.
Once that PR lands, this and the five helpers above can give way to that lemma. -/
private theorem exists_not_twoColorable_card_le_aux {k : ℕ} (hk : 2 ≤ k) :
    ∃ E : Finset (Finset (Fin (k * k))),
      (∀ e ∈ E, #e = k) ∧ #E ≤ 2 * (k * k) * 2 ^ k ∧ ¬ TwoColorable E := by
  classical
  set P : Finset (Finset (Fin (k * k))) := powersetCard k univ with hP
  have hPcard : #P = (k * k).choose k := by simp [hP]
  have hNpos : 0 < #P := by
    rw [hPcard]
    exact Nat.choose_pos (Nat.le_mul_self k)
  have hv : k * k ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  -- `G c` is the family of `k`-sets that are not monochromatic under `c`.
  let G : (Fin (k * k) → Bool) → Finset (Finset (Fin (k * k))) :=
    fun c => {e ∈ P | ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v}
  have hG : ∀ c, #(G c) * 2 ^ (k + 1) + #P ≤ #P * 2 ^ (k + 1) := by
    intro c
    -- The larger colour class holds at least half of the vertices.
    obtain ⟨b, hb⟩ : ∃ b, k * k ≤ 2 * #{x | c x = b} := by
      have htot : #{x | c x = true} + #{x | c x = false} = k * k := by
        simp only [← Bool.not_eq_true, card_filter_add_card_filter_not]
        simp
      by_cases htrue : k * k ≤ 2 * #{x | c x = true}
      · exact ⟨true, htrue⟩
      · exact ⟨false, by omega⟩
    set S : Finset (Fin (k * k)) := {x | c x = b} with hS
    have hmono : powersetCard k S ⊆ P \ G c := by
      intro e he
      obtain ⟨heS, hek⟩ := mem_powersetCard.1 he
      refine mem_sdiff.2 ⟨mem_powersetCard.2 ⟨subset_univ _, hek⟩, fun heG => ?_⟩
      obtain ⟨u, hu, v, hv', huv⟩ := (mem_filter.1 heG).2
      exact huv (((mem_filter.1 (heS hu)).2).trans (mem_filter.1 (heS hv')).2.symm)
    have hlow : (#S).choose k + #(G c) ≤ #P := by
      have hGP : G c ⊆ P := filter_subset _ _
      have h1 := card_le_card hmono
      rw [card_sdiff_of_subset hGP, card_powersetCard] at h1
      have h2 := card_le_card hGP
      omega
    have hch := choose_le_choose_mul_two_pow hk hb
    rw [← hPcard] at hch
    calc #(G c) * 2 ^ (k + 1) + #P
        ≤ #(G c) * 2 ^ (k + 1) + (#S).choose k * 2 ^ (k + 1) := Nat.add_le_add_left hch _
      _ = ((#S).choose k + #(G c)) * 2 ^ (k + 1) := by rw [Nat.add_mul, Nat.add_comm]
      _ ≤ #P * 2 ^ (k + 1) := Nat.mul_le_mul_right _ hlow
  have hcard : Fintype.card (Fin (k * k) → Bool) = 2 ^ (k * k) := by simp
  have hm : 2 * (k * k) * 2 ^ k = 2 ^ (k + 1) * (k * k) := by grind
  obtain ⟨f, hfP, hf⟩ := exists_tuple_forall_exists_notMem P G (2 * (k * k) * 2 ^ k) (fun c => by
    rw [hcard, hm]
    exact two_pow_mul_pow_lt hNpos (pow_pos (by omega) _) hv (hG c))
  refine ⟨univ.image f, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨j, -, rfl⟩ := mem_image.1 he
    exact (mem_powersetCard.1 (hfP j)).2
  · exact card_image_le.trans (by simp)
  · rintro ⟨c, hc⟩
    obtain ⟨j, hj⟩ := hf c
    exact hj (mem_filter.2 ⟨hfP j, hc _ (mem_image_of_mem f (mem_univ j))⟩)

/-- **Corollary 1.4.4.** `ch(K_{n,n}) / log₂ n → 1`. -/
theorem tendsto_listChromaticBipartite_div_logb :
    Filter.Tendsto (fun n => (listChromaticBipartite n : ℝ) / Real.logb 2 n)
      Filter.atTop (nhds 1) := by
  exact tendsto_of_exists_not_twoColorable fun _ hk => exists_not_twoColorable_card_le_aux hk

end ListChromaticAsymptotic

end PMC
