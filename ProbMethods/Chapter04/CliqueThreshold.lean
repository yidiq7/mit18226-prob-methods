import ProbMethods.Chapter04.FirstMoment
import ProbMethods.Chapter04.TriangleThreshold

/-!
# §4.2, §4.4 — the first-moment half of the clique thresholds

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 4.2.5 and Theorem 4.4.2(a). Both are
Markov's inequality applied to the number of `k`-cliques, whose mean is
`C(n,k) p^{C(k,2)}` (`PMC.sum_bweight_mul_card_cliqueSets`):

* Theorem 4.2.5, first half: `p ≪ n^{-2/3}` ⟹ `G(n,p)` has no `K₄` whp, because
  `E[#K₄] = C(n,4)p⁶ ≤ n⁴p⁶/24 → 0`;
* Theorem 4.4.2(a): `f(n,k) = C(n,k)2^{-C(k,2)} → 0` ⟹ `ω(G(n,1/2)) < k` whp.

Both are instances of one statement, `PMC.tendsto_probHasClique_zero`: the probability of
containing a `k`-clique vanishes as soon as the expected number of them does. The
*second*-moment halves are different in each case and are not proved here — 4.4.2(b) needs
`Δ*` for cliques, whose overlap analysis is the `k`-vertex analogue of what
`PMC.wvar_card_triangles_le'` does for triangles.

Nothing here is asymptotic beyond the limit itself: the explicit bound
`PMC.probHasClique_le` is what carries the content, exactly as in §4.1's threshold.
-/

open Finset Filter

namespace PMC

section CliqueThreshold

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edge set contains a `k`-clique. Written as a bounded existential so that it is
decidable, hence usable in a `Finset.filter`; `PMC.HasTriangle` is the case `k = 3`. -/
def HasClique (k : ℕ) (E : Finset (Sym2 V)) : Prop :=
  ∃ t ∈ powersetCard k (univ : Finset V), spannedEdges t ⊆ E

instance decidableHasClique (k : ℕ) : DecidablePred (HasClique (V := V) k) :=
  fun E => decidable_of_iff (∃ t ∈ powersetCard k (univ : Finset V), spannedEdges t ⊆ E) Iff.rfl

lemma hasClique_three_iff {E : Finset (Sym2 V)} : HasClique 3 E ↔ HasTriangle E := Iff.rfl

lemma hasClique_iff_cliqueSets_nonempty {k : ℕ} {E : Finset (Sym2 V)} :
    HasClique k E ↔ (cliqueSets k E).Nonempty := by
  simp [HasClique, cliqueSets, Finset.filter_nonempty_iff]

/-- The `G(n, p)` probability of containing a `k`-clique. -/
noncomputable def probHasClique (n k : ℕ) (p : ℝ) : ℝ :=
  ∑ E ∈ (univ : Finset (Finset (Sym2 (Fin n)))).filter fun E => HasClique k E, bweight p E

lemma probHasClique_nonneg (n k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ probHasClique n k p :=
  Finset.sum_nonneg fun E _ => bweight_nonneg hp0 hp1 E

/-- **Markov for `k`-cliques**: the chance of containing one is at most the expected number
of them, `C(n,k) p^{C(k,2)}`. -/
theorem probHasClique_le (n k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    probHasClique n k p ≤ (n.choose k : ℝ) * p ^ (k.choose 2) := by
  classical
  have hmean : wmean (bweight p) (fun E : Finset (Sym2 (Fin n)) => (#(cliqueSets k E) : ℝ))
      = (n.choose k : ℝ) * p ^ (k.choose 2) := by
    rw [wmean_eq_sum_powerset]
    have h := sum_bweight_mul_card_cliqueSets (V := Fin n) p k
    rwa [Fintype.card_fin] at h
  have hmark := wmarkov (bweight p) (fun E : Finset (Sym2 (Fin n)) => (#(cliqueSets k E) : ℝ))
    (fun E => bweight_nonneg hp0 hp1 E) (fun E => by positivity) (a := 1) one_pos
  rw [mul_one, hmean] at hmark
  refine le_trans (le_of_eq ?_) hmark
  rw [probHasClique]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext E
  simp only [mem_filter, mem_univ, true_and, hasClique_iff_cliqueSets_nonempty]
  rw [← Finset.card_pos, Nat.one_le_cast, Nat.succ_le_iff]

/-- **The first-moment half of both clique thresholds.** If the expected number of
`k`-cliques vanishes, so does the probability of containing one. -/
theorem tendsto_probHasClique_zero {k : ℕ → ℕ} {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n)
    (hp1 : ∀ n, p n ≤ 1)
    (h : Tendsto (fun n : ℕ => (n.choose (k n) : ℝ) * p n ^ ((k n).choose 2)) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => probHasClique n (k n) (p n)) atTop (nhds 0) :=
  squeeze_zero (fun n => probHasClique_nonneg n (k n) (hp0 n) (hp1 n))
    (fun n => probHasClique_le n (k n) (hp0 n) (hp1 n)) h

/-- **Theorem 4.2.5, first half.** If `n⁴p⁶ → 0` — that is, `p ≪ n^{-2/3}` — then `G(n,p)`
contains no `K₄` with probability `1 - o(1)`. -/
theorem tendsto_probHasClique_four_zero {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1)
    (h : Tendsto (fun n : ℕ => (n : ℝ) ^ 4 * p n ^ 6) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => probHasClique n 4 (p n)) atTop (nhds 0) := by
  refine tendsto_probHasClique_zero (k := fun _ => 4) hp0 hp1 ?_
  have hdiv : Tendsto (fun n : ℕ => (n : ℝ) ^ 4 * p n ^ 6 / 24) atTop (nhds 0) := by
    have := h.div_const 24
    rwa [zero_div] at this
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hdiv
  · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hp0 n) _)
  have hchoose : (n.choose 4 : ℝ) ≤ (n : ℝ) ^ 4 / 24 := by
    have hb := Nat.choose_le_pow_div (α := ℝ) 4 n
    rw [show ((Nat.factorial 4 : ℕ) : ℝ) = 24 from by simp [Nat.factorial]] at hb
    exact hb
  have hp6 : (0 : ℝ) ≤ p n ^ 6 := by positivity
  calc (n.choose 4 : ℝ) * p n ^ ((4 : ℕ).choose 2)
      = (n.choose 4 : ℝ) * p n ^ 6 := by
          rw [show Nat.choose 4 2 = 6 from by decide]
    _ ≤ ((n : ℝ) ^ 4 / 24) * p n ^ 6 := mul_le_mul_of_nonneg_right hchoose hp6
    _ = (n : ℝ) ^ 4 * p n ^ 6 / 24 := by ring

/-- **Theorem 4.4.2(a).** If `f(n,k) = C(n,k) 2^{-C(k,2)} → 0` then the clique number of
`G(n, 1/2)` is less than `k` with probability `1 - o(1)`. -/
theorem tendsto_probHasClique_half_zero {k : ℕ → ℕ}
    (h : Tendsto (fun n : ℕ => (n.choose (k n) : ℝ) * (1 / 2 : ℝ) ^ ((k n).choose 2)) atTop
      (nhds 0)) :
    Tendsto (fun n : ℕ => probHasClique n (k n) (1 / 2 : ℝ)) atTop (nhds 0) :=
  tendsto_probHasClique_zero (fun _ => by norm_num) (fun _ => by norm_num) h

end CliqueThreshold

end PMC
