import ProbMethods.Chapter09.BoundedDifferences
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# §9.3 — the chromatic number of a random graph is concentrated

Theorem 9.3.1 (Shamir–Spencer 1987): for every `λ ≥ 0`,

    P(|χ(G(n,p)) - E χ| ≥ λ √(n-1)) ≤ 2 e^{-2λ²}.

**This statement is finite**, with no `o(1)` anywhere, and it is the flagship application of
§9.1: as the notes put it, one proves concentration around the mean *without even knowing
where the mean is*.

The proof is Theorem 9.1.3 applied to the **vertex-exposure** decomposition. The notes take
the sample space to be `Ω₂ × ⋯ × Ωₙ` with `Ωᵢ = {0,1}^{i-1}`, whose factors have different
sizes; here it is the uniform product `Fin n → (Fin n → Bool)` with the edge `{a,b}`, `a < b`,
controlled by coordinate `b` (`PMC.graphOf`). Coordinate `0` then controls no edge at all, so
its bounded-difference constant is `0` and `∑ cᵢ² = n - 1` — which is exactly how the notes'
`√(n-1)` appears. The general-constants form of the inequality (their Theorem 9.1.3) is what
makes that work.

The graph-theoretic input is `PMC.chromNat_le_succ_of_agree_off`: changing the edges at one
vertex changes the chromatic number by at most one, because a proper colouring of the old
graph becomes one of the new graph after giving that vertex a fresh colour.
-/

open Finset

namespace PMC

section ChromaticConcentration

variable {n : ℕ}

/-- The chromatic number as a natural number: the least `k` for which the graph is
`k`-colourable. A `Fintype` graph is always `card V`-colourable, so the minimum exists. -/
noncomputable def chromNat (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact Nat.find (p := fun k => G.Colorable k) ⟨Fintype.card (Fin n), G.colorable_of_fintype⟩

lemma colorable_chromNat (G : SimpleGraph (Fin n)) : G.Colorable (chromNat G) := by
  classical
  exact Nat.find_spec (p := fun k => G.Colorable k)
    ⟨Fintype.card (Fin n), G.colorable_of_fintype⟩

lemma chromNat_le_of_colorable {G : SimpleGraph (Fin n)} {k : ℕ} (h : G.Colorable k) :
    chromNat G ≤ k := by
  classical
  exact Nat.find_le (p := fun k => G.Colorable k) h

/-- **A proper colouring survives a change at one vertex, at the cost of one extra colour.**
Give the changed vertex a brand-new colour; every other pair of adjacent vertices was already
adjacent in the old graph. -/
lemma colorable_succ_of_agree_off {G G' : SimpleGraph (Fin n)} {v : Fin n}
    (hagree : ∀ a b : Fin n, a ≠ v → b ≠ v → (G.Adj a b ↔ G'.Adj a b)) {k : ℕ}
    (hG : G.Colorable k) : G'.Colorable (k + 1) := by
  classical
  obtain ⟨C⟩ := hG
  refine ⟨SimpleGraph.Coloring.mk
    (fun u => if u = v then (Fin.last k) else (C u).castSucc) ?_⟩
  intro a b hab
  have hne : a ≠ b := hab.ne
  by_cases ha : a = v
  · subst ha
    have hbv : b ≠ a := fun h => hne h.symm
    rw [if_pos rfl, if_neg hbv]
    exact fun hcon => absurd hcon.symm (Fin.castSucc_ne_last (C b))
  · by_cases hb : b = v
    · subst hb
      rw [if_pos rfl, if_neg ha]
      exact Fin.castSucc_ne_last (C a)
    · rw [if_neg ha, if_neg hb]
      have hGab : G.Adj a b := (hagree a b ha hb).mpr hab
      have := C.valid hGab
      exact fun hcon => this (Fin.castSucc_injective k hcon)

/-- **Changing the edges at one vertex changes the chromatic number by at most one.** -/
lemma chromNat_le_succ_of_agree_off {G G' : SimpleGraph (Fin n)} {v : Fin n}
    (hagree : ∀ a b : Fin n, a ≠ v → b ≠ v → (G.Adj a b ↔ G'.Adj a b)) :
    chromNat G' ≤ chromNat G + 1 :=
  chromNat_le_of_colorable (colorable_succ_of_agree_off hagree (colorable_chromNat G))

/-! ### The vertex-exposure encoding -/

/-- The graph on `Fin n` encoded by `x`: the edge `{a,b}` with `a < b` is controlled by
coordinate `b`, the larger endpoint. So coordinate `i` controls exactly the edges from `i`
down to smaller vertices — the notes' vertex exposure — and coordinate `0` controls none. -/
def graphOf (x : Fin n → (Fin n → Bool)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => a < b ∧ x b a = true

lemma graphOf_adj (x : Fin n → (Fin n → Bool)) (a b : Fin n) :
    (graphOf x).Adj a b ↔ a ≠ b ∧ ((a < b ∧ x b a = true) ∨ (b < a ∧ x a b = true)) := by
  rw [graphOf, SimpleGraph.fromRel_adj]

/-- Coordinates other than the one at a vertex do not affect the edges away from it. -/
lemma graphOf_agree_off {x y : Fin n → (Fin n → Bool)} {i : Fin n}
    (hxy : ∀ j, j ≠ i → x j = y j) (a b : Fin n) (ha : a ≠ i) (hb : b ≠ i) :
    ((graphOf x).Adj a b ↔ (graphOf y).Adj a b) := by
  rw [graphOf_adj, graphOf_adj, hxy a ha, hxy b hb]

/-- **Coordinate `0` controls no edge**, since an edge controlled by `b` needs a vertex below
`b`. So the graph does not depend on that coordinate at all, and its bounded-difference
constant is `0` — which is where the notes' `√(n-1)` rather than `√n` comes from. -/
lemma graphOf_eq_of_agree_off_zero [NeZero n] {x y : Fin n → (Fin n → Bool)}
    (hxy : ∀ j, j ≠ (0 : Fin n) → x j = y j) : graphOf x = graphOf y := by
  ext a b
  rw [graphOf_adj, graphOf_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, Or.inl ⟨h.1, by rw [← hxy b (by
        intro hcon
        rw [hcon] at h
        exact absurd h.1 (by simp))]; exact h.2⟩⟩
    · exact ⟨hne, Or.inr ⟨h.1, by rw [← hxy a (by
        intro hcon
        rw [hcon] at h
        exact absurd h.1 (by simp))]; exact h.2⟩⟩
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, Or.inl ⟨h.1, by rw [hxy b (by
        intro hcon
        rw [hcon] at h
        exact absurd h.1 (by simp))]; exact h.2⟩⟩
    · exact ⟨hne, Or.inr ⟨h.1, by rw [hxy a (by
        intro hcon
        rw [hcon] at h
        exact absurd h.1 (by simp))]; exact h.2⟩⟩

/-! ### Theorem 9.3.1 -/

/-- The chromatic number of the encoded graph, as a real-valued function on the product. -/
noncomputable def chromF (x : Fin n → (Fin n → Bool)) : ℝ := (chromNat (graphOf x) : ℝ)

/-- **Bounded differences for the chromatic number**: coordinate `0` costs nothing, every
other coordinate costs `1`. -/
lemma bddDiff_chromF [NeZero n] :
    BddDiff (chromF (n := n)) (fun i => if i = (0 : Fin n) then 0 else 1) := by
  intro i x y hxy
  show |chromF x - chromF y| ≤ (if i = (0 : Fin n) then (0 : ℝ) else 1)
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos rfl, chromF, chromF, graphOf_eq_of_agree_off_zero hxy, sub_self, abs_zero]
  · rw [if_neg h0]
    have hagree : ∀ a b : Fin n, a ≠ i → b ≠ i →
        ((graphOf x).Adj a b ↔ (graphOf y).Adj a b) :=
      fun a b ha hb => graphOf_agree_off hxy a b ha hb
    have h1 : chromNat (graphOf y) ≤ chromNat (graphOf x) + 1 :=
      chromNat_le_succ_of_agree_off hagree
    have h2 : chromNat (graphOf x) ≤ chromNat (graphOf y) + 1 :=
      chromNat_le_succ_of_agree_off (fun a b ha hb => (hagree a b ha hb).symm)
    have h1R : (chromNat (graphOf y) : ℝ) ≤ chromNat (graphOf x) + 1 := by exact_mod_cast h1
    have h2R : (chromNat (graphOf x) : ℝ) ≤ chromNat (graphOf y) + 1 := by exact_mod_cast h2
    rw [chromF, chromF, abs_le]
    exact ⟨by linarith, by linarith⟩

lemma sum_sq_chrom_const (n : ℕ) [NeZero n] :
    ∑ i : Fin n, (if i = (0 : Fin n) then (0 : ℝ) else 1) ^ 2 = (n : ℝ) - 1 := by
  have hterm : ∀ i : Fin n, (if i = (0 : Fin n) then (0 : ℝ) else 1) ^ 2
      = 1 - (if i = (0 : Fin n) then (1 : ℝ) else 0) := by
    intro i
    by_cases h : i = 0 <;> simp [h]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, Finset.sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  simp

/-- **Theorem 9.3.1 (Shamir–Spencer 1987).** The chromatic number of a random graph is
concentrated in a window of width `O(√n)` around its mean:

    P(|χ - E χ| ≥ λ √(n-1)) ≤ 2 e^{-2λ²},

and no knowledge of the mean is needed. Theorem 9.1.3 applied to the vertex-exposure
encoding, with the coordinate-`0` constant equal to `0` — which is exactly why the notes'
window is `√(n-1)` and not `√n`.

Hoeffding's lemma enters through `PMC.hoeffdingUnif_holds`, so the statement is
unconditional — as the notes state it. -/
theorem card_filter_chromF_le [NeZero n] (hn : 2 ≤ n)
    {lam : ℝ} (hlam : 0 < lam) :
    (#((univ : Finset (Fin n → (Fin n → Bool))).filter fun x =>
        lam * Real.sqrt ((n : ℝ) - 1) ≤ |chromF x - pAvg (chromF (n := n))|) : ℝ)
      ≤ 2 * ((Fintype.card (Fin n → Bool) : ℝ) ^ n * Real.exp (-(2 * lam ^ 2))) := by
  classical
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hsqrt : (0 : ℝ) < Real.sqrt ((n : ℝ) - 1) := Real.sqrt_pos.mpr hn1
  set t : ℝ := lam * Real.sqrt ((n : ℝ) - 1) with htdef
  have ht : 0 < t := by rw [htdef]; positivity
  have hS : (0 : ℝ) < ∑ i : Fin n, (if i = (0 : Fin n) then (0 : ℝ) else 1) ^ 2 := by
    rw [sum_sq_chrom_const n]
    exact hn1
  have hup := card_filter_ge_le (chromF (n := n))
    (fun i => if i = (0 : Fin n) then 0 else 1) bddDiff_chromF ht hS
  have hlo := card_filter_le_le (chromF (n := n))
    (fun i => if i = (0 : Fin n) then 0 else 1) bddDiff_chromF ht hS
  rw [sum_sq_chrom_const n] at hup hlo
  -- the exponent collapses
  have hexp : -(2 * t ^ 2) / ((n : ℝ) - 1) = -(2 * lam ^ 2) := by
    rw [htdef, mul_pow, Real.sq_sqrt (le_of_lt hn1)]
    field_simp
  rw [hexp] at hup hlo
  -- union bound over the two tails
  have hsub : ((univ : Finset (Fin n → (Fin n → Bool))).filter fun x =>
        t ≤ |chromF x - pAvg (chromF (n := n))|)
      ⊆ ((univ : Finset (Fin n → (Fin n → Bool))).filter fun x =>
          pAvg (chromF (n := n)) + t ≤ chromF x)
        ∪ ((univ : Finset (Fin n → (Fin n → Bool))).filter fun x =>
          chromF x ≤ pAvg (chromF (n := n)) - t) := by
    intro x hx
    rw [mem_filter] at hx
    rw [mem_union, mem_filter, mem_filter]
    rcases le_abs.mp hx.2 with h | h
    · exact Or.inl ⟨mem_univ _, by linarith⟩
    · exact Or.inr ⟨mem_univ _, by linarith⟩
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    ((univ : Finset (Fin n → (Fin n → Bool))).filter fun x =>
      pAvg (chromF (n := n)) + t ≤ chromF x)
    ((univ : Finset (Fin n → (Fin n → Bool))).filter fun x =>
      chromF x ≤ pAvg (chromF (n := n)) - t)
  have hle : (#((univ : Finset (Fin n → (Fin n → Bool))).filter fun x =>
        t ≤ |chromF x - pAvg (chromF (n := n))|) : ℝ)
      ≤ #((univ : Finset (Fin n → (Fin n → Bool))).filter fun x =>
          pAvg (chromF (n := n)) + t ≤ chromF x)
        + #((univ : Finset (Fin n → (Fin n → Bool))).filter fun x =>
          chromF x ≤ pAvg (chromF (n := n)) - t) := by
    have := le_trans hcard hunion
    exact_mod_cast this
  rw [htdef] at hle
  linarith

end ChromaticConcentration
