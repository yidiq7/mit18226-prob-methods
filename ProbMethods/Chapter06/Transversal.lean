import ProbMethods.Chapter06.ProductLLL

/-!
# §6.3 — Independent transversals (Theorem 6.3.1)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 6.3.1: a graph of maximum degree `Δ`
whose vertex set is partitioned into parts of size at least `2eΔ` has an independent set
containing one vertex from each part.

**Every probabilistic component is already proved.** What is missing is the graph
bookkeeping that feeds them to the local lemma. The four components:

* `PMC.exists_avoiding_of_lll` — the local lemma on a product sample space. Supply the
  events, the coordinate block each depends on, a probability bound `p` and a degree bound
  `d`; independence is discharged internally, so this proof never mentions `PMC.wprob`.
* `PMC.exists_enumeration` — trims the parts to size exactly `k` and enumerates each by
  `Fin k`, making the sample space the *uniform* product `Fin r → Fin k`. A transversal built
  from it is automatically a transversal of the original parts.
* `PMC.card_adj_pairs_le` — the ordered adjacent pairs starting in a set `S` number at most
  `#S · Δ`. With `S = Vᵢ ∪ V_j` of size `2k` this is the notes' `2kΔ`.
* `PMC.wprob_unifProd_coord` — fixing one coordinate has probability `1/k`; block
  independence multiplies it to `1/k²` for the two coordinates a bad event pins down.

## The intended proof

Index bad events by `c : Fin r × Fin r × Fin k × Fin k`, valid when `c.1 < c.2.1` and
`w c.1 c.2.2.1` is adjacent to `w c.2.1 c.2.2.2`; take

* `A c = {f | f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2}` and `C c = {c.1, c.2.1}` when valid,
* `A c = ∅` and `C c = ∅` otherwise.

Invalid indices cost nothing: an empty event is never violated, has probability `0`, and is
determined on the empty block, so it is disjoint from every other block. That is what lets
the index type be the whole product rather than a subtype of valid indices.

**`c.1 < c.2.1` is load-bearing twice.** It counts each cross-part edge once, keeping the
dependency degree at `2kΔ` rather than `4kΔ` — the latter would only prove the theorem for
parts of size `4eΔ`, which is weaker than 6.3.1. And it is what makes the degree injection
injective: send a neighbouring index `(i',j',a',b')` to the ordered pair
`(w i' a', w j' b')` when `i' ∈ {i,j}` and to `(w j' b', w i' a')` otherwise; a collision
would need both `(i,j,a,b)` and `(j,i,b,a)` to be indices, which `i < j` forbids.

## Errata in the source

The notes write the local-lemma condition as `e (1/k²)(2kΔ + 1) ≤ 1`. That is **false** for
`k = ⌈2eΔ⌉` at small `Δ`: at `Δ = 2`, `k = 11` and `e · 45 / 121 ≈ 1.011 > 1`. The
dependency neighbourhood excludes the event itself, so the degree is `2kΔ - 1` and the
condition is `e (1/k²)(2kΔ) = 2eΔ/k ≤ 1`, which holds exactly when `k ≥ 2eΔ`. **Use
`d = 2kΔ - 1`.**

## Two Lean pitfalls, both of which cascade

An earlier attempt at this proof was written in one go and abandoned; build it block by
block, compiling after each.

* `set f := fun c => …` makes `rw [hfdef]` useless — it produces an un-beta-reduced
  `(fun c => …) c`, so the following `if_pos` never matches. Do not rewrite: `f c` is
  *definitionally* the body, so `rw [show f c = … from if_pos hc]` works.
* `rcases (h : c' = c) with rfl` may eliminate `c` rather than `c'`, giving "unknown
  identifier `c`" far from the cause. Use `rcases … with heq | _` and `rw [heq]`.

An order contradiction of the shape `c₁.1 < c₁.2.1 = c₂.1 < c₂.2.1 = c₁.1` should be a
`calc` chain ending in `lt_irrefl`; the `▸` version does not elaborate, and `Fin` rules out
`omega`.
-/

open Finset

namespace PMC

section Transversal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Theorem 6.3.1.** A graph of maximum degree `Δ` whose vertices are partitioned into
parts of size at least `2eΔ` has an independent set with one vertex from each part. -/
theorem exists_independent_transversal (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ r k : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (hΔpos : 0 < Δ)
    (part : Fin r → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (part i) (part j))
    (hsize : ∀ i, k ≤ #(part i))
    (hk : 2 * Real.exp 1 * Δ ≤ k) :
    ∃ v : Fin r → V, (∀ i, v i ∈ part i) ∧ ∀ i j, i ≠ j → ¬ G.Adj (v i) (v j) := by
  classical
  -- `2eΔ ≤ k` with `Δ ≥ 1` forces `k ≥ 5`; we only need `k > 0`.
  have hexp1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hΔ1 : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔpos
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by nlinarith
  have hkpos : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) := by linarith
    exact_mod_cast this
  have : NeZero k := ⟨hkpos.ne'⟩
  obtain ⟨w, hwmem, hwinj, hwne⟩ := exists_enumeration part hdisj hsize
  -- the bad events and their coordinate blocks
  set A : Fin r × Fin r × Fin k × Fin k → Finset (Fin r → Fin k) :=
    fun c => if c.1 < c.2.1 ∧ G.Adj (w c.1 c.2.2.1) (w c.2.1 c.2.2.2)
      then (univ.filter fun f => f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2)
      else ∅ with hAdef
  set C : Fin r × Fin r × Fin k × Fin k → Finset (Fin r) :=
    fun c => if c.1 < c.2.1 ∧ G.Adj (w c.1 c.2.2.1) (w c.2.1 c.2.2.2)
      then ({c.1, c.2.1} : Finset (Fin r))
      else ∅ with hCdef
  have hA_det : ∀ c, DeterminedOn (C c) (A c) := by
    intro c
    by_cases hc : c.1 < c.2.1 ∧ G.Adj (w c.1 c.2.2.1) (w c.2.1 c.2.2.2)
    · rw [show A c = (univ.filter fun f => f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2) from if_pos hc,
        show C c = ({c.1, c.2.1} : Finset (Fin r)) from if_pos hc]
      intro f g hfg
      have h1 : f c.1 = g c.1 := hfg c.1 (by simp)
      have h2 : f c.2.1 = g c.2.1 := hfg c.2.1 (by simp)
      simp only [mem_filter, mem_univ, true_and, h1, h2]
    · rw [show A c = (∅ : Finset (Fin r → Fin k)) from if_neg hc]
      intro f g _
      simp
  -- the dependency neighbourhood: other indices whose block meets this one
  set N : Fin r × Fin r × Fin k × Fin k → Finset (Fin r × Fin r × Fin k × Fin k) :=
    fun c => univ.filter (fun c' => c' ≠ c ∧ ¬ Disjoint (C c) (C c')) with hNdef
  have hself : ∀ c, c ∉ N c := by
    intro c hc
    rw [hNdef] at hc
    exact (mem_filter.mp hc).2.1 rfl
  have hfar : ∀ c c' : Fin r × Fin r × Fin k × Fin k,
      c' ∉ insert c (N c) → Disjoint (C c) (C c') := by
    intro c c' hc'
    rw [mem_insert, not_or] at hc'
    obtain ⟨hne, hnot⟩ := hc'
    rw [hNdef] at hnot
    simp only [mem_filter, mem_univ, true_and, not_and, not_not] at hnot
    exact hnot hne
  -- each bad event pins two coordinates, so has probability `1/k²`
  have hprob : ∀ c, wprob (unifProd (Fin r) (Fin k)) (A c) ≤ 1 / (k : ℝ) * (1 / (k : ℝ)) := by
    intro c
    by_cases hc : c.1 < c.2.1 ∧ G.Adj (w c.1 c.2.2.1) (w c.2.1 c.2.2.2)
    · rw [show A c = (univ.filter fun f => f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2) from if_pos hc]
      have hne : c.2.1 ≠ c.1 := ne_of_gt hc.1
      have hd1 : DeterminedOn ({c.1} : Finset (Fin r))
          (univ.filter fun f : Fin r → Fin k => f c.1 = c.2.2.1) := by
        intro f g hfg
        have h : f c.1 = g c.1 := hfg c.1 (by simp)
        simp [h]
      have hd2 : DeterminedOn ((univ : Finset (Fin r)) \ {c.1})
          (univ.filter fun f : Fin r → Fin k => f c.2.1 = c.2.2.2) := by
        intro f g hfg
        have h : f c.2.1 = g c.2.1 := hfg c.2.1 (by simp [hne])
        simp [h]
      rw [show (univ.filter fun f : Fin r → Fin k => f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2)
          = (univ.filter fun f : Fin r → Fin k => f c.1 = c.2.2.1)
            ∩ (univ.filter fun f : Fin r → Fin k => f c.2.1 = c.2.2.2) from by
        rw [← Finset.filter_and]]
      rw [wprob_unifProd_mul_of_determinedOn hd1 hd2, wprob_unifProd_coord,
        wprob_unifProd_coord, Fintype.card_fin]
    · rw [show A c = (∅ : Finset (Fin r → Fin k)) from if_neg hc, wprob_unifProd]
      have : (0 : ℝ) < (k : ℝ) := by linarith
      simp
      positivity
  -- a vertex determines the part and the index it came from
  have hwuniq : ∀ (i j : Fin r) (a b : Fin k), w i a = w j b → i = j ∧ a = b := by
    intro i j a b h
    by_cases hij : i = j
    · subst hij
      exact ⟨rfl, hwinj i h⟩
    · exact absurd h (hwne i j a b hij)
  have hdeg : ∀ c, #(N c) ≤ 2 * k * Δ - 1 := by
    intro c
    by_cases hc : c.1 < c.2.1 ∧ G.Adj (w c.1 c.2.2.1) (w c.2.1 c.2.2.2)
    · -- every neighbouring index is valid and shares a part with `c`
      have key : ∀ c' ∈ insert c (N c),
          (c'.1 < c'.2.1 ∧ G.Adj (w c'.1 c'.2.2.1) (w c'.2.1 c'.2.2.2)) ∧
          (c'.1 = c.1 ∨ c'.1 = c.2.1 ∨ c'.2.1 = c.1 ∨ c'.2.1 = c.2.1) := by
        intro c' hc'
        rw [mem_insert] at hc'
        rcases hc' with heq | hmem
        · rw [heq]; exact ⟨hc, Or.inl rfl⟩
        · rw [hNdef, mem_filter] at hmem
          obtain ⟨-, -, hnd⟩ := hmem
          by_cases hv : c'.1 < c'.2.1 ∧ G.Adj (w c'.1 c'.2.2.1) (w c'.2.1 c'.2.2.2)
          · refine ⟨hv, ?_⟩
            rw [show C c = ({c.1, c.2.1} : Finset (Fin r)) from if_pos hc,
              show C c' = ({c'.1, c'.2.1} : Finset (Fin r)) from if_pos hv] at hnd
            obtain ⟨x, hx1, hx2⟩ := Finset.not_disjoint_iff.mp hnd
            simp only [mem_insert, mem_singleton] at hx1 hx2
            rcases hx1 with rfl | rfl <;> rcases hx2 with h | h
            · exact Or.inl h.symm
            · exact Or.inr (Or.inr (Or.inl h.symm))
            · exact Or.inr (Or.inl h.symm)
            · exact Or.inr (Or.inr (Or.inr h.symm))
          · exfalso
            apply hnd
            rw [show C c' = (∅ : Finset (Fin r)) from if_neg hv]
            exact Finset.disjoint_empty_right _
      -- the two parts hold `2k` vertices between them
      have hSdisj : Disjoint (univ.image (w c.1)) (univ.image (w c.2.1)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hx1
        obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hx2
        exact hwne c.1 c.2.1 a b (ne_of_lt hc.1) (ha.trans hb.symm)
      have hScard : #((univ.image (w c.1)) ∪ (univ.image (w c.2.1))) = 2 * k := by
        rw [Finset.card_union_of_disjoint hSdisj,
          Finset.card_image_of_injective _ (hwinj c.1),
          Finset.card_image_of_injective _ (hwinj c.2.1), Finset.card_univ, Fintype.card_fin]
        ring
      -- send each neighbouring index to an ordered adjacent pair starting in those parts
      have hbound : #(insert c (N c)) ≤ 2 * k * Δ := by
        have hle := card_adj_pairs_le G hΔ ((univ.image (w c.1)) ∪ (univ.image (w c.2.1)))
        rw [hScard] at hle
        refine le_trans ?_ hle
        refine Finset.card_le_card_of_injOn
          (fun c' => if c'.1 = c.1 ∨ c'.1 = c.2.1
            then (w c'.1 c'.2.2.1, w c'.2.1 c'.2.2.2)
            else (w c'.2.1 c'.2.2.2, w c'.1 c'.2.2.1)) ?_ ?_
        · intro c' hc'
          obtain ⟨hv, hm⟩ := key c' hc'
          have hpart : ∀ (i : Fin r) (a : Fin k), i = c.1 ∨ i = c.2.1 →
              w i a ∈ (univ.image (w c.1)) ∪ (univ.image (w c.2.1)) := by
            intro i a hi
            rw [Finset.mem_union]
            rcases hi with h | h
            · left; rw [← h]; exact Finset.mem_image_of_mem _ (mem_univ _)
            · right; rw [← h]; exact Finset.mem_image_of_mem _ (mem_univ _)
          dsimp only
          by_cases hb : c'.1 = c.1 ∨ c'.1 = c.2.1
          · rw [if_pos hb]
            exact mem_filter.mpr ⟨mem_univ _, hpart _ _ hb, hv.2⟩
          · rw [if_neg hb, not_or] at *
            refine mem_filter.mpr ⟨mem_univ _, hpart _ _ ?_, hv.2.symm⟩
            rcases hm with h | h | h | h
            · exact absurd h hb.1
            · exact absurd h hb.2
            · exact Or.inl h
            · exact Or.inr h
        · intro c₁ h₁ c₂ h₂ heq
          obtain ⟨hv₁, -⟩ := key c₁ (Finset.mem_coe.mp h₁)
          obtain ⟨hv₂, -⟩ := key c₂ (Finset.mem_coe.mp h₂)
          dsimp only at heq
          by_cases hb₁ : c₁.1 = c.1 ∨ c₁.1 = c.2.1 <;>
            by_cases hb₂ : c₂.1 = c.1 ∨ c₂.1 = c.2.1
          · rw [if_pos hb₁, if_pos hb₂, Prod.mk.injEq] at heq
            obtain ⟨e1, e2⟩ := hwuniq _ _ _ _ heq.1
            obtain ⟨e3, e4⟩ := hwuniq _ _ _ _ heq.2
            exact Prod.ext e1 (Prod.ext e3 (Prod.ext e2 e4))
          · rw [if_pos hb₁, if_neg hb₂, Prod.mk.injEq] at heq
            obtain ⟨e1, -⟩ := hwuniq _ _ _ _ heq.1
            obtain ⟨e3, -⟩ := hwuniq _ _ _ _ heq.2
            exfalso
            have hbad : c₁.1 < c₁.1 :=
              calc c₁.1 < c₁.2.1 := hv₁.1
                _ = c₂.1 := e3
                _ < c₂.2.1 := hv₂.1
                _ = c₁.1 := e1.symm
            exact lt_irrefl _ hbad
          · rw [if_neg hb₁, if_pos hb₂, Prod.mk.injEq] at heq
            obtain ⟨e1, -⟩ := hwuniq _ _ _ _ heq.1
            obtain ⟨e3, -⟩ := hwuniq _ _ _ _ heq.2
            exfalso
            have hbad : c₂.1 < c₂.1 :=
              calc c₂.1 < c₂.2.1 := hv₂.1
                _ = c₁.1 := e3.symm
                _ < c₁.2.1 := hv₁.1
                _ = c₂.1 := e1
            exact lt_irrefl _ hbad
          · rw [if_neg hb₁, if_neg hb₂, Prod.mk.injEq] at heq
            obtain ⟨e1, e2⟩ := hwuniq _ _ _ _ heq.1
            obtain ⟨e3, e4⟩ := hwuniq _ _ _ _ heq.2
            exact Prod.ext e3 (Prod.ext e1 (Prod.ext e4 e2))

      have hins : #(insert c (N c)) = #(N c) + 1 := Finset.card_insert_of_notMem (hself c)
      omega
    · -- an invalid index has an empty block, so nothing is adjacent to it
      have hNempty : N c = ∅ := by
        rw [hNdef, Finset.filter_eq_empty_iff]
        intro c' _
        rintro ⟨-, hnd⟩
        apply hnd
        rw [show C c = (∅ : Finset (Fin r)) from if_neg hc]
        exact Finset.disjoint_empty_left _
      rw [hNempty]
      simp
  have hk2' : 2 ≤ k := by exact_mod_cast hk2
  have h2kd : 2 ≤ 2 * k * Δ := by
    have h1 : 1 ≤ k * Δ := Nat.mul_pos (by omega) hΔpos
    calc 2 = 2 * 1 := by ring
      _ ≤ 2 * (k * Δ) := by omega
      _ = 2 * k * Δ := by ring
  have hd : 0 < 2 * k * Δ - 1 := by omega
  have hkR : (0 : ℝ) < (k : ℝ) := by linarith
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have hep : Real.exp 1 * (1 / (k : ℝ) * (1 / (k : ℝ))) * (((2 * k * Δ - 1 : ℕ) : ℝ) + 1) ≤ 1 := by
    have hcast : (((2 * k * Δ - 1 : ℕ) : ℝ) + 1) = 2 * (k : ℝ) * (Δ : ℝ) := by
      have h1 : (1 : ℕ) ≤ 2 * k * Δ := by omega
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [hcast, show Real.exp 1 * (1 / (k : ℝ) * (1 / (k : ℝ))) * (2 * (k : ℝ) * (Δ : ℝ))
        = (2 * Real.exp 1 * (Δ : ℝ)) / (k : ℝ) from by field_simp, div_le_one hkR]
    exact hk
  obtain ⟨f, hf⟩ :=
    exists_avoiding_of_lll A C hA_det N hd (by positivity) hself hdeg hfar hprob hep
  refine ⟨fun i => w i (f i), fun i => hwmem i (f i), ?_⟩
  intro i j hij hadj
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact hf (i, j, f i, f j) (by
      rw [show A (i, j, f i, f j)
        = (univ.filter fun g : Fin r → Fin k => g (i, j, f i, f j).1 = (i, j, f i, f j).2.2.1 ∧
            g (i, j, f i, f j).2.1 = (i, j, f i, f j).2.2.2) from if_pos ⟨hlt, hadj⟩]
      simp)
  · exact hf (j, i, f j, f i) (by
      rw [show A (j, i, f j, f i)
        = (univ.filter fun g : Fin r → Fin k => g (j, i, f j, f i).1 = (j, i, f j, f i).2.2.1 ∧
            g (j, i, f j, f i).2.1 = (j, i, f j, f i).2.2.2) from if_pos ⟨hlt, hadj.symm⟩]
      simp)

end Transversal

end PMC
