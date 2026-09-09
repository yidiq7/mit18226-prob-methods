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

section Events

variable (G : SimpleGraph V) [DecidableRel G.Adj] {r k : ℕ} (w : Fin r → Fin k → V)

/-- The index of a bad event: an ordered pair of parts with `i < j`, and a slot in each.

`abbrev`, not `def`: reducibility is what lets `if_pos` fire on `tEvent`/`tBlock` below
without a rewrite, which is the trap that sank the first attempt at this proof. -/
abbrev tValid (c : Fin r × Fin r × Fin k × Fin k) : Prop :=
  c.1 < c.2.1 ∧ G.Adj (w c.1 c.2.2.1) (w c.2.1 c.2.2.2)

/-- The bad event: both chosen slots are the ones joined by an edge. Invalid indices get the
empty event, which is never violated, has probability `0`, and is determined on the empty
block — so it is disjoint from everything and costs nothing. -/
abbrev tEvent (c : Fin r × Fin r × Fin k × Fin k) : Finset (Fin r → Fin k) :=
  if tValid G w c then
    (univ : Finset (Fin r → Fin k)).filter (fun f => f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2)
  else ∅

/-- The coordinates a bad event depends on. -/
abbrev tBlock (c : Fin r × Fin r × Fin k × Fin k) : Finset (Fin r) :=
  if tValid G w c then {c.1, c.2.1} else ∅

/-- Each bad event depends only on the two part-indices in its block. -/
theorem determinedOn_tEvent (c : Fin r × Fin r × Fin k × Fin k) :
    DeterminedOn (tBlock G w c) (tEvent G w c) := by
  by_cases hc : tValid G w c
  · rw [show tEvent G w c = (univ : Finset (Fin r → Fin k)).filter
        (fun f => f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2) from if_pos hc,
      show tBlock G w c = ({c.1, c.2.1} : Finset (Fin r)) from if_pos hc]
    intro f g hfg
    simp only [mem_filter, mem_univ, true_and]
    rw [hfg c.1 (by simp), hfg c.2.1 (by simp)]
  · rw [show tEvent G w c = (∅ : Finset (Fin r → Fin k)) from if_neg hc]
    intro f g _
    simp

/-- **A bad event has probability `1/k²`**: it pins down two distinct coordinates, and
block independence multiplies `PMC.wprob_unifProd_coord` twice. -/
theorem wprob_tEvent_le [Nonempty (Fin k)] (c : Fin r × Fin r × Fin k × Fin k) :
    wprob (unifProd (Fin r) (Fin k)) (tEvent G w c) ≤ 1 / (k : ℝ) ^ 2 := by
  by_cases hc : tValid G w c
  · rw [show tEvent G w c = (univ : Finset (Fin r → Fin k)).filter
        (fun f => f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2) from if_pos hc]
    have hne : c.1 ≠ c.2.1 := ne_of_lt hc.1
    have hsplit : (univ : Finset (Fin r → Fin k)).filter
          (fun f => f c.1 = c.2.2.1 ∧ f c.2.1 = c.2.2.2)
        = ((univ : Finset (Fin r → Fin k)).filter fun f => f c.1 = c.2.2.1)
          ∩ ((univ : Finset (Fin r → Fin k)).filter fun f => f c.2.1 = c.2.2.2) := by
      ext f
      simp [and_assoc]
    have hdet1 : DeterminedOn ({c.1} : Finset (Fin r))
        ((univ : Finset (Fin r → Fin k)).filter fun f => f c.1 = c.2.2.1) := by
      intro f g hfg
      simp only [mem_filter, mem_univ, true_and]
      rw [hfg c.1 (by simp)]
    have hdet2 : DeterminedOn ((univ : Finset (Fin r)) \ {c.1})
        ((univ : Finset (Fin r → Fin k)).filter fun f => f c.2.1 = c.2.2.2) := by
      intro f g hfg
      simp only [mem_filter, mem_univ, true_and]
      rw [hfg c.2.1 (by simp [Ne.symm hne])]
    rw [hsplit, wprob_unifProd_mul_of_determinedOn hdet1 hdet2,
      wprob_unifProd_coord, wprob_unifProd_coord, Fintype.card_fin, div_mul_div_comm,
      one_mul, sq]
  · rw [show tEvent G w c = (∅ : Finset (Fin r → Fin k)) from if_neg hc, wprob_empty]
    positivity

/-- Orient a neighbouring index so that its first vertex lies in one of `c`'s two parts. -/
abbrev tPair (c c' : Fin r × Fin r × Fin k × Fin k) : V × V :=
  if c'.1 ∈ ({c.1, c.2.1} : Finset (Fin r))
  then (w c'.1 c'.2.2.1, w c'.2.1 c'.2.2.2)
  else (w c'.2.1 c'.2.2.2, w c'.1 c'.2.2.1)

/-- The dependency neighbourhood of a bad event. -/
abbrev tNbr (c : Fin r × Fin r × Fin k × Fin k) :
    Finset (Fin r × Fin r × Fin k × Fin k) :=
  univ.filter fun c' => c' ≠ c ∧ ¬ Disjoint (tBlock G w c) (tBlock G w c')

/-- **The dependency degree is at most `2kΔ - 1`.**

`PMC.tPair` injects the neighbourhood, together with `c` itself, into the ordered adjacent
pairs starting in `Vᵢ ∪ V_j`, of which there are at most `2kΔ`
(`PMC.card_adj_pairs_le`). The `- 1` is the self-exclusion, and it is not optional: without
it the notes' displayed inequality is false at `Δ = 2`.

Injectivity of `PMC.tPair` is exactly where the `c.1 < c.2.1` convention earns its keep — a
collision across the two branches would need both `(i,j,a,b)` and `(j,i,b,a)` to be
indices. -/
theorem card_tNbr_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (hw_eq : ∀ i j a b, w i a = w j b → i = j ∧ a = b)
    (c : Fin r × Fin r × Fin k × Fin k) :
    #(tNbr G w c) ≤ 2 * k * Δ - 1 := by
  classical
  by_cases hc : tValid G w c
  · have hvalid_of : ∀ c' ∈ insert c (tNbr G w c), tValid G w c' := by
      intro c' hc'
      rcases Finset.mem_insert.mp hc' with heq | hmem
      · rw [heq]; exact hc
      · rw [mem_filter] at hmem
        by_contra hbad
        refine hmem.2.2 ?_
        rw [show tBlock G w c' = (∅ : Finset (Fin r)) from if_neg hbad]
        exact Finset.disjoint_empty_right _
    have hmeet_of : ∀ c' ∈ insert c (tNbr G w c), ∃ x,
        x ∈ ({c.1, c.2.1} : Finset (Fin r)) ∧ x ∈ ({c'.1, c'.2.1} : Finset (Fin r)) := by
      intro c' hc'
      rcases Finset.mem_insert.mp hc' with heq | hmem
      · exact ⟨c.1, by simp, by rw [heq]; simp⟩
      · rw [mem_filter] at hmem
        have h := hmem.2.2
        rw [show tBlock G w c = ({c.1, c.2.1} : Finset (Fin r)) from if_pos hc,
          show tBlock G w c' = ({c'.1, c'.2.1} : Finset (Fin r)) from
            if_pos (hvalid_of c' hc'), Finset.not_disjoint_iff] at h
        exact h
    -- the target: ordered adjacent pairs starting in the two parts
    have hScard : #((univ.image (w c.1)) ∪ (univ.image (w c.2.1)) : Finset V) ≤ 2 * k := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have h1 : #(univ.image (w c.1)) ≤ k := by
        refine le_trans Finset.card_image_le ?_
        rw [card_univ, Fintype.card_fin]
      have h2 : #(univ.image (w c.2.1)) ≤ k := by
        refine le_trans Finset.card_image_le ?_
        rw [card_univ, Fintype.card_fin]
      omega
    have hEcard : #((univ : Finset (V × V)).filter fun q =>
        q.1 ∈ ((univ.image (w c.1)) ∪ (univ.image (w c.2.1)) : Finset V)
          ∧ G.Adj q.1 q.2) ≤ 2 * k * Δ :=
      le_trans (card_adj_pairs_le G hΔ _) (Nat.mul_le_mul_right Δ hScard)
    have hmaps : ∀ c' ∈ insert c (tNbr G w c), tPair w c c'
        ∈ (univ : Finset (V × V)).filter fun q =>
            q.1 ∈ ((univ.image (w c.1)) ∪ (univ.image (w c.2.1)) : Finset V)
              ∧ G.Adj q.1 q.2 := by
      intro c' hc'
      have hval' := hvalid_of c' hc'
      obtain ⟨x, hx1, hx2⟩ := hmeet_of c' hc'
      rw [mem_filter]
      refine ⟨mem_univ _, ?_, ?_⟩
      · by_cases hbr : c'.1 ∈ ({c.1, c.2.1} : Finset (Fin r))
        · rw [show tPair w c c' = (w c'.1 c'.2.2.1, w c'.2.1 c'.2.2.2) from if_pos hbr]
          simp only [Finset.mem_union, Finset.mem_image, mem_univ, true_and]
          rcases Finset.mem_insert.mp hbr with h | h
          · exact Or.inl ⟨c'.2.2.1, by rw [h]⟩
          · exact Or.inr ⟨c'.2.2.1, by rw [Finset.mem_singleton.mp h]⟩
        · rw [show tPair w c c' = (w c'.2.1 c'.2.2.2, w c'.1 c'.2.2.1) from if_neg hbr]
          simp only [Finset.mem_union, Finset.mem_image, mem_univ, true_and]
          have hxc' : x = c'.1 ∨ x = c'.2.1 := by
            rcases Finset.mem_insert.mp hx2 with h | h
            · exact Or.inl h
            · exact Or.inr (Finset.mem_singleton.mp h)
          have h21 : c'.2.1 ∈ ({c.1, c.2.1} : Finset (Fin r)) := by
            rcases hxc' with h | h
            · exact absurd (by rw [← h]; exact hx1) hbr
            · rw [← h]; exact hx1
          rcases Finset.mem_insert.mp h21 with h | h
          · exact Or.inl ⟨c'.2.2.2, by rw [h]⟩
          · exact Or.inr ⟨c'.2.2.2, by rw [Finset.mem_singleton.mp h]⟩
      · by_cases hbr : c'.1 ∈ ({c.1, c.2.1} : Finset (Fin r))
        · rw [show tPair w c c' = (w c'.1 c'.2.2.1, w c'.2.1 c'.2.2.2) from if_pos hbr]
          exact hval'.2
        · rw [show tPair w c c' = (w c'.2.1 c'.2.2.2, w c'.1 c'.2.2.1) from if_neg hbr]
          exact hval'.2.symm
    have hinj : ∀ c₁ ∈ insert c (tNbr G w c), ∀ c₂ ∈ insert c (tNbr G w c),
        tPair w c c₁ = tPair w c c₂ → c₁ = c₂ := by
      intro c₁ h₁ c₂ h₂ heq
      have hv₁ := hvalid_of c₁ h₁
      have hv₂ := hvalid_of c₂ h₂
      by_cases hb₁ : c₁.1 ∈ ({c.1, c.2.1} : Finset (Fin r)) <;>
        by_cases hb₂ : c₂.1 ∈ ({c.1, c.2.1} : Finset (Fin r))
      · rw [show tPair w c c₁ = (w c₁.1 c₁.2.2.1, w c₁.2.1 c₁.2.2.2) from if_pos hb₁,
          show tPair w c c₂ = (w c₂.1 c₂.2.2.1, w c₂.2.1 c₂.2.2.2) from if_pos hb₂,
          Prod.ext_iff] at heq
        obtain ⟨hi, ha⟩ := hw_eq _ _ _ _ heq.1
        obtain ⟨hj, hb⟩ := hw_eq _ _ _ _ heq.2
        exact Prod.ext hi (Prod.ext hj (Prod.ext ha hb))
      · rw [show tPair w c c₁ = (w c₁.1 c₁.2.2.1, w c₁.2.1 c₁.2.2.2) from if_pos hb₁,
          show tPair w c c₂ = (w c₂.2.1 c₂.2.2.2, w c₂.1 c₂.2.2.1) from if_neg hb₂,
          Prod.ext_iff] at heq
        obtain ⟨hi, -⟩ := hw_eq _ _ _ _ heq.1
        obtain ⟨hj, -⟩ := hw_eq _ _ _ _ heq.2
        exact absurd (calc c₁.1 < c₁.2.1 := hv₁.1
            _ = c₂.1 := hj
            _ < c₂.2.1 := hv₂.1
            _ = c₁.1 := hi.symm) (lt_irrefl _)
      · rw [show tPair w c c₁ = (w c₁.2.1 c₁.2.2.2, w c₁.1 c₁.2.2.1) from if_neg hb₁,
          show tPair w c c₂ = (w c₂.1 c₂.2.2.1, w c₂.2.1 c₂.2.2.2) from if_pos hb₂,
          Prod.ext_iff] at heq
        obtain ⟨hj, -⟩ := hw_eq _ _ _ _ heq.1
        obtain ⟨hi, -⟩ := hw_eq _ _ _ _ heq.2
        exact absurd (calc c₂.1 < c₂.2.1 := hv₂.1
            _ = c₁.1 := hi.symm
            _ < c₁.2.1 := hv₁.1
            _ = c₂.1 := hj) (lt_irrefl _)
      · rw [show tPair w c c₁ = (w c₁.2.1 c₁.2.2.2, w c₁.1 c₁.2.2.1) from if_neg hb₁,
          show tPair w c c₂ = (w c₂.2.1 c₂.2.2.2, w c₂.1 c₂.2.2.1) from if_neg hb₂,
          Prod.ext_iff] at heq
        obtain ⟨hj, hb⟩ := hw_eq _ _ _ _ heq.1
        obtain ⟨hi, ha⟩ := hw_eq _ _ _ _ heq.2
        exact Prod.ext hi (Prod.ext hj (Prod.ext ha hb))
    have hcard := le_trans (Finset.card_le_card_of_injOn _ hmaps hinj) hEcard
    have hins : #(insert c (tNbr G w c)) = #(tNbr G w c) + 1 := by
      refine Finset.card_insert_of_notMem ?_
      intro hmem
      rw [mem_filter] at hmem
      exact hmem.2.1 rfl
    omega
  · have hemp : tNbr G w c = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c' hc'
      rw [mem_filter] at hc'
      refine hc'.2.2 ?_
      rw [show tBlock G w c = (∅ : Finset (Fin r)) from if_neg hc]
      exact Finset.disjoint_empty_left _
    rw [hemp]
    simp

end Events

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
  have hexp1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hΔR : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔpos
  have hkR : (2 : ℝ) < k := by
    have hepos : (0 : ℝ) < 2 * Real.exp 1 := by positivity
    have h1 : 2 * Real.exp 1 * 1 ≤ 2 * Real.exp 1 * Δ :=
      mul_le_mul_of_nonneg_left hΔR (le_of_lt hepos)
    rw [mul_one] at h1
    have h2 : 2 * Real.exp 1 ≤ (k : ℝ) := le_trans h1 hk
    calc (2 : ℝ) = 2 * 1 := by ring
      _ < 2 * Real.exp 1 := by linarith
      _ ≤ (k : ℝ) := h2
  have hk2N : 2 < k := by exact_mod_cast hkR
  have hkpos : 0 < k := by omega
  have hkR0 : (0 : ℝ) < k := by exact_mod_cast hkpos
  haveI : Nonempty (Fin k) := ⟨⟨0, hkpos⟩⟩
  -- trim the parts to size `k` and enumerate them
  obtain ⟨w, hwmem, hwinj, hwsep⟩ := exists_enumeration part hdisj hsize
  have hw_eq : ∀ i j a b, w i a = w j b → i = j ∧ a = b := by
    intro i j a b h
    by_cases hij : i = j
    · subst hij
      exact ⟨rfl, hwinj i h⟩
    · exact absurd h (hwsep i j a b hij)
  have hdpos : 0 < 2 * k * Δ - 1 := by
    have h1 : 1 ≤ Δ := hΔpos
    have h2 : 3 ≤ k := by omega
    have h3 : 6 ≤ 2 * k * Δ := by nlinarith
    omega
  have hself : ∀ c, c ∉ tNbr G w c := by
    intro c hc
    rw [mem_filter] at hc
    exact hc.2.1 rfl
  have hfar : ∀ c c', c' ∉ insert c (tNbr G w c) →
      Disjoint (tBlock G w c) (tBlock G w c') := by
    intro c c' hc'
    rw [Finset.mem_insert] at hc'
    push_neg at hc'
    by_contra hdis
    exact hc'.2 (by rw [mem_filter]; exact ⟨mem_univ _, hc'.1, hdis⟩)
  -- `e (1/k²) (2kΔ) = 2eΔ/k ≤ 1` is exactly the hypothesis `2eΔ ≤ k`
  have hep : Real.exp 1 * (1 / (k : ℝ) ^ 2) * ((2 * k * Δ - 1 : ℕ) + 1) ≤ 1 := by
    have hcast : (((2 * k * Δ - 1 : ℕ) : ℝ) + 1) = 2 * (k : ℝ) * Δ := by
      have hk1 : 1 ≤ k := by omega
      have h1 : 1 ≤ 2 * k * Δ := by nlinarith [hΔpos]
      -- with the product as an atom, `omega` can cancel the truncated subtraction
      have h2 : (2 * k * Δ - 1 : ℕ) + 1 = 2 * k * Δ := by omega
      calc (((2 * k * Δ - 1 : ℕ) : ℝ) + 1)
          = (((2 * k * Δ - 1 : ℕ) + 1 : ℕ) : ℝ) := by push_cast; ring
        _ = ((2 * k * Δ : ℕ) : ℝ) := by rw [h2]
        _ = 2 * (k : ℝ) * Δ := by push_cast; ring
    rw [hcast]
    have hid : Real.exp 1 * (1 / (k : ℝ) ^ 2) * (2 * (k : ℝ) * Δ)
        = 2 * Real.exp 1 * Δ / k := by
      field_simp
    rw [hid, div_le_one hkR0]
    exact hk
  obtain ⟨f, hf⟩ := exists_avoiding_of_lll (tEvent G w) (tBlock G w)
    (determinedOn_tEvent G w) (tNbr G w) hdpos (by positivity) hself
    (fun c => card_tNbr_le G w hΔ hw_eq c) hfar (wprob_tEvent_le G w) hep
  refine ⟨fun i => w i (f i), fun i => hwmem i (f i), ?_⟩
  intro i j hij hadj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · refine hf (i, j, f i, f j) ?_
    rw [show tEvent G w (i, j, f i, f j) = (univ : Finset (Fin r → Fin k)).filter
        (fun g => g i = f i ∧ g j = f j) from if_pos ⟨hlt, hadj⟩, mem_filter]
    exact ⟨mem_univ _, rfl, rfl⟩
  · refine hf (j, i, f j, f i) ?_
    rw [show tEvent G w (j, i, f j, f i) = (univ : Finset (Fin r → Fin k)).filter
        (fun g => g j = f j ∧ g i = f i) from if_pos ⟨hgt, hadj.symm⟩, mem_filter]
    exact ⟨mem_univ _, rfl, rfl⟩

end Transversal

end PMC
