import ProbMethods.Chapter06.ProductLLL

/-!
# §6.3 — the bad events of the independent-transversal proof

Theorem 6.3.1 itself is in `Transversal.lean`. This file holds the pieces its probabilistic
setup is built from, as named results: after `PMC.exists_enumeration` has trimmed the parts
to size exactly `k` and enumerated them, a transversal is a point of the uniform product
`Fin r → Fin k`, and the bad events are indexed by an ordered pair of parts together with a
slot in each.

* `PMC.tEvent` — the bad event: both chosen slots are the ones joined by an edge.
* `PMC.determinedOn_tEvent` — it depends only on the two part-indices in its block, which is
  what discharges the local lemma's independence hypothesis.
* `PMC.wprob_tEvent_le` — its probability is `1/k²`, by block independence.
* `PMC.card_tNbr_le` — the dependency degree is at most `2kΔ - 1`.

**The `-1` in the degree bound is not slack, it is an erratum.** The notes display
`e (1/k²) (2kΔ + 1) ≤ 1`, which is false at `Δ = 2`: at `k = 11`,
`e · 45 / 121 ≈ 1.011 > 1`. The dependency neighbourhood excludes the event itself, so the
correct count is `2kΔ - 1`, and that is what makes `k = ⌈2eΔ⌉` suffice.

These are kept separate because `Transversal.lean` carries a contributor's self-contained
proof of 6.3.1 (PR #43), which does not route through them. They stay available for §6.5 and
for any variant of the transversal argument.
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
end Transversal

end PMC
