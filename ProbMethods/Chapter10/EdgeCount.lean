import ProbMethods.Chapter10.Intersecting
import Mathlib.Data.Sym.Card

/-!
# Counting the edges of a complete graph inside a vertex set

Step (2) of Theorem 10.4.9: the block `A_S` is the set of edges lying inside `S` together
with those lying inside its complement, and its size is `C(|S|,2) + C(n-|S|,2)`.

The edge type is `PMC.Edge V = {e : Sym2 V // ¬ e.IsDiag}`, chosen because Mathlib's
`Sym2.card_subtype_not_diag` gives `#(Edge V) = C(#V, 2)` for free and because — since the
`LinearOrder` hypothesis came off Shearer's chain — it now works directly with
`PMC.card_pow_le_prod_of_traces_intersecting`.

`PMC.card_within` is proved by exhibiting a bijection with `PMC.Edge ↥S` and quoting the
same Mathlib count on the subtype. The one trick worth noting: the *surjectivity* half needs
to lift an edge of `V` with both ends in `S` to an edge of `↥S`, which would be awkward as a
function — but surjectivity is a `Prop`, so `Sym2.ind` destructs the edge into an actual
pair and the lift is immediate. Using `Finset.card_bij` (surjectivity) rather than
`Finset.card_bij'` (an explicit inverse) is what makes that available.
-/

open Finset

namespace PMC

section EdgeCount

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of the complete graph on `V`: unordered pairs of distinct vertices.

An `abbrev` rather than a `def`, so the subtype structure — coercions, `Fintype`,
`DecidableEq` — stays visible to instance resolution. -/
abbrev Edge (V : Type*) := {e : Sym2 V // ¬ e.IsDiag}

@[simp] lemma card_Edge : Fintype.card (Edge V) = (Fintype.card V).choose 2 :=
  Sym2.card_subtype_not_diag

/-- Every edge is an unordered pair of distinct vertices. `Sym2.ind` needs the proof of
non-diagonality reverted first, since it mentions the element being destructed. -/
lemma exists_pair_of_edge (e : Edge V) : ∃ x y : V, x ≠ y ∧ e.1 = s(x, y) := by
  obtain ⟨z, hz⟩ := e
  revert hz
  induction z using Sym2.ind with
  | _ x y =>
    intro hz
    exact ⟨x, y, fun h => hz (Sym2.mk_isDiag_iff.mpr h), rfl⟩

/-- An injection on vertices carries edges to edges. -/
lemma map_not_isDiag {W : Type*} (g : W → V) (hg : Function.Injective g) {z : Sym2 W}
    (hz : ¬ z.IsDiag) : ¬ (Sym2.map g z).IsDiag := by
  revert hz
  induction z using Sym2.ind with
  | _ a b =>
    intro hz
    rw [Sym2.map_pair_eq, Sym2.mk_isDiag_iff]
    intro h
    exact hz (Sym2.mk_isDiag_iff.mpr (hg h))

/-- The edge map induced by an injection on vertices. -/
abbrev edgeMap {W : Type*} (g : W → V) (hg : Function.Injective g) (f : Edge W) : Edge V :=
  ⟨Sym2.map g f.1, map_not_isDiag g hg f.2⟩

/-- The edges with both endpoints in `S`. -/
def within (S : Finset V) : Finset (Edge V) :=
  univ.filter fun e => ∀ x ∈ e.1, x ∈ S

/-- **The number of edges inside `S` is `C(#S, 2)`.** -/
theorem card_within (S : Finset V) : #(within S) = (#S).choose 2 := by
  classical
  have hbij : #(univ : Finset (Edge ↥S)) = #(within S) := by
    refine Finset.card_bij (fun f _ => edgeMap Subtype.val Subtype.val_injective f) ?_ ?_ ?_
    · intro f _
      rw [within, mem_filter]
      refine ⟨mem_univ _, fun x hx => ?_⟩
      rw [Sym2.mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact a.2
    · intro f _ f' _ heq
      exact Subtype.ext
        (Sym2.map.injective Subtype.val_injective (Subtype.ext_iff.mp heq))
    · intro e he
      rw [within, mem_filter] at he
      obtain ⟨x, y, hxy, hz⟩ := exists_pair_of_edge e
      have hxS : x ∈ S := he.2 x (by rw [hz]; simp)
      have hyS : y ∈ S := he.2 y (by rw [hz]; simp)
      refine ⟨⟨s(⟨x, hxS⟩, ⟨y, hyS⟩), ?_⟩, mem_univ _, ?_⟩
      · rw [Sym2.mk_isDiag_iff]
        exact fun h => hxy (congrArg Subtype.val h)
      · apply Subtype.ext
        rw [hz]
        exact Sym2.map_pair_eq _ _ _
  rw [← hbij, card_univ, card_Edge, Fintype.card_coe]

/-- The block `A_S` of Theorem 10.4.9: the edges lying inside `S` together with those lying
inside its complement. -/
def block (S : Finset V) : Finset (Edge V) :=
  univ.filter fun e => (∀ z ∈ e.1, z ∈ S) ∨ (∀ z ∈ e.1, z ∉ S)

/-- **Step (3): the covering multiplicity, as a direct count.**

For a fixed edge, the number of `m`-element vertex sets putting both of its endpoints on the
same side is `C(n-2, m-2) + C(n-2, m)` — both endpoints inside, or both outside. It visibly
does not depend on *which* edge, so the notes' appeal to "symmetry and averaging" (which in
Lean would mean a transitive action of `Sₙ` on edges) is unnecessary.

`2 ≤ m` is required and not cosmetic: at `m = 0` the truncated `m - 2` makes the first term
`C(n-2,0) = 1`, while no `0`-set can contain both endpoints. -/
theorem card_blocks_containing (e : Edge V) {m : ℕ} (hm : 2 ≤ m) :
    #(((univ : Finset V).powersetCard m).filter fun S => e ∈ block S)
      = (Fintype.card V - 2).choose (m - 2) + (Fintype.card V - 2).choose m := by
  classical
  obtain ⟨x, y, hxy, hz⟩ := exists_pair_of_edge e
  set P := (univ : Finset V) \ ({x, y} : Finset V) with hPdef
  have hpairsub : ({x, y} : Finset V) ⊆ univ := subset_univ _
  have hPcard : #P = Fintype.card V - 2 := by
    rw [hPdef, card_sdiff_of_subset hpairsub, card_univ, Finset.card_pair hxy]
  have hmemP : ∀ w, w ∈ P → w ≠ x ∧ w ≠ y := by
    intro w hw
    rw [hPdef, mem_sdiff, mem_insert, mem_singleton] at hw
    exact ⟨fun h => hw.2 (Or.inl h), fun h => hw.2 (Or.inr h)⟩
  -- the block condition, in terms of the two endpoints
  have hpred : ∀ S : Finset V,
      e ∈ block S ↔ ((x ∈ S ∧ y ∈ S) ∨ (x ∉ S ∧ y ∉ S)) := by
    intro S
    rw [block, mem_filter, hz]
    simp only [mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨h x (by simp), h y (by simp)⟩
      · exact Or.inr ⟨h x (by simp), h y (by simp)⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · refine Or.inl fun w hw => ?_
        rw [Sym2.mem_iff] at hw
        rcases hw with rfl | rfl
        · exact h1
        · exact h2
      · refine Or.inr fun w hw => ?_
        rw [Sym2.mem_iff] at hw
        rcases hw with rfl | rfl
        · exact h1
        · exact h2
  rw [Finset.filter_congr fun S _ => hpred S, Finset.filter_or]
  have hdisj : Disjoint
      (((univ : Finset V).powersetCard m).filter fun S => x ∈ S ∧ y ∈ S)
      (((univ : Finset V).powersetCard m).filter fun S => x ∉ S ∧ y ∉ S) := by
    rw [Finset.disjoint_left]
    intro S hS hS'
    rw [mem_filter] at hS hS'
    exact hS'.2.1 hS.2.1
  rw [Finset.card_union_of_disjoint hdisj]
  congr 1
  · -- both endpoints inside: delete them
    rw [← hPcard, ← Finset.card_powersetCard]
    refine Finset.card_nbij' (fun S => S \ ({x, y} : Finset V))
      (fun T => insert x (insert y T)) ?_ ?_ ?_ ?_
    · intro S hS
      rw [mem_coe, mem_filter, Finset.mem_powersetCard] at hS
      obtain ⟨⟨-, hcard⟩, hxS, hyS⟩ := hS
      have hsub : ({x, y} : Finset V) ⊆ S := by
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hxS
        · exact hyS
      rw [mem_coe, Finset.mem_powersetCard]
      refine ⟨fun w hw => ?_, ?_⟩
      · rw [mem_sdiff] at hw
        rw [hPdef, mem_sdiff]
        exact ⟨mem_univ w, hw.2⟩
      · rw [card_sdiff_of_subset hsub, hcard, Finset.card_pair hxy]
    · intro T hT
      rw [mem_coe, Finset.mem_powersetCard] at hT
      obtain ⟨hsub, hcard⟩ := hT
      have hxT : x ∉ T := fun h => (hmemP x (hsub h)).1 rfl
      have hyT : y ∉ T := fun h => (hmemP y (hsub h)).2 rfl
      have hxyT : x ∉ insert y T := by
        simp only [mem_insert]
        exact fun h => h.elim hxy fun h' => hxT h'
      rw [mem_coe, mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨subset_univ _, ?_⟩, by simp, by simp⟩
      rw [Finset.card_insert_of_notMem hxyT, Finset.card_insert_of_notMem hyT, hcard]
      omega
    · intro S hS
      rw [mem_coe, mem_filter] at hS
      obtain ⟨-, hxS, hyS⟩ := hS
      ext w
      simp only [mem_insert, mem_singleton, mem_sdiff]
      constructor
      · rintro (rfl | rfl | ⟨h, -⟩)
        · exact hxS
        · exact hyS
        · exact h
      · intro hwS
        by_cases hwx : w = x
        · exact Or.inl hwx
        · by_cases hwy : w = y
          · exact Or.inr (Or.inl hwy)
          · exact Or.inr (Or.inr ⟨hwS, by simp [hwx, hwy]⟩)
    · intro T hT
      rw [mem_coe, Finset.mem_powersetCard] at hT
      obtain ⟨hsub, -⟩ := hT
      have hxT : x ∉ T := fun h => (hmemP x (hsub h)).1 rfl
      have hyT : y ∉ T := fun h => (hmemP y (hsub h)).2 rfl
      ext w
      simp only [mem_sdiff, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hw, hne⟩
        rcases hw with rfl | rfl | hw
        · exact absurd (Or.inl rfl) hne
        · exact absurd (Or.inr rfl) hne
        · exact hw
      · intro hw
        refine ⟨Or.inr (Or.inr hw), ?_⟩
        rintro (rfl | rfl)
        · exact hxT hw
        · exact hyT hw
  · -- both endpoints outside: the set lives in the complement of the pair
    rw [← hPcard, ← Finset.card_powersetCard]
    congr 1
    ext S
    rw [mem_filter, Finset.mem_powersetCard, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨-, hcard⟩, hx, hy⟩
      refine ⟨fun w hwS => ?_, hcard⟩
      rw [hPdef, mem_sdiff]
      refine ⟨mem_univ w, ?_⟩
      rw [mem_insert, mem_singleton]
      rintro (rfl | rfl)
      · exact hx hwS
      · exact hy hwS
    · rintro ⟨hsub, hcard⟩
      refine ⟨⟨subset_univ S, hcard⟩, fun hxS => ?_, fun hyS => ?_⟩
      · have h := hsub hxS
        rw [hPdef, mem_sdiff, mem_insert, mem_singleton] at h
        exact h.2 (Or.inl rfl)
      · have h := hsub hyS
        rw [hPdef, mem_sdiff, mem_insert, mem_singleton] at h
        exact h.2 (Or.inr rfl)

/-- The block splits as a disjoint union: edges inside `S`, and edges inside its
complement. An edge cannot be in both, because it has a vertex. -/
theorem card_block (S : Finset V) :
    #(block S) = (#S).choose 2 + (Fintype.card V - #S).choose 2 := by
  classical
  have hsplit : block S = within S ∪ within ((univ : Finset V) \ S) := by
    ext e
    simp [block, within]
  have hdisj : Disjoint (within S) (within ((univ : Finset V) \ S)) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨x, y, -, hz⟩ := exists_pair_of_edge e
    rw [within, mem_filter] at he he'
    have h1 : x ∈ S := he.2 x (by rw [hz]; simp)
    have h2 : x ∈ (univ : Finset V) \ S := he'.2 x (by rw [hz]; simp)
    exact (mem_sdiff.mp h2).2 h1
  rw [hsplit, Finset.card_union_of_disjoint hdisj, card_within, card_within,
    card_sdiff_of_subset (subset_univ S), card_univ]

/-- Counting the pairs `(S, e)` with `e` inside a part of `S`, both ways round. -/
theorem sum_card_block (m : ℕ) :
    ∑ S ∈ (univ : Finset V).powersetCard m, #(block S)
      = ∑ e : Edge V, #(((univ : Finset V).powersetCard m).filter fun S => e ∈ block S) := by
  classical
  have hself : ∀ S : Finset V,
      (univ : Finset (Edge V)).filter (fun e => e ∈ block S) = block S := by
    intro S
    ext e
    simp
  have h1 : ∀ S : Finset V, #(block S) = ∑ e : Edge V, if e ∈ block S then 1 else 0 := by
    intro S
    rw [← Finset.sum_filter, hself S, Finset.card_eq_sum_ones]
  calc ∑ S ∈ (univ : Finset V).powersetCard m, #(block S)
      = ∑ S ∈ (univ : Finset V).powersetCard m,
          ∑ e : Edge V, (if e ∈ block S then 1 else 0) :=
        Finset.sum_congr rfl fun S _ => h1 S
    _ = ∑ e : Edge V,
          ∑ S ∈ (univ : Finset V).powersetCard m, (if e ∈ block S then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ e : Edge V,
          #(((univ : Finset V).powersetCard m).filter fun S => e ∈ block S) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.card_filter]

/-- **Step (4) of Theorem 10.4.9: the double-count identity.**

`C(n,m) · r = C(n,2) · k`, where `r = C(m,2) + C(n-m,2)` is the size of every block and
`k = C(n-2,m-2) + C(n-2,m)` is the number of blocks containing any given edge. Both sides
count the pairs `(S, e)` with `S` an `m`-set and `e` an edge inside one of its two parts;
the point is that both `r` and `k` are *constant*, so each side collapses to a product. -/
theorem choose_mul_block_eq {m : ℕ} (hm : 2 ≤ m) :
    (Fintype.card V).choose m * (m.choose 2 + (Fintype.card V - m).choose 2)
      = (Fintype.card V).choose 2
        * ((Fintype.card V - 2).choose (m - 2) + (Fintype.card V - 2).choose m) := by
  classical
  have h := sum_card_block (V := V) m
  rw [Finset.sum_congr rfl (fun S hS => by
        rw [Finset.mem_powersetCard] at hS
        rw [card_block, hS.2] : ∀ S ∈ (univ : Finset V).powersetCard m,
          #(block S) = m.choose 2 + (Fintype.card V - m).choose 2),
    Finset.sum_const, Finset.card_powersetCard, card_univ,
    Finset.sum_congr rfl (fun e _ => card_blocks_containing e hm), Finset.sum_const,
    card_univ, card_Edge] at h
  simpa [nsmul_eq_mul] using h

end EdgeCount

end PMC
