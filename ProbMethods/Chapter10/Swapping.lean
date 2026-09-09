import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

/-!
# §10.4 — the bipartite swapping trick

Lemma 10.4.13: `i(G)² ≤ i(G × K₂)`, where `i` counts independent sets and `G × K₂` is the
bipartite double cover. This is what reduces Kahn–Zhao (Theorem 10.4.12) from all `d`-regular
graphs to the bipartite ones, and unlike the rest of §10.4 it is **not** an entropy argument:
the notes give an explicit injection.

The idea. `i(G)² = i(2G)` where `2G` is two disjoint copies, so it suffices to inject
`I(2G) → I(G × K₂)`. An independent set `S` of `2G` fails to be independent in the cover
exactly on the *bad* edges `{uv ∈ E : u₀, v₁ ∈ S}`. Those form a **bipartite** subgraph of `G`
— each bad edge has exactly one endpoint in `{v : v₀ ∈ S}`, or `S` would not be independent —
so some `A ⊆ V` has every bad edge crossing it. Swapping the two copies of every vertex of `A`
repairs all the bad edges at once, and taking `A` to be *the first* such set in a fixed order
makes the map injective, because the bad edges are recoverable from the image.

Here `2G` and `G × K₂` are given as *relations* on `V × Bool` rather than as `SimpleGraph`
structures: independence only ever needs the relation, and this way there are no `symm` or
`loopless` obligations to discharge.
-/

open Finset

namespace PMC

section Swapping

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The independent sets of `G`. -/
def indepSets : Finset (Finset V) :=
  (univ : Finset (Finset V)).filter fun S => ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

/-- Adjacency in two disjoint copies of `G`: same copy, adjacent in `G`. -/
def twoAdj (p q : V × Bool) : Prop := G.Adj p.1 q.1 ∧ p.2 = q.2

/-- Adjacency in the bipartite double cover `G × K₂`: opposite copies, adjacent in `G`. -/
def coverAdj (p q : V × Bool) : Prop := G.Adj p.1 q.1 ∧ p.2 ≠ q.2

instance : DecidableRel (twoAdj G) := fun p q => by
  rw [twoAdj]
  infer_instance

instance : DecidableRel (coverAdj G) := fun p q => by
  rw [coverAdj]
  infer_instance

/-- The independent sets of two disjoint copies of `G`. -/
def indepTwo : Finset (Finset (V × Bool)) :=
  (univ : Finset (Finset (V × Bool))).filter fun S => ∀ p ∈ S, ∀ q ∈ S, ¬ twoAdj G p q

/-- The independent sets of the bipartite double cover. -/
def indepCover : Finset (Finset (V × Bool)) :=
  (univ : Finset (Finset (V × Bool))).filter fun S => ∀ p ∈ S, ∀ q ∈ S, ¬ coverAdj G p q

lemma mem_indepSets {S : Finset V} :
    S ∈ indepSets G ↔ ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v := by
  rw [indepSets, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

lemma mem_indepTwo {S : Finset (V × Bool)} :
    S ∈ indepTwo G ↔ ∀ p ∈ S, ∀ q ∈ S, ¬ twoAdj G p q := by
  rw [indepTwo, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

lemma mem_indepCover {S : Finset (V × Bool)} :
    S ∈ indepCover G ↔ ∀ p ∈ S, ∀ q ∈ S, ¬ coverAdj G p q := by
  rw [indepCover, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- The slice of a subset of `V × Bool` in one copy. -/
def slice (S : Finset (V × Bool)) (i : Bool) : Finset V :=
  (univ : Finset V).filter fun v => (v, i) ∈ S

lemma mem_slice {S : Finset (V × Bool)} {i : Bool} {v : V} :
    v ∈ slice S i ↔ (v, i) ∈ S := by
  rw [slice, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- **`i(2G) = i(G)²`.** An independent set of two disjoint copies is exactly a pair of
independent sets, one in each copy. -/
theorem card_indepTwo : #(indepTwo G) = #(indepSets G) * #(indepSets G) := by
  classical
  rw [← Finset.card_product]
  refine Finset.card_bij (fun S _ => (slice S false, slice S true)) ?_ ?_ ?_
  · intro S hS
    rw [mem_indepTwo] at hS
    rw [Finset.mem_product, mem_indepSets, mem_indepSets]
    constructor
    · intro u hu v hv hadj
      exact hS (u, false) (mem_slice.mp hu) (v, false) (mem_slice.mp hv) ⟨hadj, rfl⟩
    · intro u hu v hv hadj
      exact hS (u, true) (mem_slice.mp hu) (v, true) (mem_slice.mp hv) ⟨hadj, rfl⟩
  · intro S hS S' hS' h
    ext p
    obtain ⟨v, i⟩ := p
    have h1 : slice S false = slice S' false := congrArg Prod.fst h
    have h2 : slice S true = slice S' true := congrArg Prod.snd h
    cases i with
    | false =>
        rw [← mem_slice (S := S), ← mem_slice (S := S'), h1]
    | true =>
        rw [← mem_slice (S := S), ← mem_slice (S := S'), h2]
  · intro P hP
    rw [Finset.mem_product, mem_indepSets, mem_indepSets] at hP
    refine ⟨(P.1.image fun v => (v, false)) ∪ (P.2.image fun v => (v, true)), ?_, ?_⟩
    · rw [mem_indepTwo]
      intro p hp q hq hadj
      rw [mem_union, Finset.mem_image, Finset.mem_image] at hp hq
      obtain ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ := hp <;>
        obtain ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ := hq
      · exact hP.1 u hu v hv hadj.1
      · exact absurd hadj.2 (by simp)
      · exact absurd hadj.2 (by simp)
      · exact hP.2 u hu v hv hadj.1
    · have h1 : slice ((P.1.image fun v => (v, false)) ∪ (P.2.image fun v => (v, true)))
          false = P.1 := by
        ext v
        rw [mem_slice, mem_union, Finset.mem_image, Finset.mem_image]
        constructor
        · rintro (⟨u, hu, huv⟩ | ⟨u, -, huv⟩)
          · rw [Prod.mk.injEq] at huv
            exact huv.1 ▸ hu
          · rw [Prod.mk.injEq] at huv
            exact absurd huv.2 (by simp)
        · intro hv
          exact Or.inl ⟨v, hv, rfl⟩
      have h2 : slice ((P.1.image fun v => (v, false)) ∪ (P.2.image fun v => (v, true)))
          true = P.2 := by
        ext v
        rw [mem_slice, mem_union, Finset.mem_image, Finset.mem_image]
        constructor
        · rintro (⟨u, -, huv⟩ | ⟨u, hu, huv⟩)
          · rw [Prod.mk.injEq] at huv
            exact absurd huv.2 (by simp)
          · rw [Prod.mk.injEq] at huv
            exact huv.1 ▸ hu
        · intro hv
          exact Or.inr ⟨v, hv, rfl⟩
      rw [h1, h2]

/-! ### The bad edges, and a set they all cross -/

/-- An edge is **bad** for `S` if its first endpoint appears in copy `0` and its second in
copy `1` — exactly the pairs that stop `S` from being independent in the cover. -/
def BadEdge (S : Finset (V × Bool)) (u v : V) : Prop :=
  G.Adj u v ∧ (u, false) ∈ S ∧ (v, true) ∈ S

/-- `A` **crosses** every bad edge: one endpoint inside, one outside. -/
def Crossing (S : Finset (V × Bool)) (A : Finset V) : Prop :=
  ∀ u v : V, BadEdge G S u v → (u ∈ A ↔ v ∉ A)

/-- **The bad edges are bipartite**, witnessed by the copy-`0` slice: a bad edge has its first
endpoint there and — since `S` is independent in `2G` — its second endpoint not. -/
theorem crossing_slice {S : Finset (V × Bool)} (hS : S ∈ indepTwo G) :
    Crossing G S (slice S false) := by
  intro u v hbad
  obtain ⟨hadj, hu, hv⟩ := hbad
  have hu' : u ∈ slice S false := mem_slice.mpr hu
  have hv' : v ∉ slice S false := by
    intro hcon
    rw [mem_indepTwo] at hS
    exact hS (u, false) hu (v, false) (mem_slice.mp hcon) ⟨hadj, rfl⟩
  exact ⟨fun _ => hv', fun _ => hu'⟩

/-- Swapping the two copies of every vertex of `A`. -/
noncomputable def swapSet (A : Finset V) (S : Finset (V × Bool)) : Finset (V × Bool) := by
  classical
  exact (univ : Finset (V × Bool)).filter fun p =>
    if p.1 ∈ A then (p.1, !p.2) ∈ S else p ∈ S

lemma mem_swapSet {A : Finset V} {S : Finset (V × Bool)} {p : V × Bool} :
    p ∈ swapSet A S ↔ (if p.1 ∈ A then (p.1, !p.2) ∈ S else p ∈ S) := by
  classical
  rw [swapSet, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

lemma mem_swapSet_of_mem {A : Finset V} {S : Finset (V × Bool)} {v : V} {i : Bool}
    (hv : v ∈ A) : ((v, i) ∈ swapSet A S ↔ (v, !i) ∈ S) := by
  rw [mem_swapSet]
  simp only [if_pos hv]

lemma mem_swapSet_of_notMem {A : Finset V} {S : Finset (V × Bool)} {v : V} {i : Bool}
    (hv : v ∉ A) : ((v, i) ∈ swapSet A S ↔ (v, i) ∈ S) := by
  rw [mem_swapSet]
  simp only [if_neg hv]

/-- **Swapping is an involution**, which is what makes the map recoverable. -/
theorem swapSet_swapSet (A : Finset V) (S : Finset (V × Bool)) :
    swapSet A (swapSet A S) = S := by
  classical
  ext p
  obtain ⟨v, i⟩ := p
  by_cases hv : v ∈ A
  · rw [mem_swapSet_of_mem hv, mem_swapSet_of_mem hv, Bool.not_not]
  · rw [mem_swapSet_of_notMem hv, mem_swapSet_of_notMem hv]

/-- **Swapping repairs every bad edge**: the swapped set is independent in the cover.

Four cases on which endpoints lie in `A`. Two of them produce two vertices of `S` in the
*same* copy, contradicting independence in `2G`; the other two produce a bad edge whose
endpoints are on the same side of `A`, contradicting the crossing property. -/
theorem swapSet_mem_indepCover {S : Finset (V × Bool)} (hS : S ∈ indepTwo G) {A : Finset V}
    (hA : Crossing G S A) : swapSet A S ∈ indepCover G := by
  classical
  rw [mem_indepCover]
  rintro ⟨u, i⟩ hp ⟨v, j⟩ hq ⟨hadj, hij⟩
  rw [mem_indepTwo] at hS
  -- `i ≠ j` in `Bool` means one is `false` and the other `true`
  have hcase : (i = false ∧ j = true) ∨ (i = true ∧ j = false) := by
    cases i <;> cases j <;> simp_all
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · by_cases hu : u ∈ A
    · rw [mem_swapSet_of_mem hu] at hp
      by_cases hv : v ∈ A
      · rw [mem_swapSet_of_mem hv] at hq
        -- `(v, false), (u, true) ∈ S`: a bad edge from `v` to `u`, but both lie in `A`
        have := hA v u ⟨hadj.symm, hq, hp⟩
        exact absurd hu (by simpa [hv] using this)
      · rw [mem_swapSet_of_notMem hv] at hq
        exact hS (u, true) hp (v, true) hq ⟨hadj, rfl⟩
    · rw [mem_swapSet_of_notMem hu] at hp
      by_cases hv : v ∈ A
      · rw [mem_swapSet_of_mem hv] at hq
        exact hS (u, false) hp (v, false) hq ⟨hadj, rfl⟩
      · rw [mem_swapSet_of_notMem hv] at hq
        -- `(u, false), (v, true) ∈ S`: a bad edge with both endpoints outside `A`
        have := hA u v ⟨hadj, hp, hq⟩
        exact hv (by simpa [hu] using this)
  · by_cases hu : u ∈ A
    · rw [mem_swapSet_of_mem hu] at hp
      by_cases hv : v ∈ A
      · rw [mem_swapSet_of_mem hv] at hq
        have := hA u v ⟨hadj, hp, hq⟩
        exact absurd hv (by simpa [hu] using this)
      · rw [mem_swapSet_of_notMem hv] at hq
        exact hS (u, false) hp (v, false) hq ⟨hadj, rfl⟩
    · rw [mem_swapSet_of_notMem hu] at hp
      by_cases hv : v ∈ A
      · rw [mem_swapSet_of_mem hv] at hq
        exact hS (u, true) hp (v, true) hq ⟨hadj, rfl⟩
      · rw [mem_swapSet_of_notMem hv] at hq
        have := hA v u ⟨hadj.symm, hq, hp⟩
        exact hu (by simpa [hv] using this)


/-! ### Recovering the swap, and injectivity -/

/-- The same-copy adjacent pairs of `T` — the data the *image* exposes. -/
def SameEdge (T : Finset (V × Bool)) (u v : V) : Prop :=
  G.Adj u v ∧ ∃ i : Bool, (u, i) ∈ T ∧ (v, i) ∈ T

/-- **The image remembers the bad edges.** After swapping along a crossing set, the same-copy
adjacent pairs of the image are exactly the bad edges of the original, in either orientation.
This is what makes the choice of `A` recoverable. -/
theorem sameEdge_swapSet {S : Finset (V × Bool)} (hS : S ∈ indepTwo G) {A : Finset V}
    (hA : Crossing G S A) (u v : V) :
    SameEdge G (swapSet A S) u v ↔ (BadEdge G S u v ∨ BadEdge G S v u) := by
  classical
  rw [mem_indepTwo] at hS
  constructor
  · rintro ⟨hadj, i, hu, hv⟩
    by_cases hua : u ∈ A
    · rw [mem_swapSet_of_mem hua] at hu
      by_cases hva : v ∈ A
      · rw [mem_swapSet_of_mem hva] at hv
        exact absurd (hS (u, !i) hu (v, !i) hv ⟨hadj, rfl⟩) (by simp)
      · rw [mem_swapSet_of_notMem hva] at hv
        cases i with
        | false => exact Or.inr ⟨hadj.symm, hv, hu⟩
        | true => exact Or.inl ⟨hadj, hu, hv⟩
    · rw [mem_swapSet_of_notMem hua] at hu
      by_cases hva : v ∈ A
      · rw [mem_swapSet_of_mem hva] at hv
        cases i with
        | false => exact Or.inl ⟨hadj, hu, hv⟩
        | true => exact Or.inr ⟨hadj.symm, hv, hu⟩
      · rw [mem_swapSet_of_notMem hva] at hv
        exact absurd (hS (u, i) hu (v, i) hv ⟨hadj, rfl⟩) (by simp)
  · rintro (⟨hadj, hu, hv⟩ | ⟨hadj, hv, hu⟩)
    · -- a bad edge `u → v`: crossing puts exactly one endpoint in `A`
      have hcross := hA u v ⟨hadj, hu, hv⟩
      by_cases hua : u ∈ A
      · have hva : v ∉ A := hcross.mp hua
        exact ⟨hadj, true, by rw [mem_swapSet_of_mem hua]; exact hu,
          by rw [mem_swapSet_of_notMem hva]; exact hv⟩
      · have hva : v ∈ A := by
          by_contra hcon
          exact hua (hcross.mpr hcon)
        exact ⟨hadj, false, by rw [mem_swapSet_of_notMem hua]; exact hu,
          by rw [mem_swapSet_of_mem hva]; exact hv⟩
    · have hcross := hA v u ⟨hadj, hv, hu⟩
      by_cases hva : v ∈ A
      · have hua : u ∉ A := hcross.mp hva
        refine ⟨hadj.symm, true, ?_, ?_⟩
        · rw [mem_swapSet_of_notMem hua]
          exact hu
        · rw [mem_swapSet_of_mem hva]
          simpa using hv
      · have hua : u ∈ A := by
          by_contra hcon
          exact hva (hcross.mpr hcon)
        refine ⟨hadj.symm, false, ?_, ?_⟩
        · rw [mem_swapSet_of_mem hua]
          simpa using hu
        · rw [mem_swapSet_of_notMem hva]
          exact hv

/-- The crossing condition stated on the image's data. -/
def CrossingT (T : Finset (V × Bool)) (A : Finset V) : Prop :=
  ∀ u v : V, SameEdge G T u v → (u ∈ A ↔ v ∉ A)

/-- **The crossing sets of `S` are exactly those of its image**, so the whole family — and
hence the canonical choice made from it — is recoverable. -/
theorem crossing_iff_crossingT {S : Finset (V × Bool)} (hS : S ∈ indepTwo G) {A : Finset V}
    (hA : Crossing G S A) (A' : Finset V) :
    Crossing G S A' ↔ CrossingT G (swapSet A S) A' := by
  constructor
  · intro hA' u v hsame
    rcases (sameEdge_swapSet G hS hA u v).mp hsame with h | h
    · exact hA' u v h
    · have := hA' v u h
      constructor
      · intro hu hcon
        exact absurd hu (this.mp hcon)
      · intro hv
        by_contra hcon
        exact hv (this.mpr hcon)
  · intro hA' u v hbad
    exact hA' u v ((sameEdge_swapSet G hS hA u v).mpr (Or.inl hbad))


/-! ### Lemma 10.4.13 -/

/-- An arbitrary but fixed indexing of the subsets of `V`, used only to make a canonical
choice — the notes' "fix an arbitrary order on all subsets of `V`". -/
noncomputable def idxOf (A : Finset V) : ℕ := (Fintype.equivFin (Finset V) A : ℕ)

/-- The canonical member of a family of subsets: the one of least index. **A function of the
family alone**, which is exactly what injectivity needs. -/
noncomputable def pickMin (F : Finset (Finset V)) : Finset V := by
  classical
  exact if h : F.Nonempty then (F.exists_min_image idxOf h).choose else ∅

lemma pickMin_mem {F : Finset (Finset V)} (h : F.Nonempty) : pickMin F ∈ F := by
  classical
  rw [pickMin, dif_pos h]
  exact (F.exists_min_image idxOf h).choose_spec.1

/-- The sets crossing every bad edge of `S`. -/
noncomputable def crossings (S : Finset (V × Bool)) : Finset (Finset V) := by
  classical
  exact (univ : Finset (Finset V)).filter fun A => Crossing G S A

/-- The same family, read off the image. -/
noncomputable def crossingsT (T : Finset (V × Bool)) : Finset (Finset V) := by
  classical
  exact (univ : Finset (Finset V)).filter fun A => CrossingT G T A

lemma mem_crossings {S : Finset (V × Bool)} {A : Finset V} :
    A ∈ crossings G S ↔ Crossing G S A := by
  classical
  rw [crossings, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

lemma mem_crossingsT {T : Finset (V × Bool)} {A : Finset V} :
    A ∈ crossingsT G T ↔ CrossingT G T A := by
  classical
  rw [crossingsT, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

lemma crossings_nonempty {S : Finset (V × Bool)} (hS : S ∈ indepTwo G) :
    (crossings G S).Nonempty :=
  ⟨slice S false, (mem_crossings G).mpr (crossing_slice G hS)⟩

/-- **The injection**: swap along the canonically chosen crossing set. -/
noncomputable def swapMap (S : Finset (V × Bool)) : Finset (V × Bool) :=
  swapSet (pickMin (crossings G S)) S

/-- **Lemma 10.4.13.** `i(G)² ≤ i(G × K₂)`, by the bipartite swapping trick.

The map sends an independent set `S` of `2G` to its swap along the canonically chosen set
crossing all of `S`'s bad edges. Swapping repairs the bad edges, so the image is independent
in the cover; and the image remembers the bad edges
(`PMC.sameEdge_swapSet`), hence the whole crossing family and so the chosen set, so swapping
back recovers `S`. -/
theorem card_indepSets_sq_le_card_indepCover :
    #(indepSets G) * #(indepSets G) ≤ #(indepCover G) := by
  classical
  rw [← card_indepTwo]
  refine Finset.card_le_card_of_injOn (swapMap G) ?_ ?_
  · intro S hS
    rw [mem_coe] at hS
    exact swapSet_mem_indepCover G hS ((mem_crossings G).mp (pickMin_mem (crossings_nonempty G hS)))
  · intro S hS S' hS' heq
    rw [mem_coe] at hS hS'
    have hA : Crossing G S (pickMin (crossings G S)) :=
      (mem_crossings G).mp (pickMin_mem (crossings_nonempty G hS))
    have hA' : Crossing G S' (pickMin (crossings G S')) :=
      (mem_crossings G).mp (pickMin_mem (crossings_nonempty G hS'))
    -- the crossing families are both the one read off the common image
    have hfam : crossings G S = crossings G S' := by
      have h1 : crossings G S = crossingsT G (swapMap G S) := by
        ext A''
        rw [mem_crossings, mem_crossingsT]
        exact crossing_iff_crossingT G hS hA A''
      have h2 : crossings G S' = crossingsT G (swapMap G S') := by
        ext A''
        rw [mem_crossings, mem_crossingsT]
        exact crossing_iff_crossingT G hS' hA' A''
      rw [h1, h2, heq]
    -- so the chosen sets agree, and swapping back is the inverse
    have hpick : pickMin (crossings G S) = pickMin (crossings G S') := by rw [hfam]
    calc S = swapSet (pickMin (crossings G S)) (swapMap G S) := by
          rw [swapMap, swapSet_swapSet]
      _ = swapSet (pickMin (crossings G S')) (swapMap G S') := by rw [hpick, heq]
      _ = S' := by rw [swapMap, swapSet_swapSet]


end Swapping

end PMC
