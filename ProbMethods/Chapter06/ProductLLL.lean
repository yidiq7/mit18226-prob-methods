import ProbMethods.Chapter06.LocalLemma
import ProbMethods.Product

/-!
# §6.3–§6.5 — the local lemma on a product sample space

§6.2 could run the local lemma on `Finset V`, because a 2-colouring *is* a subset and
`PMC.DeterminedBy` applies. The remaining applications choose one value per coordinate —
§6.3 one vertex from each part of a partition, §6.4 a label in `ZMod k` for each vertex — so
their sample space is a product `ι → β`.

`PMC.exists_avoiding_of_lll` is the local lemma packaged for that setting: supply the events,
the block of coordinates each one depends on, a bound `p` on their probabilities and a bound
`d` on how many other blocks each block meets, and it returns a point of the product avoiding
every event. Independence is discharged internally from
`PMC.wprob_unifProd_mul_of_determinedOn`, so an application never has to mention `wprob`.

This is the product-space twin of §6.2's `PMC.exists_two_coloring_of_local_lemma`, and the
three remaining Chapter 6 applications all go through it.
-/

open Finset

namespace PMC

section ProductLLL

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The product analogue of `PMC.determinedBy_noneOf`: "none of the events in `T` occurs"
depends only on a block containing all of their blocks. -/
theorem determinedOn_noneOf {A : κ → Finset (ι → β)} {C : κ → Finset ι}
    (hA : ∀ c, DeterminedOn (C c) (A c)) {D : Finset ι} {T : Finset κ}
    (hT : ∀ c ∈ T, C c ⊆ D) : DeterminedOn D (noneOf A T) := by
  classical
  revert hT
  induction T using Finset.induction_on with
  | empty =>
      intro _
      simpa using determinedOn_univ_event (β := β) D
  | @insert c T _ ih =>
      intro hT
      rw [noneOf_insert]
      exact ((hA c).mono (hT c (mem_insert_self c T))).compl.inter
        (ih fun c' hc' => hT c' (mem_insert_of_mem hc'))

variable [Nonempty β]

/-- **The Lovász local lemma on a product sample space.**

Each event `A c` depends only on the coordinates in `C c`; events whose blocks are disjoint
are genuinely independent, which is what `hfar` records. Given `e p (d+1) ≤ 1`, some point of
the product avoids every event. -/
theorem exists_avoiding_of_lll (A : κ → Finset (ι → β)) (C : κ → Finset ι)
    (hA : ∀ c, DeterminedOn (C c) (A c))
    (N : κ → Finset κ) {d : ℕ} (hd : 0 < d) {p : ℝ} (hp0 : 0 ≤ p)
    (hself : ∀ c, c ∉ N c)
    (hdeg : ∀ c, #(N c) ≤ d)
    (hfar : ∀ c c' : κ, c' ∉ insert c (N c) → Disjoint (C c) (C c'))
    (hprob : ∀ c, wprob (unifProd ι β) (A c) ≤ p)
    (hep : Real.exp 1 * p * (d + 1) ≤ 1) :
    ∃ f : ι → β, ∀ c, f ∉ A c := by
  classical
  have hindep : ∀ (c : κ) (T : Finset κ), Disjoint T (insert c (N c)) →
      wprob (unifProd ι β) (A c ∩ noneOf A T)
        = wprob (unifProd ι β) (A c) * wprob (unifProd ι β) (noneOf A T) := by
    intro c T hT
    refine wprob_unifProd_mul_of_determinedOn (hA c) ?_
    refine determinedOn_noneOf hA ?_
    intro c' hc' i hi
    have hdis : Disjoint (C c) (C c') := hfar c c' (Finset.disjoint_left.mp hT hc')
    rw [mem_sdiff]
    exact ⟨mem_univ i, fun hic => Finset.disjoint_left.mp hdis hic hi⟩
  have hpos := lovasz_local_lemma_symmetric (unifProd ι β) unifProd_nonneg sum_unifProd
    A N hd hp0 hself hdeg hindep hprob hep
  have hne : (noneOf A (univ : Finset κ)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (noneOf A (univ : Finset κ)) with h | h
    · rw [h, wprob_empty] at hpos
      linarith
    · exact h
  obtain ⟨f, hf⟩ := hne
  exact ⟨f, fun c => mem_noneOf.mp hf c (mem_univ c)⟩

end ProductLLL

/-! ### §6.3's bridge: trimming and enumerating the parts

Theorem 6.3.1 partitions the vertices into parts of size *at least* `2eΔ`. The notes' first
move is "we may assume `|Vᵢ| = k := ⌈2eΔ⌉`, or else remove some vertices", and that
reduction is what makes the sample space a **uniform** product: with all parts the same
size, enumerating each by `Fin k` turns a choice of one vertex per part into a point of
`Fin r → Fin k`, which is what `PMC.exists_avoiding_of_lll` runs on. Without the trimming
the parts have different sizes and the weight would be a product of `1/|Vᵢ|`.

`PMC.exists_enumeration` performs both steps at once.
-/

section Enumeration

variable {V : Type*} [DecidableEq V]

/-- **Trim and enumerate.** Pairwise disjoint parts, each of size at least `k`, admit an
array `w` listing `k` distinct vertices from each part, with vertices of different parts
distinct.

A transversal built from `w` is automatically a transversal of the original parts, since
`w i a ∈ part i`; this is why trimming loses nothing. -/
theorem exists_enumeration {r k : ℕ} (part : Fin r → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (part i) (part j))
    (hcard : ∀ i, k ≤ #(part i)) :
    ∃ w : Fin r → Fin k → V,
      (∀ i a, w i a ∈ part i) ∧ (∀ i, Function.Injective (w i)) ∧
      (∀ i j a b, i ≠ j → w i a ≠ w j b) := by
  classical
  -- trim each part to exactly `k` vertices
  choose q hqsub hqcard using fun i => Finset.exists_subset_card_eq (hcard i)
  -- enumerate the trimmed part by `Fin k`
  set w : Fin r → Fin k → V :=
    fun i a => ((q i).equivFin.symm (finCongr (hqcard i).symm a) : V) with hwdef
  have hmem : ∀ i a, w i a ∈ q i := by
    intro i a
    rw [hwdef]
    exact Finset.coe_mem _
  refine ⟨w, fun i a => hqsub i (hmem i a), ?_, ?_⟩
  · intro i a a' h
    rw [hwdef] at h
    have h' := Subtype.val_injective h
    exact (finCongr (hqcard i).symm).injective ((q i).equivFin.symm.injective h')
  · intro i j a b hij hval
    have hi : w i a ∈ part i := hqsub i (hmem i a)
    have hj : w j b ∈ part j := hqsub j (hmem j b)
    rw [hval] at hi
    exact Finset.disjoint_left.mp (hdisj i j hij) hi hj

end Enumeration

/-! ### §6.3's counting core

The dependency degree in Theorem 6.3.1 is bounded by counting *ordered adjacent pairs whose
first vertex lies in the two relevant parts*. That count is `#S · Δ` for a set `S` of
vertices in a graph of maximum degree `Δ`, which is what `PMC.card_adj_pairs_le` gives.

With `S = Vᵢ ∪ V_j` of size `2k`, this is the `2kΔ` of the notes.
-/

section AdjacentPairs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The ordered adjacent pairs starting in `S` number at most `#S · Δ`.**

Fibre over the first coordinate; each fibre injects into that vertex's neighbourhood. -/
theorem card_adj_pairs_le (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (S : Finset V) :
    #((univ : Finset (V × V)).filter fun q => q.1 ∈ S ∧ G.Adj q.1 q.2) ≤ #S * Δ := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun q : V × V => q.1) (t := S) (fun q hq => (mem_filter.mp hq).2.1)]
  calc ∑ x ∈ S, #(((univ : Finset (V × V)).filter
        fun q => q.1 ∈ S ∧ G.Adj q.1 q.2).filter fun q => q.1 = x)
      ≤ ∑ _x ∈ S, Δ := by
        refine Finset.sum_le_sum fun x _ => ?_
        have hfib : #(((univ : Finset (V × V)).filter
            fun q => q.1 ∈ S ∧ G.Adj q.1 q.2).filter fun q => q.1 = x)
            ≤ #(G.neighborFinset x) := by
          refine Finset.card_le_card_of_injOn (fun q => q.2) ?_ ?_
          · intro q hq
            rw [mem_coe, mem_filter, mem_filter] at hq
            simp only [mem_coe, SimpleGraph.mem_neighborFinset]
            exact hq.2 ▸ hq.1.2.2
          · intro q hq q' hq' h
            rw [mem_coe, mem_filter] at hq hq'
            exact Prod.ext (hq.2.trans hq'.2.symm) h
        exact le_trans hfib (hΔ x)
    _ = #S * Δ := by rw [Finset.sum_const, smul_eq_mul]

end AdjacentPairs

/-! ### §6.4's counting core: the dependency degree of a digraph

For §6.4 the bad event at `v` is "no out-neighbour of `v` carries the next label", so it is
determined on `{v} ∪ N⁺(v)`. Two such blocks meet in one of three ways, and the notes count
them exactly that way: at most `Δ` stepping backward, `δ` stepping forward, and `δ(Δ-1)`
stepping forward and then backward. The last is where the `-1` comes from — `v` is itself an
in-neighbour of each of its out-neighbours, so it must be excluded — and it is what turns
`Δ + δ + δ(Δ-1)` into `Δ + δΔ`.
-/

section DigraphDependency

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The coordinates §6.4's bad event at `v` depends on: `v` and its out-neighbours. -/
abbrev dblk (r : V → V → Prop) [DecidableRel r] (v : V) : Finset V :=
  insert v ((univ : Finset V).filter fun u => r v u)

/-- **The dependency degree of a digraph is at most `Δ + δΔ`.**

`δ` bounds out-degrees, `Δ` bounds in-degrees. `1 ≤ Δ` is needed only to fold
`δ + δ(Δ-1)` into `δΔ`; with `Δ = 0` the relation is empty and every count is zero anyway.

This is the *first-pass* bound, which is what the straightforward local lemma needs. The
notes then observe a smaller valid dependency digraph — their "final trick" — to reach
Theorem 6.4.3's exact constant `k ≤ δ/(1 + log(1 + δΔ))`; without it one gets
`k ≤ δ/(1 + log(1 + Δ + δΔ))`. -/
theorem card_digraph_dependency_le (r : V → V → Prop) [DecidableRel r] {δ D : ℕ}
    (hD : 1 ≤ D)
    (hout : ∀ v, #((univ : Finset V).filter fun u => r v u) ≤ δ)
    (hin : ∀ v, #((univ : Finset V).filter fun u => r u v) ≤ D)
    (v : V) :
    #((univ : Finset V).filter fun w => w ≠ v ∧ ¬ Disjoint (dblk r v) (dblk r w))
      ≤ D + δ * D := by
  classical
  set B := (univ : Finset V).filter fun w => r w v with hB
  set F := (univ : Finset V).filter fun u => r v u with hF
  set T := F.biUnion (fun u => ((univ : Finset V).filter fun w => r w u).erase v) with hT
  -- the three ways two blocks can meet
  have hsub : (univ : Finset V).filter
      (fun w => w ≠ v ∧ ¬ Disjoint (dblk r v) (dblk r w)) ⊆ B ∪ F ∪ T := by
    intro w hw
    rw [mem_filter] at hw
    obtain ⟨-, hwv, hdis⟩ := hw
    rw [Finset.not_disjoint_iff] at hdis
    obtain ⟨x, hxv, hxw⟩ := hdis
    rw [Finset.mem_insert, mem_filter] at hxv hxw
    rw [Finset.mem_union, Finset.mem_union]
    rcases hxv with rfl | ⟨-, hrvx⟩
    · rcases hxw with rfl | ⟨-, hrwx⟩
      · exact absurd rfl hwv
      · exact Or.inl (Or.inl (by rw [hB, mem_filter]; exact ⟨mem_univ _, hrwx⟩))
    · rcases hxw with rfl | ⟨-, hrwx⟩
      · exact Or.inl (Or.inr (by rw [hF, mem_filter]; exact ⟨mem_univ _, hrvx⟩))
      · refine Or.inr ?_
        rw [hT, Finset.mem_biUnion]
        exact ⟨x, by rw [hF, mem_filter]; exact ⟨mem_univ _, hrvx⟩,
          Finset.mem_erase.mpr ⟨hwv, by rw [mem_filter]; exact ⟨mem_univ _, hrwx⟩⟩⟩
  -- and their sizes
  have hTcard : #T ≤ δ * (D - 1) := by
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_card_nsmul F _ (D - 1) ?_) ?_
    · intro u hu
      rw [hF, mem_filter] at hu
      have hvmem : v ∈ (univ : Finset V).filter fun w => r w u := by
        rw [mem_filter]
        exact ⟨mem_univ _, hu.2⟩
      rw [Finset.card_erase_of_mem hvmem]
      have := hin u
      omega
    · rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ (hout v)
  have hBcard : #B ≤ D := hin v
  have hFcard : #F ≤ δ := hout v
  calc #((univ : Finset V).filter fun w => w ≠ v ∧ ¬ Disjoint (dblk r v) (dblk r w))
      ≤ #(B ∪ F ∪ T) := Finset.card_le_card hsub
    _ ≤ #(B ∪ F) + #T := Finset.card_union_le _ _
    _ ≤ #B + #F + #T := by
        have := Finset.card_union_le B F
        omega
    _ ≤ D + δ + δ * (D - 1) := by omega
    _ = D + δ * D := by
        cases D with
        | zero => omega
        | succ d => simp; ring

/-- §6.4's bad event at `v`: no out-neighbour of `v` carries the next label. -/
abbrev dEvent (r : V → V → Prop) [DecidableRel r] {k : ℕ} [NeZero k] (v : V) :
    Finset (V → ZMod k) :=
  (univ : Finset (V → ZMod k)).filter fun x => ∀ u, r v u → x u ≠ x v + 1

/-- **§6.4's probability bound**: `P(A_v) ≤ ((k-1)/k) ^ δ`.

The event is not of the form "each coordinate in a block satisfies a fixed predicate",
because what the out-neighbours must avoid depends on `x v`. Splitting on the value of
`x v` fixes that: each piece *is* of that form, so
`PMC.wprob_unifProd_forall` applies, and the `k` pieces each have probability
`(1/k)((k-1)/k)^δ`. Subadditivity over the `k` pieces then gives the bound — no exact
computation is needed, since the local lemma only wants an upper bound. -/
theorem wprob_dEvent_le (r : V → V → Prop) [DecidableRel r] {k δ : ℕ} [NeZero k]
    (hloop : ∀ v, ¬ r v v)
    (hout : ∀ v, #((univ : Finset V).filter fun u => r v u) = δ) (v : V) :
    wprob (unifProd V (ZMod k)) (dEvent r v) ≤ (((k : ℝ) - 1) / k) ^ δ := by
  classical
  have hk : Fintype.card (ZMod k) = k := ZMod.card k
  have hkpos : 0 < k := Nat.pos_of_neZero k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  set N := (univ : Finset V).filter fun u => r v u with hN
  have hvN : v ∉ N := by
    rw [hN, mem_filter]
    exact fun h => hloop v h.2
  -- split on the value of `x v`
  have hsub : dEvent r v ⊆ (univ : Finset (ZMod k)).biUnion
      (fun a => (univ : Finset (V → ZMod k)).filter fun x =>
        ∀ i ∈ insert v N, (if i = v then x i = a else x i ≠ a + 1)) := by
    intro x hx
    rw [mem_filter] at hx
    rw [Finset.mem_biUnion]
    refine ⟨x v, mem_univ _, ?_⟩
    rw [mem_filter]
    refine ⟨mem_univ _, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · rw [if_pos rfl]
    · rw [hN, mem_filter] at hi'
      have hri : r v i := hi'.2
      have hiv : i ≠ v := by
        intro h
        subst h
        exact hloop _ hri
      rw [if_neg hiv]
      exact hx.2 i hri
  -- each piece has probability `(1/k) ((k-1)/k) ^ δ`
  have hpiece : ∀ a : ZMod k,
      wprob (unifProd V (ZMod k)) ((univ : Finset (V → ZMod k)).filter fun x =>
        ∀ i ∈ insert v N, (if i = v then x i = a else x i ≠ a + 1))
      = (1 / (k : ℝ)) * (((k : ℝ) - 1) / k) ^ δ := by
    intro a
    -- `P` must be given explicitly: matching `?P i (f i)` against a body where `f i`
    -- occurs in both branches of an `if` is beyond `rw`'s higher-order unification
    rw [wprob_unifProd_forall (C := insert v N)
      (P := fun i b => if i = v then b = a else b ≠ a + 1),
      Finset.prod_insert hvN]
    -- the `v` factor: `if v = v` is under a binder, so let `simp` collapse it
    have h1 : #((univ : Finset (ZMod k)).filter
        fun b => (if v = v then b = a else b ≠ a + 1)) = 1 := by
      simp [Finset.filter_eq']
    have h2 : ∀ u ∈ N, ((#((univ : Finset (ZMod k)).filter
        fun b => (if u = v then b = a else b ≠ a + 1)) : ℝ)) / Fintype.card (ZMod k)
        = ((k : ℝ) - 1) / k := by
      intro u hu
      have huv : u ≠ v := by
        intro h
        subst h
        exact hvN hu
      have hcard : #((univ : Finset (ZMod k)).filter
          fun b => (if u = v then b = a else b ≠ a + 1)) = k - 1 := by
        simp only [if_neg huv]
        rw [Finset.filter_ne' univ (a + 1), Finset.card_erase_of_mem (mem_univ _),
          card_univ, hk]
      rw [hcard, hk]
      have h1k : (1 : ℕ) ≤ k := hkpos
      rw [Nat.cast_sub h1k]
      norm_num
    rw [Finset.prod_congr rfl h2, Finset.prod_const, hout v, hk, h1]
    norm_num
  calc wprob (unifProd V (ZMod k)) (dEvent r v)
      ≤ wprob (unifProd V (ZMod k)) ((univ : Finset (ZMod k)).biUnion
          (fun a => (univ : Finset (V → ZMod k)).filter fun x =>
            ∀ i ∈ insert v N, (if i = v then x i = a else x i ≠ a + 1))) :=
        wprob_mono unifProd_nonneg hsub
    _ ≤ ∑ a : ZMod k, wprob (unifProd V (ZMod k))
          ((univ : Finset (V → ZMod k)).filter fun x =>
            ∀ i ∈ insert v N, (if i = v then x i = a else x i ≠ a + 1)) :=
        wprob_biUnion_le unifProd_nonneg _ _
    _ = (((k : ℝ) - 1) / k) ^ δ := by
        rw [Finset.sum_congr rfl fun a _ => hpiece a, Finset.sum_const, card_univ, hk,
          nsmul_eq_mul]
        field_simp

end DigraphDependency

end PMC
