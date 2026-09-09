import ProbMethods.Basic
import ProbMethods.Weighted
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# §3.4 — High girth and high chromatic number (Theorem 3.4.1)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 3.4.1 (Erdős 1959): for all `k` and
`ℓ` there is a graph with girth `> ℓ` and chromatic number `> k` — a graph that is locally
tree-like yet not colourable with few colours, so high chromatic number cannot be certified
locally.

The four pieces, in order:

* `PMC.lt_chromaticNumber_of_mul_indepNum_lt` — `χ(G) > #V / α(G)`, because the colour classes
  of a proper colouring are independent sets and they partition `V`. Mathlib has `indepNum` and
  `chromaticNumber` but not this inequality.
* `PMC.support_mem_badSets` — the *deterministic* heart. A cycle of length `≤ ℓ` has a vertex
  set `t` with `3 ≤ #t ≤ ℓ` spanning at least `#t` edges. Replacing "carries a short cycle" by
  that plain edge count is what lets the first moment method reach it: no cyclic orderings, no
  modular index arithmetic, and the probabilistic side never mentions walks.
* `PMC.sum_bweight_card_badSets_le` and `PMC.sum_bweight_indep_le` — the two moments, both
  instances of machinery already in `ProbMethods/Weighted.lean`.
* `PMC.exists_girth_chromatic_of_good` — the alteration: delete the least vertex of every bad
  set. No short cycle survives, more than `n/2` vertices remain, and the independence number
  only drops.
-/

open Finset

namespace PMC

section ColourClasses

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **A colour class is an independent set.** -/
lemma isIndepSet_colorClass {m : ℕ} (C : G.Coloring (Fin m)) (i : Fin m) :
    G.IsIndepSet ((univ.filter fun v => C v = i : Finset V) : Set V) := by
  intro u hu v hv huv hadj
  rw [Finset.mem_coe, mem_filter] at hu hv
  exact C.valid hadj (hu.2.trans hv.2.symm)

/-- **`#V ≤ m · α(G)` for every `m`-colouring**: the `m` colour classes are independent sets,
each of size at most the independence number, and they partition `V`. -/
lemma card_le_mul_indepNum_of_colorable {m : ℕ} (h : G.Colorable m) :
    Fintype.card V ≤ m * G.indepNum := by
  classical
  obtain ⟨C⟩ := h
  have hpart : #(univ : Finset V)
      = ∑ i : Fin m, #(univ.filter fun v => C v = i) :=
    Finset.card_eq_sum_card_fiberwise fun v _ => mem_univ (C v)
  have hle : ∀ i : Fin m, #(univ.filter fun v => C v = i) ≤ G.indepNum := fun i =>
    SimpleGraph.IsIndepSet.card_le_indepNum (isIndepSet_colorClass G C i)
  calc Fintype.card V = #(univ : Finset V) := (card_univ).symm
    _ = ∑ i : Fin m, #(univ.filter fun v => C v = i) := hpart
    _ ≤ ∑ _i : Fin m, G.indepNum := Finset.sum_le_sum fun i _ => hle i
    _ = m * G.indepNum := by rw [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The chromatic number is at least `#V / α(G)`**, in the form used by Theorem 3.4.1: if
`k · α(G) < #V` then more than `k` colours are needed. -/
theorem lt_chromaticNumber_of_mul_indepNum_lt {k : ℕ}
    (h : k * G.indepNum < Fintype.card V) : (k : ℕ∞) < G.chromaticNumber := by
  classical
  have hstep : ∀ m : ℕ, G.Colorable m → k + 1 ≤ m := by
    intro m hm
    by_contra hcon
    have hmk : m ≤ k := by omega
    have := card_le_mul_indepNum_of_colorable G hm
    have hmono : m * G.indepNum ≤ k * G.indepNum := Nat.mul_le_mul_right _ hmk
    omega
  have h1 : ((k + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber := by
    rw [SimpleGraph.le_chromaticNumber_iff_colorable]
    intro m hm
    exact_mod_cast hstep m hm
  refine lt_of_lt_of_le ?_ h1
  exact_mod_cast Nat.lt_succ_self k

end ColourClasses

section BadSets

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph whose edges are the non-loop members of `X`. -/
def graphOfEdges (X : Finset (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet {e | e ∈ X}

noncomputable instance (X : Finset (Sym2 V)) : DecidableRel (graphOfEdges X).Adj :=
  fun _ _ => Classical.dec _

lemma graphOfEdges_adj {X : Finset (Sym2 V)} {u v : V} :
    (graphOfEdges X).Adj u v ↔ (s(u, v) ∈ X ∧ u ≠ v) := by
  rw [graphOfEdges, SimpleGraph.fromEdgeSet_adj]
  simp

/-- A non-loop edge with both ends in `t` is spanned by `t`. -/
lemma mem_spannedEdges_of_forall_mem {t : Finset V} {e : Sym2 V}
    (h : ∀ v ∈ e, v ∈ t) (hd : ¬ e.IsDiag) : e ∈ spannedEdges t := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [mem_spannedEdges]
    refine ⟨a, h a (by simp), b, h b (by simp), ?_, rfl⟩
    simpa using hd

/-- **Vertex sets that could carry a short cycle**: `3 ≤ #t ≤ ℓ` and at least `#t` of the
`C(#t,2)` pairs inside `t` are edges. A cycle of length `≤ ℓ` has such a vertex set, and this
condition — unlike "carries a cycle" — is a plain count of edges, so the first-moment method
reaches it with no walks and no cyclic orderings. -/
def badSets (ℓ : ℕ) (X : Finset (Sym2 V)) : Finset (Finset V) :=
  (univ : Finset (Finset V)).filter fun t => 3 ≤ #t ∧ #t ≤ ℓ ∧ #t ≤ #(spannedEdges t ∩ X)

lemma mem_badSets {ℓ : ℕ} {X : Finset (Sym2 V)} {t : Finset V} :
    t ∈ badSets ℓ X ↔ 3 ≤ #t ∧ #t ≤ ℓ ∧ #t ≤ #(spannedEdges t ∩ X) := by
  simp [badSets]

/-- The edges of a walk are edges of the graph spanned by its support. -/
lemma edges_toFinset_subset {X : Finset (Sym2 V)} {u v : V}
    (w : (graphOfEdges X).Walk u v) :
    w.edges.toFinset ⊆ spannedEdges w.support.toFinset ∩ X := by
  intro e he
  rw [List.mem_toFinset] at he
  revert he
  induction e using Sym2.ind with
  | _ a b =>
    intro he
    have hadj : (graphOfEdges X).Adj a b :=
      (SimpleGraph.mem_edgeSet _).mp (w.edges_subset_edgeSet he)
    rw [graphOfEdges_adj] at hadj
    refine Finset.mem_inter.mpr ⟨mem_spannedEdges.mpr ⟨a, ?_, b, ?_, hadj.2, rfl⟩, hadj.1⟩
    · rw [List.mem_toFinset]
      exact w.fst_mem_support_of_mem_edges he
    · rw [List.mem_toFinset]
      exact w.snd_mem_support_of_mem_edges he

/-- **The support of a short cycle is a bad set.**

Its `L` edges are distinct (`SimpleGraph.Walk.IsCycle.edges_nodup`), lie inside its support,
and are edges of the graph; and the support has exactly `L` vertices, because for a closed walk
the starting vertex reappears in the tail, whose vertices are distinct. -/
lemma support_mem_badSets {ℓ : ℕ} {X : Finset (Sym2 V)} {u : V}
    (w : (graphOfEdges X).Walk u u) (hc : w.IsCycle) (hlen : w.length ≤ ℓ) :
    w.support.toFinset ∈ badSets ℓ X := by
  classical
  -- the starting vertex reappears in the tail
  have hnil : ¬ w.Nil := hc.not_nil
  have humem : u ∈ w.support.tail := by
    rw [← SimpleGraph.Walk.support_tail_of_not_nil w hnil]
    exact SimpleGraph.Walk.end_mem_support _
  have hsupp : w.support = u :: w.support.tail := by
    rw [← SimpleGraph.Walk.support_tail_of_not_nil w hnil]
    exact (SimpleGraph.Walk.cons_support_tail hnil).symm
  have hteq : w.support.toFinset = w.support.tail.toFinset := by
    ext x
    simp only [List.mem_toFinset]
    constructor
    · intro hx
      rw [hsupp, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact humem
      · exact hx
    · intro hx
      rw [hsupp, List.mem_cons]
      exact Or.inr hx
  have htlen : w.support.tail.length = w.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]
    omega
  have htcard : #(w.support.toFinset) = w.length := by
    rw [hteq, List.toFinset_card_of_nodup hc.support_nodup, htlen]
  have hecard : #(w.edges.toFinset) = w.length := by
    rw [List.toFinset_card_of_nodup hc.edges_nodup, SimpleGraph.Walk.length_edges]
  rw [mem_badSets, htcard]
  refine ⟨hc.three_le_length, hlen, ?_⟩
  calc w.length = #(w.edges.toFinset) := hecard.symm
    _ ≤ #(spannedEdges w.support.toFinset ∩ X) :=
        Finset.card_le_card (edges_toFinset_subset w)

end BadSets

section Alteration

variable {n : ℕ}

/-- One vertex deleted from each bad set — the alteration step. -/
def cutVertices (ℓ : ℕ) (X : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  (badSets ℓ X).biUnion fun t => if h : t.Nonempty then {t.min' h} else ∅

lemma card_cutVertices_le (ℓ : ℕ) (X : Finset (Sym2 (Fin n))) :
    #(cutVertices ℓ X) ≤ #(badSets ℓ X) := by
  classical
  refine le_trans Finset.card_biUnion_le ?_
  calc ∑ t ∈ badSets ℓ X, #(if h : t.Nonempty then {t.min' h} else (∅ : Finset (Fin n)))
      ≤ ∑ _t ∈ badSets ℓ X, 1 := by
        refine Finset.sum_le_sum fun t _ => ?_
        by_cases h : t.Nonempty
        · rw [dif_pos h, Finset.card_singleton]
        · rw [dif_neg h, Finset.card_empty]
          exact Nat.zero_le 1
    _ = #(badSets ℓ X) := by simp

lemma min'_mem_cutVertices {ℓ : ℕ} {X : Finset (Sym2 (Fin n))} {t : Finset (Fin n)}
    (ht : t ∈ badSets ℓ X) (h : t.Nonempty) : t.min' h ∈ cutVertices ℓ X := by
  rw [cutVertices, Finset.mem_biUnion]
  refine ⟨t, ht, ?_⟩
  rw [dif_pos h]
  exact Finset.mem_singleton_self _

/-- **The alteration.** From an edge set with few bad sets and no independent set of size `x`,
an induced subgraph with girth `> ℓ` and chromatic number `> k`.

Deleting one vertex from each bad set leaves more than `n/2` vertices, and no short cycle can
survive: its support would be a bad set, whose least vertex is gone. The surviving graph still
has independence number `< x`, so more than `#s / x > k` colours are needed. -/
theorem exists_girth_chromatic_of_good {ℓ k x : ℕ} {X : Finset (Sym2 (Fin n))}
    (hbad : 2 * #(badSets ℓ X) < n) (hx : 1 ≤ x)
    (hindep : ∀ t : Finset (Fin n), #t = x → ¬ Disjoint (spannedEdges t) X)
    (hkx : 2 * (k * x) ≤ n) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W) (_ : DecidableRel G.Adj),
      (ℓ : ℕ∞) < G.egirth ∧ (k : ℕ∞) < G.chromaticNumber := by
  classical
  refine ⟨↥((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n)), inferInstance,
    (graphOfEdges X).induce ((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n)),
    inferInstance, ?_, ?_⟩
  · -- girth: a surviving short cycle would be a bad set with all its vertices present
    have hstep : ((ℓ + 1 : ℕ) : ℕ∞)
        ≤ ((graphOfEdges X).induce
            ((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n))).egirth := by
      rw [SimpleGraph.le_egirth]
      intro a w' hcyc
      have hlen : ℓ + 1 ≤ w'.length := by
        by_contra hcon
        push_neg at hcon
        have hlen' : w'.length ≤ ℓ := by omega
        -- transport the cycle down to `graphOfEdges X`
        have hinj : Function.Injective
            ((SimpleGraph.Embedding.induce (G := graphOfEdges X)
              ((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n))).toHom :
                ↥((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n)) → Fin n) :=
          Subtype.val_injective
        have hcyc' : (w'.map (SimpleGraph.Embedding.induce (G := graphOfEdges X)
            ((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n))).toHom).IsCycle :=
          hcyc.map hinj
        have hlen'' : (w'.map (SimpleGraph.Embedding.induce (G := graphOfEdges X)
            ((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n))).toHom).length ≤ ℓ := by
          rw [SimpleGraph.Walk.length_map]
          exact hlen'
        have hmem := support_mem_badSets (X := X) _ hcyc' hlen''
        have hne : ((w'.map (SimpleGraph.Embedding.induce (G := graphOfEdges X)
            ((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n))).toHom).support.toFinset).Nonempty := by
          refine Finset.card_pos.mp ?_
          have := (mem_badSets.mp hmem).1
          omega
        have hcut := min'_mem_cutVertices hmem hne
        have hsub : ∀ v ∈ (w'.map (SimpleGraph.Embedding.induce (G := graphOfEdges X)
            ((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n))).toHom).support.toFinset,
            v ∈ (univ \ cutVertices ℓ X : Finset (Fin n)) := by
          intro v hv
          rw [List.mem_toFinset, SimpleGraph.Walk.support_map, List.mem_map] at hv
          obtain ⟨b, -, rfl⟩ := hv
          exact Finset.mem_coe.mp b.2
        have hvs := hsub _ (Finset.min'_mem _ hne)
        exact (Finset.mem_sdiff.mp hvs).2 hcut
      exact_mod_cast hlen
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self ℓ) hstep
  · -- chromatic number: independence number below `x`, and more than `n/2` vertices survive
    refine lt_chromaticNumber_of_mul_indepNum_lt _ ?_
    have hcard : Fintype.card ↥((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n))
        = #(univ \ cutVertices ℓ X : Finset (Fin n)) := Fintype.card_coe _
    rw [hcard]
    have hind : ((graphOfEdges X).induce
        ((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n))).indepNum < x := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨t', ht'⟩ := SimpleGraph.exists_isNIndepSet_indepNum
        (G := (graphOfEdges X).induce
          ((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n)))
      obtain ⟨t'', ht''sub, ht''card⟩ :=
        Finset.exists_subset_card_eq (s := t') (n := x) (by rw [ht'.2]; exact hcon)
      refine hindep (t''.image Subtype.val) ?_ ?_
      · rw [Finset.card_image_of_injective _ Subtype.val_injective]
        exact ht''card
      · rw [Finset.disjoint_right]
        intro e he hspan
        rw [mem_spannedEdges] at hspan
        obtain ⟨a, ha, b, hb, hab, rfl⟩ := hspan
        obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
        have hadj : (graphOfEdges X).Adj (a' : Fin n) (b' : Fin n) := by
          rw [graphOfEdges_adj]
          exact ⟨he, hab⟩
        have hadj' : ((graphOfEdges X).induce
            ((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n))).Adj a' b' := hadj
        have hne' : a' ≠ b' := fun h => hab (by rw [h])
        exact ht'.1 (Finset.mem_coe.mpr (ht''sub ha')) (Finset.mem_coe.mpr (ht''sub hb'))
          hne' hadj'
    have hcut : #(cutVertices ℓ X) ≤ #(badSets ℓ X) := card_cutVertices_le ℓ X
    have hscard : #(univ \ cutVertices ℓ X : Finset (Fin n)) = n - #(cutVertices ℓ X) := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), card_univ, Fintype.card_fin]
    calc k * ((graphOfEdges X).induce
          ((univ \ cutVertices ℓ X : Finset (Fin n)) : Set (Fin n))).indepNum ≤ k * x :=
          Nat.mul_le_mul_left _ (le_of_lt hind)
      _ < #(univ \ cutVertices ℓ X : Finset (Fin n)) := by omega

end Alteration

section Moments

variable {n : ℕ}

/-- The witnesses counted by the first moment: a `j`-set `t` of vertices together with `j` of
the pairs inside it. A bad set of size `j` supplies at least one, with all `j` pairs present. -/
def badPairs (n j : ℕ) : Finset (Finset (Fin n) × Finset (Sym2 (Fin n))) :=
  ((univ : Finset (Fin n)).powersetCard j).biUnion fun t =>
    ((spannedEdges t).powersetCard j).image fun F => (t, F)

lemma mem_badPairs {n j : ℕ} {q : Finset (Fin n) × Finset (Sym2 (Fin n))} :
    q ∈ badPairs n j ↔ (#q.1 = j ∧ q.2 ⊆ spannedEdges q.1 ∧ #q.2 = j) := by
  classical
  rw [badPairs, Finset.mem_biUnion]
  constructor
  · rintro ⟨t, ht, hq⟩
    rw [Finset.mem_powersetCard] at ht
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hq
    rw [Finset.mem_powersetCard] at hF
    exact ⟨ht.2, hF.1, hF.2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨q.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h1⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨q.2, Finset.mem_powersetCard.mpr ⟨h2, h3⟩, rfl⟩

lemma card_badPairs (n j : ℕ) : #(badPairs n j) = n.choose j * ((j.choose 2).choose j) := by
  classical
  rw [badPairs, Finset.card_biUnion]
  · have hterm : ∀ t ∈ (univ : Finset (Fin n)).powersetCard j,
        #(((spannedEdges t).powersetCard j).image fun F => (t, F)) = (j.choose 2).choose j := by
      intro t ht
      rw [Finset.mem_powersetCard] at ht
      rw [Finset.card_image_of_injective _ (fun F F' h => (Prod.mk.injEq .. ▸ h).2),
        Finset.card_powersetCard, card_spannedEdges, ht.2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, card_univ,
      Fintype.card_fin, smul_eq_mul]
  · intro t ht t' ht' hne
    refine Finset.disjoint_left.mpr fun q hq hq' => ?_
    obtain ⟨F, -, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨F', -, hFF'⟩ := Finset.mem_image.mp hq'
    exact hne (Prod.mk.injEq .. ▸ hFF').1.symm

/-- Every bad set of size `j` yields a member of `badPairs n j` all of whose edges are
present. -/
lemma card_badSets_le (ℓ : ℕ) (X : Finset (Sym2 (Fin n))) :
    #(badSets ℓ X) ≤ ∑ j ∈ Finset.Icc 3 ℓ, #((badPairs n j).filter fun q => q.2 ⊆ X) := by
  classical
  have hfib : #(badSets ℓ X)
      = ∑ j ∈ Finset.Icc 3 ℓ, #((badSets ℓ X).filter fun t => #t = j) := by
    refine Finset.card_eq_sum_card_fiberwise fun t ht => ?_
    simp only [Finset.mem_coe] at ht ⊢
    rw [mem_badSets] at ht
    rw [Finset.mem_Icc]
    exact ⟨ht.1, ht.2.1⟩
  rw [hfib]
  refine Finset.sum_le_sum fun j _ => ?_
  -- choose `j` present edges inside each bad set of size `j`
  have hex : ∀ t : Finset (Fin n), ∃ F : Finset (Sym2 (Fin n)),
      t ∈ (badSets ℓ X).filter (fun t => #t = j) →
        (F ⊆ spannedEdges t ∧ #F = j ∧ F ⊆ X) := by
    intro t
    by_cases ht : t ∈ (badSets ℓ X).filter (fun t => #t = j)
    · rw [mem_filter, mem_badSets] at ht
      obtain ⟨F, hFsub, hFcard⟩ :=
        Finset.exists_subset_card_eq (s := spannedEdges t ∩ X) (n := j) (by
          rw [← ht.2]
          exact ht.1.2.2)
      exact ⟨F, fun _ => ⟨hFsub.trans Finset.inter_subset_left, hFcard,
        hFsub.trans Finset.inter_subset_right⟩⟩
    · exact ⟨∅, fun h => absurd h ht⟩
  choose F hF using hex
  refine Finset.card_le_card_of_injOn (fun t => (t, F t)) ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe] at ht
    obtain ⟨h1, h2, h3⟩ := hF t ht
    rw [mem_filter] at ht
    simp only [Finset.mem_coe, mem_filter]
    exact ⟨mem_badPairs.mpr ⟨ht.2, h1, h2⟩, h3⟩
  · intro t₁ h₁ t₂ h₂ heq
    exact (Prod.mk.injEq .. ▸ heq).1

/-- **The first moment of the bad-set count**: at most
`∑_{j=3}^{ℓ} C(n,j) · C(C(j,2), j) · p^j` bad sets on average.

`PMC.card_badSets_le` replaces the count by the number of *witnesses* — a `j`-set of vertices
together with `j` present pairs inside it — and each witness is a fixed set of `j` edges, so
`PMC.sum_bweight_mul_card_filter` (the first moment method) applies verbatim. -/
theorem sum_bweight_card_badSets_le (ℓ : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ X ∈ (univ : Finset (Sym2 (Fin n))).powerset, bweight p X * (#(badSets ℓ X) : ℝ)
      ≤ ∑ j ∈ Finset.Icc 3 ℓ,
          (n.choose j * ((j.choose 2).choose j) : ℝ) * p ^ j := by
  classical
  calc ∑ X ∈ (univ : Finset (Sym2 (Fin n))).powerset, bweight p X * (#(badSets ℓ X) : ℝ)
      ≤ ∑ X ∈ (univ : Finset (Sym2 (Fin n))).powerset, bweight p X *
          (∑ j ∈ Finset.Icc 3 ℓ, (#((badPairs n j).filter fun q => q.2 ⊆ X) : ℝ)) := by
        refine Finset.sum_le_sum fun X _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (bweight_nonneg hp0 hp1 X)
        have h := card_badSets_le ℓ X
        have : ((#(badSets ℓ X) : ℕ) : ℝ)
            ≤ ((∑ j ∈ Finset.Icc 3 ℓ, #((badPairs n j).filter fun q => q.2 ⊆ X) : ℕ) : ℝ) := by
          exact_mod_cast h
        rwa [Nat.cast_sum] at this
    _ = ∑ j ∈ Finset.Icc 3 ℓ, ∑ X ∈ (univ : Finset (Sym2 (Fin n))).powerset,
          bweight p X * (#((badPairs n j).filter fun q => q.2 ⊆ X) : ℝ) := by
        rw [Finset.sum_congr rfl fun X _ => Finset.mul_sum _ _ _, Finset.sum_comm]
    _ = ∑ j ∈ Finset.Icc 3 ℓ, (#(badPairs n j) : ℝ) * p ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact sum_bweight_mul_card_filter p (badPairs n j) (fun q => q.2) j
          fun q hq => (mem_badPairs.mp hq).2.2
    _ = ∑ j ∈ Finset.Icc 3 ℓ, (n.choose j * ((j.choose 2).choose j) : ℝ) * p ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [card_badPairs]
        push_cast
        ring

/-- **The independence tail.** The weight of the edge sets admitting an independent `x`-set is
at most `C(n,x)(1-p)^{C(x,2)}`: a union bound over the `C(n,x)` candidate sets, each of which
needs its `C(x,2)` pairs all absent (`PMC.sum_bweight_disjoint`). -/
theorem sum_bweight_indep_le (x : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ X ∈ ((univ : Finset (Sym2 (Fin n))).powerset).filter
        (fun X => ∃ t ∈ (univ : Finset (Fin n)).powersetCard x, Disjoint (spannedEdges t) X),
      bweight p X ≤ (n.choose x : ℝ) * (1 - p) ^ (x.choose 2) := by
  classical
  set T : Finset (Finset (Fin n)) := (univ : Finset (Fin n)).powersetCard x with hT
  set Z : Finset (Fin n) → Finset (Finset (Sym2 (Fin n))) := fun t =>
    ((univ : Finset (Sym2 (Fin n))).powerset).filter fun X => Disjoint X (spannedEdges t) with hZ
  have hsub : ((univ : Finset (Sym2 (Fin n))).powerset).filter
      (fun X => ∃ t ∈ T, Disjoint (spannedEdges t) X) ⊆ T.biUnion Z := by
    intro X hX
    rw [mem_filter] at hX
    obtain ⟨t, ht, hdisj⟩ := hX.2
    exact Finset.mem_biUnion.mpr ⟨t, ht, mem_filter.mpr ⟨hX.1, hdisj.symm⟩⟩
  have hnn : ∀ X : Finset (Sym2 (Fin n)), 0 ≤ bweight p X := fun X => bweight_nonneg hp0 hp1 X
  calc ∑ X ∈ ((univ : Finset (Sym2 (Fin n))).powerset).filter
        (fun X => ∃ t ∈ T, Disjoint (spannedEdges t) X), bweight p X
      ≤ ∑ X ∈ T.biUnion Z, bweight p X :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun X _ _ => hnn X
    _ ≤ ∑ t ∈ T, ∑ X ∈ Z t, bweight p X := wprob_biUnion_le hnn T Z
    _ = ∑ _t ∈ T, (1 - p) ^ (x.choose 2) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [hT, Finset.mem_powersetCard] at ht
        rw [hZ]
        have := sum_bweight_disjoint (α := Sym2 (Fin n)) p (spannedEdges t)
        rw [this, card_spannedEdges, ht.2]
    _ = (n.choose x : ℝ) * (1 - p) ^ (x.choose 2) := by
        rw [Finset.sum_const, hT, Finset.card_powersetCard, card_univ, Fintype.card_fin,
          nsmul_eq_mul]

/-- **The two bad events together have weight below `1`**, so some edge set avoids both. -/
theorem exists_good_edgeSet {ℓ x : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n)
    (h1 : 4 * (∑ j ∈ Finset.Icc 3 ℓ,
      (n.choose j * ((j.choose 2).choose j) : ℝ) * p ^ j) < n)
    (h2 : (n.choose x : ℝ) * (1 - p) ^ (x.choose 2) < 1 / 2) :
    ∃ X : Finset (Sym2 (Fin n)), 2 * #(badSets ℓ X) < n ∧
      ∀ t : Finset (Fin n), #t = x → ¬ Disjoint (spannedEdges t) X := by
  classical
  have hnn : ∀ X : Finset (Sym2 (Fin n)), 0 ≤ bweight p X := fun X => bweight_nonneg hp0 hp1 X
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set A : Finset (Finset (Sym2 (Fin n))) :=
    (univ : Finset (Finset (Sym2 (Fin n)))).filter
      fun X => (n : ℝ) / 2 ≤ (#(badSets ℓ X) : ℝ) with hA
  set B : Finset (Finset (Sym2 (Fin n))) :=
    ((univ : Finset (Sym2 (Fin n))).powerset).filter
      (fun X => ∃ t ∈ (univ : Finset (Fin n)).powersetCard x, Disjoint (spannedEdges t) X)
    with hB
  -- Markov on the bad-set count
  have hmark := wmarkov (bweight (α := Sym2 (Fin n)) p) (fun X => (#(badSets ℓ X) : ℝ)) hnn
    (fun X : Finset (Sym2 (Fin n)) => by positivity) (a := (n : ℝ) / 2) (by positivity)
  have hmean : wmean (bweight (α := Sym2 (Fin n)) p) (fun X => (#(badSets ℓ X) : ℝ))
      ≤ ∑ j ∈ Finset.Icc 3 ℓ, (n.choose j * ((j.choose 2).choose j) : ℝ) * p ^ j := by
    rw [wmean, ← Finset.powerset_univ]
    exact sum_bweight_card_badSets_le ℓ hp0 hp1
  have hAweight : ∑ X ∈ A, bweight p X < 1 / 2 := by
    have hpos : (0 : ℝ) < (n : ℝ) / 2 := by positivity
    have hfilter : ∑ X ∈ A, bweight p X
        = ∑ ω ∈ (univ : Finset (Finset (Sym2 (Fin n)))).filter (fun ω => (n : ℝ) / 2 ≤ (#(badSets ℓ ω) : ℝ)), bweight p ω := by
      rw [hA]
    rw [hfilter]
    refine lt_of_mul_lt_mul_right ?_ (le_of_lt hpos)
    have h3 : (∑ ω ∈ (univ : Finset (Finset (Sym2 (Fin n)))).filter (fun ω => (n : ℝ) / 2 ≤ (#(badSets ℓ ω) : ℝ)), bweight p ω)
        * ((n : ℝ) / 2) < (n : ℝ) / 4 := by linarith
    calc (∑ ω ∈ (univ : Finset (Finset (Sym2 (Fin n)))).filter (fun ω => (n : ℝ) / 2 ≤ (#(badSets ℓ ω) : ℝ)), bweight p ω)
        * ((n : ℝ) / 2) < (n : ℝ) / 4 := h3
      _ = 1 / 2 * ((n : ℝ) / 2) := by ring
  have hBweight : ∑ X ∈ B, bweight p X < 1 / 2 :=
    lt_of_le_of_lt (sum_bweight_indep_le x hp0 hp1) h2
  -- so the union misses something
  have htot : ∑ X ∈ (univ : Finset (Finset (Sym2 (Fin n)))), bweight p X = 1 := by
    rw [← Finset.powerset_univ]
    exact sum_bweight p
  have hne : ((univ : Finset (Finset (Sym2 (Fin n)))) \ (A ∪ B)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty ((univ : Finset (Finset (Sym2 (Fin n)))) \ (A ∪ B))
      with hemp | h
    · exfalso
      have hcover : (univ : Finset (Finset (Sym2 (Fin n)))) ⊆ A ∪ B := by
        intro X _
        by_contra hcon
        exact absurd (Finset.mem_sdiff.mpr ⟨mem_univ X, hcon⟩)
          (by rw [hemp]; exact Finset.notMem_empty X)
      have h1' : (1 : ℝ) ≤ ∑ X ∈ A ∪ B, bweight p X := by
        rw [← htot]
        exact Finset.sum_le_sum_of_subset_of_nonneg hcover fun X _ _ => hnn X
      have h2' : ∑ X ∈ A ∪ B, bweight p X ≤ (∑ X ∈ A, bweight p X) + ∑ X ∈ B, bweight p X := by
        have := wprob_union_le hnn A B
        rw [wprob, wprob, wprob] at this
        exact this
      linarith
    · exact h
  obtain ⟨X, hX⟩ := hne
  rw [Finset.mem_sdiff, Finset.mem_union] at hX
  refine ⟨X, ?_, ?_⟩
  · -- not in `A`
    have hnotA : X ∉ A := fun h => hX.2 (Or.inl h)
    rw [hA, mem_filter] at hnotA
    have : ¬ ((n : ℝ) / 2 ≤ (#(badSets ℓ X) : ℝ)) := fun h => hnotA ⟨mem_univ X, h⟩
    push_neg at this
    have hlt : (2 * #(badSets ℓ X) : ℝ) < n := by linarith
    exact_mod_cast hlt
  · -- not in `B`
    intro t htcard hdisj
    refine hX.2 (Or.inr ?_)
    rw [hB, mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      ⟨t, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, htcard⟩, hdisj⟩⟩

end Moments

section Main

/-- **Theorem 3.4.1 (Erdős 1959).** For every `k` and `ℓ` there is a finite graph with girth
greater than `ℓ` and chromatic number greater than `k`.

The parameters are explicit, which is what makes the proof elementary. With `L = ℓ+1`,
`M = 4L-2` and `r` any integer exceeding both `6k` and `4L·2^{L²}`, take

    n = r^{M+2},   p = r^{-M},   x = 3 r^{M+1}.

Then `nᵢpʲ = r^{2j} ≤ r^{2L}` for every cycle length `j ≤ L`, so the expected number of bad
sets is at most `L 2^{L²} r^{2L} < n/4`; and `p·C(x,2) ≥ p x²/4 = (9/4) n`, so the chance of an
independent set of size `x` is at most `2ⁿ e^{-(9/4)n} < 1/2` — for *every* `r`, since
`9/4 > log 2`. The notes take `p = (log n)²/n` and argue asymptotically; choosing `n` as a
power of `r` instead turns every estimate into an exponent comparison, with no `o(1)` and no
logarithms beyond `log 2 < 0.694`.

Stated with `SimpleGraph.egirth` (the `ℕ∞`-valued girth), not `girth`: the latter is `0` for an
acyclic graph, so "girth `> ℓ`" in that form would additionally demand that the graph *have* a
cycle, which is not what the notes ask for. `ℓ < egirth` says exactly "no cycle of length
`≤ ℓ`". -/
theorem exists_girth_chromatic (k ℓ : ℕ) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W) (_ : DecidableRel G.Adj),
      (ℓ : ℕ∞) < G.egirth ∧ (k : ℕ∞) < G.chromaticNumber := by
  classical
  obtain ⟨L, hL⟩ : ∃ L, L = ℓ + 1 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, 4 * L = M + 2 := ⟨4 * L - 2, by omega⟩
  obtain ⟨r, hr1, hr2, hr3⟩ : ∃ r : ℕ, 6 * k ≤ r ∧ 4 * L * 2 ^ (L * L) < r ∧ 3 ≤ r :=
    ⟨max (6 * k) (max (4 * L * 2 ^ (L * L) + 1) 3), le_max_left _ _,
      lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) (le_max_right _ _)),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨n, hn⟩ : ∃ n, n = r ^ (M + 2) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = 3 * r ^ (M + 1) := ⟨_, rfl⟩
  set p : ℝ := 1 / (r : ℝ) ^ M with hp
  have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hrpow : ∀ i : ℕ, (1 : ℝ) ≤ (r : ℝ) ^ i := fun i => one_le_pow₀ (by linarith)
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one (by positivity)]
    exact hrpow M
  have hnR : (n : ℝ) = (r : ℝ) ^ (M + 2) := by rw [hn]; push_cast; ring
  have hnpos : 0 < n := by
    rw [hn]
    exact pow_pos (by omega) _
  have hxR : (x : ℝ) = 3 * (r : ℝ) ^ (M + 1) := by rw [hx]; push_cast; ring
  have hx2 : 2 ≤ x := by
    rw [hx]
    have : 1 ≤ r ^ (M + 1) := Nat.one_le_pow _ _ (by omega)
    omega
  -- the bad-set bound
  have h1 : 4 * (∑ j ∈ Finset.Icc 3 L,
      (n.choose j * ((j.choose 2).choose j) : ℝ) * p ^ j) < n := by
    have hterm : ∀ j ∈ Finset.Icc 3 L,
        (n.choose j * ((j.choose 2).choose j) : ℝ) * p ^ j
          ≤ (2 : ℝ) ^ (L * L) * (r : ℝ) ^ (2 * L) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hc1 : (n.choose j : ℝ) ≤ (n : ℝ) ^ j := by
        exact_mod_cast Nat.choose_le_pow n j
      have hjj : j.choose 2 ≤ L * L := by
        refine le_trans (Nat.choose_le_pow j 2) ?_
        calc j ^ 2 = j * j := by ring
          _ ≤ L * L := Nat.mul_le_mul hj.2 hj.2
      have hc2 : (((j.choose 2).choose j : ℕ) : ℝ) ≤ (2 : ℝ) ^ (L * L) := by
        have h := Nat.choose_le_two_pow (j.choose 2) j
        have h2 : (j.choose 2).choose j ≤ 2 ^ (L * L) :=
          le_trans h (Nat.pow_le_pow_right (by norm_num) hjj)
        exact_mod_cast h2
      have hnp : (n : ℝ) ^ j * p ^ j = (r : ℝ) ^ (2 * j) := by
        rw [hnR, hp, div_pow, one_pow, ← pow_mul, ← pow_mul, mul_one_div,
          div_eq_iff (by positivity), ← pow_add]
        congr 1
        ring
      have hrj : (r : ℝ) ^ (2 * j) ≤ (r : ℝ) ^ (2 * L) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      calc (n.choose j * ((j.choose 2).choose j) : ℝ) * p ^ j
          ≤ ((n : ℝ) ^ j * (2 : ℝ) ^ (L * L)) * p ^ j := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul hc1 hc2 (by positivity) (by positivity))
              (by positivity)
        _ = (2 : ℝ) ^ (L * L) * ((n : ℝ) ^ j * p ^ j) := by ring
        _ = (2 : ℝ) ^ (L * L) * (r : ℝ) ^ (2 * j) := by rw [hnp]
        _ ≤ (2 : ℝ) ^ (L * L) * (r : ℝ) ^ (2 * L) := by
            exact mul_le_mul_of_nonneg_left hrj (by positivity)
    have hsum : (∑ j ∈ Finset.Icc 3 L,
        (n.choose j * ((j.choose 2).choose j) : ℝ) * p ^ j)
        ≤ (L : ℝ) * ((2 : ℝ) ^ (L * L) * (r : ℝ) ^ (2 * L)) := by
      refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
      rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have : #(Finset.Icc 3 L) ≤ L := by
        rw [Nat.card_Icc]
        omega
      exact_mod_cast this
    -- `4L·2^{L²} ≤ r` and `r · r^{2L} ≤ r^{M+2}`
    have hkey : 4 * ((L : ℝ) * ((2 : ℝ) ^ (L * L) * (r : ℝ) ^ (2 * L))) < (r : ℝ) ^ (M + 2) := by
      have hcoef : (4 : ℝ) * (L : ℝ) * (2 : ℝ) ^ (L * L) < (r : ℝ) := by
        have h : ((4 * L * 2 ^ (L * L) : ℕ) : ℝ) < (r : ℝ) := by exact_mod_cast hr2
        push_cast at h
        linarith
      have hpow : (r : ℝ) * (r : ℝ) ^ (2 * L) ≤ (r : ℝ) ^ (M + 2) := by
        rw [← pow_succ']
        exact pow_le_pow_right₀ (by linarith) (by omega)
      calc 4 * ((L : ℝ) * ((2 : ℝ) ^ (L * L) * (r : ℝ) ^ (2 * L)))
          = ((4 : ℝ) * (L : ℝ) * (2 : ℝ) ^ (L * L)) * (r : ℝ) ^ (2 * L) := by ring
        _ < (r : ℝ) * (r : ℝ) ^ (2 * L) :=
            mul_lt_mul_of_pos_right hcoef (by positivity)
        _ ≤ (r : ℝ) ^ (M + 2) := hpow
    rw [hnR]
    have hstrict : 4 * (∑ j ∈ Finset.Icc 3 L,
        (n.choose j * ((j.choose 2).choose j) : ℝ) * p ^ j)
        ≤ 4 * ((L : ℝ) * ((2 : ℝ) ^ (L * L) * (r : ℝ) ^ (2 * L))) := by
      linarith
    linarith
  -- the chromatic-number budget
  have hkx : 2 * (k * x) ≤ n := by
    rw [hn, hx]
    calc 2 * (k * (3 * r ^ (M + 1))) = (6 * k) * r ^ (M + 1) := by ring
      _ ≤ r * r ^ (M + 1) := Nat.mul_le_mul_right _ hr1
      _ = r ^ (M + 2) := by rw [← pow_succ']
  -- the independence bound
  have hx9 : 9 ≤ x := by
    rw [hx]
    have h : 3 ≤ r ^ (M + 1) := le_trans hr3 (Nat.le_self_pow (by omega) r)
    omega
  have hchooseN : x ^ 2 ≤ 4 * x.choose 2 := by
    obtain ⟨y, hy⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    subst hy
    rw [Nat.choose_two_right]
    simp only [Nat.add_sub_cancel]
    have hdiv := Nat.div_add_mod ((y + 1) * y) 2
    have hmod : ((y + 1) * y) % 2 < 2 := Nat.mod_lt _ (by omega)
    nlinarith [hdiv, hmod, hx9]
  have hpx : p * (x : ℝ) ^ 2 = 9 * (n : ℝ) := by
    have hexp : (r : ℝ) ^ ((M + 1) * 2) = (r : ℝ) ^ (M + 2) * (r : ℝ) ^ M := by
      rw [← pow_add]
      congr 1
      ring
    rw [hxR, hp, hnR, mul_pow, ← pow_mul, hexp]
    field_simp
    ring
  have hbig : (9 / 4 : ℝ) * n ≤ p * (x.choose 2 : ℝ) := by
    have h1' : (x : ℝ) ^ 2 ≤ 4 * (x.choose 2 : ℝ) := by exact_mod_cast hchooseN
    nlinarith [h1', hpx, hp0]
  have h2 : (n.choose x : ℝ) * (1 - p) ^ (x.choose 2) < 1 / 2 := by
    have hxc : (n.choose x : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast Nat.choose_le_two_pow n x
    have h1p : (0 : ℝ) ≤ 1 - p := by linarith
    have hexp1 : (1 - p) ^ (x.choose 2) ≤ Real.exp (-(p * (x.choose 2 : ℝ))) := by
      have hstep : (1 - p) ≤ Real.exp (-p) := by
        have := Real.add_one_le_exp (-p)
        linarith
      calc (1 - p) ^ (x.choose 2) ≤ (Real.exp (-p)) ^ (x.choose 2) :=
            pow_le_pow_left₀ h1p hstep _
        _ = Real.exp (-(p * (x.choose 2 : ℝ))) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
    have hmono : Real.exp (-(p * (x.choose 2 : ℝ))) ≤ Real.exp (-((9 / 4 : ℝ) * n)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2n : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
      rw [← Real.rpow_natCast (2 : ℝ) n, Real.rpow_def_of_pos (by norm_num)]
      ring_nf
    have hhalf : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    have hfinal : (2 : ℝ) ^ n * Real.exp (-((9 / 4 : ℝ) * n)) < 1 / 2 := by
      rw [h2n, ← Real.exp_add, hhalf, Real.exp_lt_exp]
      have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      nlinarith [hlog, hn1]
    calc (n.choose x : ℝ) * (1 - p) ^ (x.choose 2)
        ≤ (2 : ℝ) ^ n * Real.exp (-(p * (x.choose 2 : ℝ))) :=
          mul_le_mul hxc hexp1 (by positivity) (by positivity)
      _ ≤ (2 : ℝ) ^ n * Real.exp (-((9 / 4 : ℝ) * n)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ < 1 / 2 := hfinal
  -- assemble
  obtain ⟨X, hbad, hindep⟩ := exists_good_edgeSet hp0 hp1 hnpos h1 h2
  obtain ⟨W, hW, G, hGdec, hgirth, hchrom⟩ :=
    exists_girth_chromatic_of_good hbad (by omega : 1 ≤ x) hindep hkx
  refine ⟨W, hW, G, hGdec, lt_of_le_of_lt ?_ hgirth, hchrom⟩
  exact_mod_cast (by omega : ℓ ≤ L)

end Main

end PMC



