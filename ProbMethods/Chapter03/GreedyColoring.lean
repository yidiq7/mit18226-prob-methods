import ProbMethods.Chapter01.PropertyB
import ProbMethods.Product
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# §3.5 — Random greedy colouring (Theorem 3.5.1)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 3.5.1 (Radhakrishnan–Srinivasan 2000,
in the form due to Cherkashin–Kozik 2015): there is `c > 0` such that every `k`-uniform
hypergraph with at most `c √(k / log k) 2^k` edges is 2-colourable.

This file builds the deterministic half: Pluhár's observation that a *conflict-free* ordering
of the vertices already gives a 2-colouring.

**The colouring is not the greedy one.** The notes colour greedily from left to right — blue
unless that would complete a blue edge — and then observe that a red edge forces two edges
`e, f` with `last(e) = first(f)`. Formalizing the greedy colouring means a recursion whose
value at `v` depends on all earlier vertices. It is not needed: colour `v` **red exactly when
`v` is the last vertex of some edge**. That is a non-recursive definition, and the same two
lines prove it works:

* no edge is all blue — an edge's own last vertex is red;
* no edge is all red — its *first* vertex `v` is red, so `v` ends some edge `f`, and
  `last(f) = v = first(e)` is a conflict.

`PMC.exists_bichromatic_of_no_conflict` is that statement. Ties in the vertex values are broken
by the vertex index (`PMC.vkey`), which is what makes the induced order total, so that every
nonempty edge has a first and a last vertex.
-/

open Finset

namespace PMC

section Greedy

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {N : ℕ}

/-- The position key of a vertex: its value, with the vertex itself breaking ties. -/
def vkey (val : V → Fin N) (v : V) : Fin N ×ₗ V := toLex (val v, v)

lemma vkey_injective (val : V → Fin N) : Function.Injective (vkey val) := by
  intro u v h
  have := congrArg (fun x => (ofLex x).2) h
  simpa [vkey] using this

lemma val_le_of_vkey_lt {val : V → Fin N} {u v : V} (h : vkey val u < vkey val v) :
    val u ≤ val v := by
  rw [vkey, vkey, Prod.Lex.toLex_lt_toLex'] at h
  exact h.1

/-- `v` is the last vertex of `e`. -/
def IsLast (val : V → Fin N) (e : Finset V) (v : V) : Prop :=
  v ∈ e ∧ ∀ u ∈ e, u ≠ v → vkey val u < vkey val v

/-- `v` is the first vertex of `e`. -/
def IsFirst (val : V → Fin N) (e : Finset V) (v : V) : Prop :=
  v ∈ e ∧ ∀ u ∈ e, u ≠ v → vkey val v < vkey val u

instance (val : V → Fin N) (e : Finset V) : DecidablePred (IsLast val e) := fun _ => by
  unfold IsLast
  infer_instance

instance (val : V → Fin N) (e : Finset V) : DecidablePred (IsFirst val e) := fun _ => by
  unfold IsFirst
  infer_instance

lemma exists_isLast (val : V → Fin N) {e : Finset V} (he : e.Nonempty) :
    ∃ v, IsLast val e v := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image e (vkey val) he
  refine ⟨v, hv, fun u hu hne => ?_⟩
  exact lt_of_le_of_ne (hmax u hu) fun h => hne (vkey_injective val h)

lemma exists_isFirst (val : V → Fin N) {e : Finset V} (he : e.Nonempty) :
    ∃ v, IsFirst val e v := by
  obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image e (vkey val) he
  refine ⟨v, hv, fun u hu hne => ?_⟩
  exact lt_of_le_of_ne (hmin u hu) fun h => hne (vkey_injective val h).symm

/-- The last and the first vertex of an edge with at least two vertices are distinct. -/
lemma isLast_ne_isFirst {val : V → Fin N} {e : Finset V} {u v : V} (hu : IsFirst val e u)
    (hv : IsLast val e v) (hcard : 2 ≤ #e) : u ≠ v := by
  intro h
  subst h
  obtain ⟨w, hw, hwu⟩ : ∃ w ∈ e, w ≠ u := by
    by_contra hcon
    push_neg at hcon
    have : e ⊆ {u} := fun w hw => Finset.mem_singleton.mpr (hcon w hw)
    have := Finset.card_le_card this
    simp at this
    omega
  exact absurd (hu.2 w hw hwu) (not_lt.mpr (le_of_lt (hv.2 w hw hwu)))

/-- **Pluhár's observation.** If no edge of `H` ends where another begins, then colouring a
vertex red exactly when it is the last vertex of some edge leaves no edge monochromatic. -/
theorem exists_bichromatic_of_no_conflict (H : Finset (Finset V)) (val : V → Fin N)
    (hcard : ∀ e ∈ H, 2 ≤ #e)
    (hconf : ∀ e ∈ H, ∀ f ∈ H, ∀ v, IsLast val e v → IsFirst val f v → False) :
    TwoColorable H := by
  classical
  refine ⟨fun v => decide (¬ ∃ e ∈ H, IsLast val e v), fun e he => ?_⟩
  have hne : e.Nonempty := Finset.card_pos.mp (by have := hcard e he; omega)
  obtain ⟨v, hv⟩ := exists_isLast val hne
  obtain ⟨u, hu⟩ := exists_isFirst val hne
  refine ⟨u, hu.1, v, hv.1, ?_⟩
  have hublue : ¬ ∃ f ∈ H, IsLast val f u := by
    rintro ⟨f, hf, hfu⟩
    exact hconf f hf e he u hfu hu
  have hu' : decide (¬ ∃ f ∈ H, IsLast val f u) = true := decide_eq_true hublue
  have hv' : decide (¬ ∃ f ∈ H, IsLast val f v) = false :=
    decide_eq_false (not_not_intro ⟨e, he, hv⟩)
  show decide (¬ ∃ f ∈ H, IsLast val f u) ≠ decide (¬ ∃ f ∈ H, IsLast val f v)
  rw [hu', hv']
  simp

end Greedy

section Probability

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {N : ℕ} [NeZero N]

/-- Every vertex of `e` gets a value below `lo` — "the edge lies in `L`". -/
def lowEvent (e : Finset V) (lo : Fin N) : Finset (V → Fin N) :=
  (univ : Finset (V → Fin N)).filter fun val => ∀ u ∈ e, val u < lo

/-- Every vertex of `e` gets a value at least `hi` — "the edge lies in `R`". -/
def highEvent (e : Finset V) (hi : Fin N) : Finset (V → Fin N) :=
  (univ : Finset (V → Fin N)).filter fun val => ∀ u ∈ e, hi ≤ val u

lemma wprob_lowEvent (e : Finset V) (lo : Fin N) :
    wprob (unifProd V (Fin N)) (lowEvent e lo) = (((lo : ℕ) : ℝ) / N) ^ #e := by
  have hcard : #((univ : Finset (Fin N)).filter fun b => b < lo) = (lo : ℕ) := by
    have h : (univ : Finset (Fin N)).filter (fun b => b < lo) = Finset.Iio lo := by
      ext b
      simp
    rw [h, Fin.card_Iio]
  rw [lowEvent, wprob_unifProd_forall e (fun _ b => b < lo),
    Finset.prod_congr rfl (fun u _ => by rw [hcard]), Finset.prod_const, Fintype.card_fin]

lemma wprob_highEvent (e : Finset V) (hi : Fin N) :
    wprob (unifProd V (Fin N)) (highEvent e hi) = (((N - hi : ℕ) : ℝ) / N) ^ #e := by
  have hcard : #((univ : Finset (Fin N)).filter fun b => hi ≤ b) = N - (hi : ℕ) := by
    have h : (univ : Finset (Fin N)).filter (fun b => hi ≤ b) = Finset.Ici hi := by
      ext b
      simp
    rw [h, Fin.card_Ici]
  rw [highEvent, wprob_unifProd_forall e (fun _ b => hi ≤ b),
    Finset.prod_congr rfl (fun u _ => by rw [hcard]), Finset.prod_const, Fintype.card_fin]

/-- The values that put `v` at level `j`, the rest of `e` at or below `j`, and the rest of `f`
at or above `j`. A conflict whose shared vertex sits at level `j` is one of these. -/
def confEvent (e f : Finset V) (v : V) (j : Fin N) : Finset (V → Fin N) :=
  (univ : Finset (V → Fin N)).filter fun val =>
    ∀ u ∈ e ∪ f, (if u = v then val u = j else if u ∈ e then val u ≤ j else j ≤ val u)

/-- **The conflict probability at a level.** For two edges meeting in exactly one vertex, the
three coordinate blocks `{v}`, `e \ {v}` and `f \ e` are disjoint, so the probability is a
product: `(1/N) · ((j+1)/N)^{#e-1} · ((N-j)/N)^{#f-1}`. -/
lemma wprob_confEvent (e f : Finset V) (v : V) (hv : e ∩ f = {v}) (j : Fin N) :
    wprob (unifProd V (Fin N)) (confEvent e f v j)
      = 1 / (N : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / N) ^ (#e - 1)
        * (((N - (j : ℕ) : ℕ) : ℝ) / N) ^ (#f - 1) := by
  classical
  have hvmem : v ∈ e ∩ f := by rw [hv]; exact Finset.mem_singleton_self v
  rw [Finset.mem_inter] at hvmem
  obtain ⟨hve, hvf⟩ := hvmem
  -- the three counts
  have hc1 : #((univ : Finset (Fin N)).filter fun b => b = j) = 1 := by
    rw [Finset.filter_eq' univ j]
    simp
  have hc2 : #((univ : Finset (Fin N)).filter fun b => b ≤ j) = (j : ℕ) + 1 := by
    have h : (univ : Finset (Fin N)).filter (fun b => b ≤ j) = Finset.Iic j := by
      ext b
      simp
    rw [h, Fin.card_Iic]
  have hc3 : #((univ : Finset (Fin N)).filter fun b => j ≤ b) = N - (j : ℕ) := by
    have h : (univ : Finset (Fin N)).filter (fun b => j ≤ b) = Finset.Ici j := by
      ext b
      simp
    rw [h, Fin.card_Ici]
  rw [confEvent, wprob_unifProd_forall (e ∪ f)
    (fun u b => (if u = v then b = j else if u ∈ e then b ≤ j else j ≤ b))]
  -- split `e ∪ f` into `{v}`, `e \ {v}` and `f \ e`
  have hunion : e ∪ f = e ∪ f \ e := (Finset.union_sdiff_self_eq_union).symm
  have hdisj : Disjoint e (f \ e) :=
    Finset.disjoint_left.mpr fun a ha ha' => (Finset.mem_sdiff.mp ha').2 ha
  rw [hunion, Finset.prod_union hdisj]
  -- the block `f \ e`
  have hfe : ∀ u ∈ f \ e, (#((univ : Finset (Fin N)).filter
      fun b => (if u = v then b = j else if u ∈ e then b ≤ j else j ≤ b)) : ℝ)
      / Fintype.card (Fin N) = (((N - (j : ℕ) : ℕ) : ℝ) / N) := by
    intro u hu
    rw [Finset.mem_sdiff] at hu
    have hne : u ≠ v := fun h => hu.2 (h ▸ hve)
    simp only [hne, if_false, hu.2, Fintype.card_fin]
    rw [hc3]
  rw [Finset.prod_congr rfl hfe, Finset.prod_const]
  have hcardfe : #(f \ e) = #f - 1 := by
    have h := Finset.card_sdiff_add_card_inter f e
    rw [Finset.inter_comm, hv] at h
    simp at h
    omega
  rw [hcardfe]
  -- the block `e`, split off `v`
  rw [← Finset.mul_prod_erase _ _ hve]
  have hev : (#((univ : Finset (Fin N)).filter
      fun b => (if v = v then b = j else if v ∈ e then b ≤ j else j ≤ b)) : ℝ)
      / Fintype.card (Fin N) = 1 / (N : ℝ) := by
    simp only [Fintype.card_fin, eq_self_iff_true, if_true]
    rw [hc1]
    norm_num
  have hee : ∀ u ∈ e.erase v, (#((univ : Finset (Fin N)).filter
      fun b => (if u = v then b = j else if u ∈ e then b ≤ j else j ≤ b)) : ℝ)
      / Fintype.card (Fin N) = ((((j : ℕ) + 1 : ℕ) : ℝ) / N) := by
    intro u hu
    have hne : u ≠ v := Finset.ne_of_mem_erase hu
    have hue : u ∈ e := Finset.mem_of_mem_erase hu
    simp only [hne, if_false, hue, if_true, Fintype.card_fin]
    rw [hc2]
  rw [hev, Finset.prod_congr rfl hee, Finset.prod_const, Finset.card_erase_of_mem hve]

/-- The vertex shared by two edges, when there is exactly one. -/
noncomputable def sharedVertex [Nonempty V] (e f : Finset V) : V :=
  if h : ∃ v, e ∩ f = {v} then h.choose else Classical.arbitrary V

lemma sharedVertex_eq [Nonempty V] {e f : Finset V} {v : V} (h : e ∩ f = {v}) :
    sharedVertex e f = v := by
  have hex : ∃ w, e ∩ f = {w} := ⟨v, h⟩
  rw [sharedVertex, dif_pos hex]
  have hspec := hex.choose_spec
  have hsingle : ({v} : Finset V) = {hex.choose} := h.symm.trans hspec
  exact (Finset.singleton_inj.mp hsingle).symm

/-- Two edges carrying a conflict meet in exactly the conflicting vertex: a second common
vertex would have to lie both before and after it. -/
lemma inter_eq_singleton_of_conflict {val : V → Fin N} {e f : Finset V} {v : V}
    (hlast : IsLast val e v) (hfirst : IsFirst val f v) : e ∩ f = {v} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨Finset.mem_inter.mpr ⟨hlast.1, hfirst.1⟩, fun u hu => ?_⟩
  rw [Finset.mem_inter] at hu
  by_contra hne
  exact absurd (hlast.2 u hu.1 hne) (not_lt.mpr (le_of_lt (hfirst.2 u hu.2 hne)))

/-- A conflict at `v` puts the whole configuration inside `PMC.confEvent` at level `val v`. -/
lemma mem_confEvent_of_conflict {val : V → Fin N} {e f : Finset V} {v : V}
    (hlast : IsLast val e v) (hfirst : IsFirst val f v) :
    val ∈ confEvent e f v (val v) := by
  rw [confEvent, mem_filter]
  refine ⟨mem_univ _, fun u hu => ?_⟩
  by_cases huv : u = v
  · simp [huv]
  · rw [if_neg huv]
    by_cases hue : u ∈ e
    · rw [if_pos hue]
      exact val_le_of_vkey_lt (hlast.2 u hue huv)
    · rw [if_neg hue]
      have huf : u ∈ f := by
        rcases Finset.mem_union.mp hu with h | h
        · exact absurd h hue
        · exact h
      exact val_le_of_vkey_lt (hfirst.2 u huf huv)

/-- **The probabilistic half of Theorem 3.5.1.** If the three union bounds — an edge inside
`L`, an edge inside `R`, and a conflict at a level of `M` — total less than `1`, then `H` is
2-colourable.

The三 events are exactly the notes': no edge inside `L` or `R` forces the shared vertex of any
conflict into `M`, and then `PMC.exists_bichromatic_of_no_conflict` colours. -/
theorem twoColorable_of_union_bound [Nonempty V] (H : Finset (Finset V)) {k : ℕ}
    (hk : ∀ e ∈ H, #e = k) (hk2 : 2 ≤ k) (lo hi : Fin N)
    (hb : (#H : ℝ) * (((lo : ℕ) : ℝ) / N) ^ k + (#H : ℝ) * (((N - (hi : ℕ) : ℕ) : ℝ) / N) ^ k
        + ∑ q ∈ H ×ˢ H, ∑ j ∈ Finset.Ico lo hi,
            1 / (N : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / N) ^ (k - 1)
              * (((N - (j : ℕ) : ℕ) : ℝ) / N) ^ (k - 1) < 1) :
    TwoColorable H := by
  classical
  have hnn : ∀ val : V → Fin N, 0 ≤ unifProd V (Fin N) val := unifProd_nonneg
  set A : Finset (V → Fin N) := H.biUnion (fun e => lowEvent e lo) with hA
  set B : Finset (V → Fin N) := H.biUnion (fun e => highEvent e hi) with hB
  set P : Finset (Finset V × Finset V) :=
    (H ×ˢ H).filter (fun q => ∃ v, q.1 ∩ q.2 = {v}) with hP
  set C : Finset (V → Fin N) := P.biUnion
    (fun q => (Finset.Ico lo hi).biUnion
      fun j => confEvent q.1 q.2 (sharedVertex q.1 q.2) j) with hC
  -- the three weights
  have hAw : wprob (unifProd V (Fin N)) A ≤ (#H : ℝ) * (((lo : ℕ) : ℝ) / N) ^ k := by
    refine le_trans (wprob_biUnion_le hnn H _) ?_
    have : ∀ e ∈ H, wprob (unifProd V (Fin N)) (lowEvent e lo)
        = (((lo : ℕ) : ℝ) / N) ^ k := by
      intro e he
      rw [wprob_lowEvent, hk e he]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hBw : wprob (unifProd V (Fin N)) B ≤ (#H : ℝ) * (((N - (hi : ℕ) : ℕ) : ℝ) / N) ^ k := by
    refine le_trans (wprob_biUnion_le hnn H _) ?_
    have : ∀ e ∈ H, wprob (unifProd V (Fin N)) (highEvent e hi)
        = (((N - (hi : ℕ) : ℕ) : ℝ) / N) ^ k := by
      intro e he
      rw [wprob_highEvent, hk e he]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hCw : wprob (unifProd V (Fin N)) C
      ≤ ∑ q ∈ H ×ˢ H, ∑ j ∈ Finset.Ico lo hi,
          1 / (N : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / N) ^ (k - 1)
            * (((N - (j : ℕ) : ℕ) : ℝ) / N) ^ (k - 1) := by
    refine le_trans (wprob_biUnion_le hnn P _) ?_
    refine le_trans (Finset.sum_le_sum (g := fun q => ∑ j ∈ Finset.Ico lo hi,
        1 / (N : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / N) ^ (k - 1)
          * (((N - (j : ℕ) : ℕ) : ℝ) / N) ^ (k - 1)) fun q hq => ?_) ?_
    · refine le_trans (wprob_biUnion_le hnn (Finset.Ico lo hi) _) ?_
      refine Finset.sum_le_sum fun j hj => ?_
      rw [hP, mem_filter] at hq
      obtain ⟨v, hvsing⟩ := hq.2
      have hsing : q.1 ∩ q.2 = {sharedVertex q.1 q.2} := by
        rw [sharedVertex_eq hvsing]
        exact hvsing
      have h1 : #q.1 = k := hk q.1 (Finset.mem_product.mp hq.1).1
      have h2 : #q.2 = k := hk q.2 (Finset.mem_product.mp hq.1).2
      rw [wprob_confEvent q.1 q.2 _ hsing j, h1, h2]
    · refine Finset.sum_le_sum_of_subset_of_nonneg (by rw [hP]; exact Finset.filter_subset _ _)
        fun q _ _ => ?_
      refine Finset.sum_nonneg fun j _ => ?_
      positivity
  -- some value assignment avoids all three
  have htot : wprob (unifProd V (Fin N)) (A ∪ B ∪ C) < 1 := by
    have h1 : wprob (unifProd V (Fin N)) (A ∪ B ∪ C)
        ≤ wprob (unifProd V (Fin N)) (A ∪ B) + wprob (unifProd V (Fin N)) C :=
      wprob_union_le hnn _ _
    have h2 : wprob (unifProd V (Fin N)) (A ∪ B)
        ≤ wprob (unifProd V (Fin N)) A + wprob (unifProd V (Fin N)) B :=
      wprob_union_le hnn _ _
    linarith
  have hex : ∃ val : V → Fin N, val ∉ A ∪ B ∪ C := by
    by_contra hcon
    push_neg at hcon
    have huniv : A ∪ B ∪ C = univ := Finset.eq_univ_of_forall hcon
    rw [huniv, wprob_univ, sum_unifProd] at htot
    exact absurd htot (lt_irrefl 1)
  obtain ⟨val, hval⟩ := hex
  rw [Finset.mem_union, Finset.mem_union] at hval
  push_neg at hval
  obtain ⟨⟨hvalA, hvalB⟩, hvalC⟩ := hval
  -- no conflict survives
  refine exists_bichromatic_of_no_conflict H val (fun e he => by rw [hk e he]; exact hk2) ?_
  intro e he f hf v hlast hfirst
  have hsing := inter_eq_singleton_of_conflict hlast hfirst
  -- the shared vertex is in `M`
  have hlo : lo ≤ val v := by
    by_contra hcon
    push_neg at hcon
    refine hvalA (Finset.mem_biUnion.mpr ⟨e, he, ?_⟩)
    rw [lowEvent, mem_filter]
    refine ⟨mem_univ _, fun u hu => ?_⟩
    by_cases huv : u = v
    · rw [huv]; exact hcon
    · exact lt_of_le_of_lt (val_le_of_vkey_lt (hlast.2 u hu huv)) hcon
  have hhi : val v < hi := by
    by_contra hcon
    push_neg at hcon
    refine hvalB (Finset.mem_biUnion.mpr ⟨f, hf, ?_⟩)
    rw [highEvent, mem_filter]
    refine ⟨mem_univ _, fun u hu => ?_⟩
    by_cases huv : u = v
    · rw [huv]; exact hcon
    · exact le_trans hcon (val_le_of_vkey_lt (hfirst.2 u hu huv))
  refine hvalC (Finset.mem_biUnion.mpr ⟨(e, f), ?_, ?_⟩)
  · rw [hP, mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨he, hf⟩, ⟨v, hsing⟩⟩
  refine Finset.mem_biUnion.mpr ⟨val v, Finset.mem_Ico.mpr ⟨hlo, hhi⟩, ?_⟩
  rw [sharedVertex_eq hsing]
  exact mem_confEvent_of_conflict hlast hfirst

end Probability

section Main

/-- Each level contributes at most `(1/N)·((N+1)²/(4N²))^{k-1}`: the product
`(j+1)(N-j)` of the two block sizes is largest in the middle, where it is `((N+1)/2)²`. -/
private lemma conflict_term_le {N : ℕ} (hN : 0 < N) (j : Fin N) (k' : ℕ) :
    1 / (N : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / N) ^ k'
        * (((N - (j : ℕ) : ℕ) : ℝ) / N) ^ k'
      ≤ 1 / (N : ℝ) * (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ k' := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hjN : (j : ℕ) < N := j.isLt
  have hj : ((j : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast hjN
  have hjnn : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := by positivity
  have hcast : (((N - (j : ℕ) : ℕ)) : ℝ) = (N : ℝ) - ((j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hjN.le]
  have hcast' : ((((j : ℕ) + 1 : ℕ)) : ℝ) = ((j : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast, hcast', mul_assoc, ← mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine pow_le_pow_left₀ ?_ ?_ k'
  · refine mul_nonneg (by positivity) (div_nonneg (by linarith) hNR.le)
  · rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (((j : ℕ) : ℝ) + 1 - ((N : ℝ) - ((j : ℕ) : ℝ))), hNR, hj, hjnn]

set_option maxHeartbeats 1000000 in
/-- **Theorem 3.5.1** (Radhakrishnan–Srinivasan 2000; this proof Cherkashin–Kozik 2015).

Every `k`-uniform hypergraph with at most `(1/4) · 2^k · √(k / log k)` edges is 2-colourable.

The notes leave the constant existential and optimise `p` — the width of the middle block — as
`log(2^{k-1}k/m)/k`, depending on the number of edges. Taking

    p = log k / (2k)

instead makes the choice independent of `m`, and both conditions come out with room to spare:
writing `u = m 2^{1-k}`, the union bound needs `u(1-p)^k < 1/2` and `u²p < 1/4`, and

    u(1-p)^k < u e^{-pk} = u/√k ≤ 1/(2√(log k)) ≤ 1/2,    u²p ≤ (k/(4 log k))(log k/(2k)) = 1/8.

The levels are `Fin (32k)` — `32k` is large enough that rounding `p` to a multiple of `1/(32k)`
and the factor `(1 + 1/N)^{2(k-1)} ≤ 2` both stay inside that room. `k = 2` is handled by
§1.3's bound `2^{k-1}`, which the hypothesis already implies there. -/
theorem twoColorable_of_card_le {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 2 ≤ k)
    {H : Finset (Finset V)} (hcard : ∀ e ∈ H, #e = k)
    (hm : (#H : ℝ) ≤ 1 / 4 * 2 ^ k * Real.sqrt (k / Real.log k)) : TwoColorable H := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · -- no vertices at all, so there are no edges of size `k ≥ 2`
    have hHempty : H = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨e, he⟩
      have h1 : #e = k := hcard e he
      have h2 : #e = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_of_isEmpty e]
      omega
    exact ⟨fun _ => false, by simp [hHempty]⟩
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  rcases lt_or_ge k 3 with hk3 | hk3
  · -- `k = 2`: the hypothesis gives `#H ≤ √(2/log 2) < 2`
    have hk2 : k = 2 := by omega
    subst hk2
    refine twoColorable_of_card_lt_two_pow hcard ?_
    have hcast : (((2 : ℕ)) : ℝ) = 2 := by norm_num
    rw [hcast] at hm
    have hnn : (0 : ℝ) ≤ 2 / Real.log 2 := div_nonneg (by norm_num) (by linarith)
    have hs : Real.sqrt (2 / Real.log 2) < 2 := by
      have h4 : (2 : ℝ) / Real.log 2 < 4 := by
        rw [div_lt_iff₀ (by linarith)]
        linarith
      calc Real.sqrt (2 / Real.log 2) < Real.sqrt 4 := Real.sqrt_lt_sqrt hnn h4
        _ = 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    have hlt : (#H : ℝ) < 2 := by
      have : (1 : ℝ) / 4 * 2 ^ 2 * Real.sqrt (2 / Real.log 2)
          = Real.sqrt (2 / Real.log 2) := by ring
      rw [this] at hm
      linarith
    have h2 : #H < 2 := by exact_mod_cast hlt
    simpa using h2
  -- the main case
  let _ : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Equiv.injective _)
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
  have hk0 : (0 : ℝ) < k := by linarith
  have hlogk : (1 : ℝ) ≤ Real.log k := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (by norm_num) hkR
    linarith
  have hlogkpos : (0 : ℝ) < Real.log k := by linarith
  have hlogkle : Real.log k ≤ (k : ℝ) := by
    have := Real.log_le_sub_one_of_pos hk0
    linarith
  -- the parameters
  set m : ℕ := #H with hmdef
  set N : ℕ := 32 * k with hNdef
  haveI : NeZero N := ⟨by omega⟩
  have hNR : (N : ℝ) = 32 * k := by rw [hNdef]; push_cast; ring
  have hNpos : (0 : ℝ) < N := by rw [hNR]; linarith
  set p : ℝ := Real.log k / (2 * k) with hpdef
  have hp0 : 0 < p := by rw [hpdef]; exact div_pos hlogkpos (by linarith)
  have hp2 : p ≤ 1 / 2 := by
    rw [hpdef, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  set a : ℕ := ⌊(N : ℝ) * (1 - p) / 2⌋₊ with hadef
  have hxnn : (0 : ℝ) ≤ (N : ℝ) * (1 - p) / 2 := by
    have : (0 : ℝ) ≤ 1 - p := by linarith
    positivity
  have haub : (a : ℝ) ≤ (N : ℝ) * (1 - p) / 2 := by rw [hadef]; exact Nat.floor_le hxnn
  have halb : (N : ℝ) * (1 - p) / 2 - 1 < (a : ℝ) := by
    rw [hadef]
    have := Nat.lt_floor_add_one ((N : ℝ) * (1 - p) / 2)
    linarith
  have haN : 2 * a ≤ N := by
    have h1 : (2 * a : ℝ) ≤ (N : ℝ) * (1 - p) := by linarith
    have h2 : (N : ℝ) * (1 - p) ≤ (N : ℝ) := by nlinarith
    have : ((2 * a : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have ha1 : 1 ≤ a := by
    have h1 : (2 : ℝ) ≤ (N : ℝ) * (1 - p) / 2 := by
      rw [hNR]
      nlinarith
    have : (1 : ℝ) ≤ (a : ℝ) := by linarith
    exact_mod_cast this
  have haltN : a < N := by omega
  refine twoColorable_of_union_bound (N := N) H hcard (by omega)
    (⟨a, haltN⟩ : Fin N) (⟨N - a, by omega⟩ : Fin N) ?_
  -- the three terms
  have hcast1 : ((⟨a, haltN⟩ : Fin N) : ℕ) = a := rfl
  have hcast2 : ((⟨N - a, by omega⟩ : Fin N) : ℕ) = N - a := rfl
  set u : ℝ := 2 * (m : ℝ) / 2 ^ k with hudef
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  have husq : u ^ 2 ≤ (k : ℝ) / (4 * Real.log k) := by
    have hsq : Real.sqrt ((k : ℝ) / Real.log k) ^ 2 = (k : ℝ) / Real.log k :=
      Real.sq_sqrt (by positivity)
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have hub : u ≤ 1 / 2 * Real.sqrt ((k : ℝ) / Real.log k) := by
      rw [hudef, div_le_iff₀ h2k]
      nlinarith [hm, Real.sqrt_nonneg ((k : ℝ) / Real.log k)]
    calc u ^ 2 ≤ (1 / 2 * Real.sqrt ((k : ℝ) / Real.log k)) ^ 2 := by
          exact pow_le_pow_left₀ hu0 hub 2
      _ = 1 / 4 * ((k : ℝ) / Real.log k) := by rw [mul_pow, hsq]; ring
      _ = (k : ℝ) / (4 * Real.log k) := by field_simp
  -- Part 1: the two outer blocks
  have hA : (m : ℝ) * (((a : ℕ) : ℝ) / N) ^ k
      + (m : ℝ) * (((N - (N - a) : ℕ) : ℝ) / N) ^ k ≤ 1 / 2 := by
    have hNa : N - (N - a) = a := by omega
    rw [hNa]
    have hratio : ((a : ℕ) : ℝ) / N ≤ (1 - p) / 2 := by
      rw [div_le_div_iff₀ hNpos (by norm_num)]
      linarith
    have hnn : (0 : ℝ) ≤ ((a : ℕ) : ℝ) / N := by positivity
    have hpow : (((a : ℕ) : ℝ) / N) ^ k ≤ ((1 - p) / 2) ^ k := pow_le_pow_left₀ hnn hratio k
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hstep : (m : ℝ) * (((a : ℕ) : ℝ) / N) ^ k + (m : ℝ) * (((a : ℕ) : ℝ) / N) ^ k
        ≤ 2 * (m : ℝ) * ((1 - p) / 2) ^ k := by nlinarith
    -- `2m((1-p)/2)^k = u(1-p)^k ≤ u e^{-pk} = u/√k ≤ 1/2`
    have hid : 2 * (m : ℝ) * ((1 - p) / 2) ^ k = u * (1 - p) ^ k := by
      rw [hudef, div_pow]
      field_simp
    have hexp : (1 - p) ^ k ≤ Real.exp (-(p * k)) := by
      have h1 : (1 - p) ≤ Real.exp (-p) := by
        have := Real.add_one_le_exp (-p)
        linarith
      calc (1 - p) ^ k ≤ (Real.exp (-p)) ^ k := by
            refine pow_le_pow_left₀ (by linarith) h1 k
        _ = Real.exp (-(p * k)) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
    have hsqk : Real.exp (-(p * k)) = 1 / Real.sqrt k := by
      have hpk : p * k = Real.log k / 2 := by
        rw [hpdef]
        field_simp
      have hs : Real.sqrt (k : ℝ) = Real.exp (Real.log k / 2) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hk0]
        congr 1
        ring
      rw [hpk, Real.exp_neg, hs, inv_eq_one_div]
    have hfinal : u * (1 - p) ^ k ≤ 1 / 2 := by
      have hsk : (1 : ℝ) ≤ Real.sqrt (Real.log k) := by
        rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
        exact Real.sqrt_le_sqrt hlogk
      have hskpos : (0 : ℝ) < Real.sqrt (Real.log k) := by linarith
      have hkpos : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.mpr hk0
      have hub : u ≤ 1 / 2 * (Real.sqrt k / Real.sqrt (Real.log k)) := by
        have hdiv : Real.sqrt ((k : ℝ) / Real.log k)
            = Real.sqrt k / Real.sqrt (Real.log k) := Real.sqrt_div hk0.le _
        have hub' : u ≤ 1 / 2 * Real.sqrt ((k : ℝ) / Real.log k) := by
          have h2k : (0 : ℝ) < 2 ^ k := by positivity
          rw [hudef, div_le_iff₀ h2k]
          nlinarith [hm, Real.sqrt_nonneg ((k : ℝ) / Real.log k)]
        rwa [hdiv] at hub'
      calc u * (1 - p) ^ k ≤ u * Real.exp (-(p * k)) := by
            exact mul_le_mul_of_nonneg_left hexp hu0
        _ = u * (1 / Real.sqrt k) := by rw [hsqk]
        _ ≤ (1 / 2 * (Real.sqrt k / Real.sqrt (Real.log k))) * (1 / Real.sqrt k) := by
            refine mul_le_mul_of_nonneg_right hub (by positivity)
        _ = 1 / 2 * (1 / Real.sqrt (Real.log k)) := by field_simp
        _ ≤ 1 / 2 := by
            rw [mul_le_iff_le_one_right (by norm_num : (0:ℝ) < 1/2)]
            rw [div_le_one hskpos]
            exact hsk
    linarith only [hstep, hid, hfinal]
  -- Part 2: the conflict term
  obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hkm1 : k - 1 = k' := by omega
  set B : ℝ := 1 / (N : ℝ) * (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ k' with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hterm : ∀ j : Fin N,
      1 / (N : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / N) ^ (k - 1)
        * (((N - (j : ℕ) : ℕ) : ℝ) / N) ^ (k - 1) ≤ B := by
    intro j
    rw [hkm1, hBdef]
    exact conflict_term_le (by omega) j k'
  have hcardIco : #(Finset.Ico (⟨a, haltN⟩ : Fin N) (⟨N - a, by omega⟩ : Fin N)) = N - 2 * a := by
    rw [Fin.card_Ico]
    simp only [hcast1, hcast2]
    omega
  have hB : ∑ q ∈ H ×ˢ H, ∑ j ∈ Finset.Ico (⟨a, haltN⟩ : Fin N) (⟨N - a, by omega⟩ : Fin N),
      1 / (N : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / N) ^ (k - 1)
        * (((N - (j : ℕ) : ℕ) : ℝ) / N) ^ (k - 1) < 1 / 2 := by
    have hinner : ∀ q ∈ H ×ˢ H,
        (∑ j ∈ Finset.Ico (⟨a, haltN⟩ : Fin N) (⟨N - a, by omega⟩ : Fin N),
          1 / (N : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / N) ^ (k - 1)
            * (((N - (j : ℕ) : ℕ) : ℝ) / N) ^ (k - 1))
        ≤ ((N - 2 * a : ℕ) : ℝ) * B := by
      intro q _
      refine le_trans (Finset.sum_le_card_nsmul _ _ B fun j _ => hterm j) ?_
      rw [nsmul_eq_mul, hcardIco]
    have hmm : ((m * m : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
    -- `(N - 2a)/N ≤ p + 2/N`
    have hp' : ((N - 2 * a : ℕ) : ℝ) ≤ (N : ℝ) * p + 2 := by
      have hc : ((N - 2 * a : ℕ) : ℝ) = (N : ℝ) - 2 * (a : ℝ) := by
        rw [Nat.cast_sub haN]
        push_cast
        ring
      rw [hc]
      linarith
    -- `((N+1)²/(4N²))^{k'} ≤ 2 * (1/4)^{k'}`
    have hgrow : (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ k' ≤ 2 * (1 / 4 : ℝ) ^ k' := by
      have hfac : ((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)
          = (1 / 4) * (1 + 1 / (N : ℝ)) ^ 2 := by
        field_simp
      rw [hfac, mul_pow, mul_comm (2 : ℝ) ((1 / 4 : ℝ) ^ k')]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      -- `(1 + 1/N)^{2k'} ≤ 2`
      have hstep : ((1 : ℝ) + 1 / (N : ℝ)) ^ 2 ≤ Real.exp (2 / (N : ℝ)) := by
        have h1 : (1 : ℝ) + 1 / (N : ℝ) ≤ Real.exp (1 / (N : ℝ)) := by
          have := Real.add_one_le_exp (1 / (N : ℝ))
          linarith
        calc ((1 : ℝ) + 1 / (N : ℝ)) ^ 2 ≤ (Real.exp (1 / (N : ℝ))) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h1 2
          _ = Real.exp (2 / (N : ℝ)) := by
              rw [← Real.exp_nat_mul]
              congr 1
              push_cast
              ring
      calc (((1 : ℝ) + 1 / (N : ℝ)) ^ 2) ^ k'
          ≤ (Real.exp (2 / (N : ℝ))) ^ k' := pow_le_pow_left₀ (by positivity) hstep k'
        _ = Real.exp (k' * (2 / (N : ℝ))) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp (1 / 16) := by
            refine Real.exp_le_exp.mpr ?_
            rw [hNR]
            have hk'R : (k' : ℝ) ≤ (k : ℝ) := by
              have h : k' ≤ k := by omega
              exact_mod_cast h
            have hstep2 : (k' : ℝ) * (2 / (32 * (k : ℝ))) = (k' : ℝ) / (16 * (k : ℝ)) := by
              ring
            rw [hstep2, div_le_div_iff₀ (by positivity) (by norm_num)]
            linarith only [hk'R, hk0]
        _ ≤ 2 := by
            rw [show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm]
            exact Real.exp_le_exp.mpr (by linarith)
    -- put it together
    have hkey : (m : ℝ) ^ 2 * (((N - 2 * a : ℕ) : ℝ) * B) < 1 / 2 := by
      have hid4 : ((4 : ℝ)) ^ k * (1 / 4 : ℝ) ^ k' = 4 := by
        rw [hk', pow_succ, mul_comm ((4:ℝ)^k') 4, mul_assoc, ← mul_pow]
        norm_num
      have hmsq : (m : ℝ) ^ 2 ≤ 1 / 16 * (4 : ℝ) ^ k * ((k : ℝ) / Real.log k) := by
        have hsq : Real.sqrt ((k : ℝ) / Real.log k) ^ 2 = (k : ℝ) / Real.log k :=
          Real.sq_sqrt (by positivity)
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := by positivity
        have h2 : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
          rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 from by norm_num, ← pow_mul]
          congr 1
          ring
        calc (m : ℝ) ^ 2 ≤ (1 / 4 * 2 ^ k * Real.sqrt ((k : ℝ) / Real.log k)) ^ 2 :=
              pow_le_pow_left₀ hmnn hm 2
          _ = 1 / 16 * ((2 : ℝ) ^ k) ^ 2 * ((k : ℝ) / Real.log k) := by
              rw [mul_pow, mul_pow, hsq]
              ring
          _ = 1 / 16 * (4 : ℝ) ^ k * ((k : ℝ) / Real.log k) := by rw [h2]
      -- expand `B`
      rw [hBdef]
      have hchain : ((N - 2 * a : ℕ) : ℝ) * (1 / (N : ℝ)
          * (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ k')
          ≤ ((N : ℝ) * p + 2) * (1 / (N : ℝ)) * (2 * (1 / 4 : ℝ) ^ k') := by
        have h1 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
        have h2 : (0 : ℝ) ≤ (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ k' := by positivity
        have h3 : (0 : ℝ) ≤ ((N - 2 * a : ℕ) : ℝ) := by positivity
        calc ((N - 2 * a : ℕ) : ℝ) * (1 / (N : ℝ)
              * (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ k')
            ≤ ((N : ℝ) * p + 2) * (1 / (N : ℝ)
              * (((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2)) ^ k') := by
              refine mul_le_mul_of_nonneg_right hp' (by positivity)
          _ ≤ ((N : ℝ) * p + 2) * (1 / (N : ℝ) * (2 * (1 / 4 : ℝ) ^ k')) := by
              refine mul_le_mul_of_nonneg_left ?_ (by
                have h4 : (0:ℝ) ≤ (N:ℝ) * p := by positivity
                linarith only [h4])
              exact mul_le_mul_of_nonneg_left hgrow h1
          _ = ((N : ℝ) * p + 2) * (1 / (N : ℝ)) * (2 * (1 / 4 : ℝ) ^ k') := by ring
      have hmnn2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
      refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left hchain hmnn2) ?_
      -- now a pure computation
      have hNp : ((N : ℝ) * p + 2) * (1 / (N : ℝ)) = p + 2 / (N : ℝ) := by
        field_simp
      rw [hNp]
      have hpval : p + 2 / (N : ℝ) ≤ Real.log k / (2 * k) + 1 / (16 * k) := by
        rw [hpdef, hNR]
        have : (2 : ℝ) / (32 * k) = 1 / (16 * k) := by ring
        rw [this]
      have hstep2 : (m : ℝ) ^ 2 * ((p + 2 / (N : ℝ)) * (2 * (1 / 4 : ℝ) ^ k'))
          ≤ (1 / 16 * (4 : ℝ) ^ k * ((k : ℝ) / Real.log k))
            * ((Real.log k / (2 * k) + 1 / (16 * k)) * (2 * (1 / 4 : ℝ) ^ k')) := by
        refine mul_le_mul hmsq ?_ (by positivity) (by positivity)
        refine mul_le_mul_of_nonneg_right hpval (by positivity)
      refine lt_of_le_of_lt hstep2 ?_
      -- `(1/16)·4^k·(1/4)^{k'}·2 = 1/2`, and `(k/log k)(log k/(2k) + 1/(16k)) ≤ 1/2 + 1/16`
      have hfrac : ((k : ℝ) / Real.log k) * (Real.log k / (2 * k) + 1 / (16 * k))
          ≤ 1 / 2 + 1 / 16 := by
        have h1 : ((k : ℝ) / Real.log k) * (Real.log k / (2 * k)) = 1 / 2 := by
          field_simp
        have h2 : ((k : ℝ) / Real.log k) * (1 / (16 * k)) = 1 / (16 * Real.log k) := by
          field_simp
        have h3 : 1 / (16 * Real.log k) ≤ 1 / 16 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        calc ((k : ℝ) / Real.log k) * (Real.log k / (2 * k) + 1 / (16 * k))
            = ((k : ℝ) / Real.log k) * (Real.log k / (2 * k))
              + ((k : ℝ) / Real.log k) * (1 / (16 * k)) := by ring
          _ = 1 / 2 + 1 / (16 * Real.log k) := by rw [h1, h2]
          _ ≤ 1 / 2 + 1 / 16 := by linarith
      have hrearr : (1 / 16 * (4 : ℝ) ^ k * ((k : ℝ) / Real.log k))
            * ((Real.log k / (2 * k) + 1 / (16 * k)) * (2 * (1 / 4 : ℝ) ^ k'))
          = (1 / 8) * ((4 : ℝ) ^ k * (1 / 4 : ℝ) ^ k')
            * (((k : ℝ) / Real.log k) * (Real.log k / (2 * k) + 1 / (16 * k))) := by
        ring
      rw [hrearr, hid4]
      linarith only [hfrac]
    calc (∑ q ∈ H ×ˢ H, ∑ j ∈ Finset.Ico (⟨a, haltN⟩ : Fin N) (⟨N - a, by omega⟩ : Fin N),
          1 / (N : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / N) ^ (k - 1)
            * (((N - (j : ℕ) : ℕ) : ℝ) / N) ^ (k - 1))
        ≤ ∑ _q ∈ H ×ˢ H, ((N - 2 * a : ℕ) : ℝ) * B := Finset.sum_le_sum hinner
      _ = (m : ℝ) ^ 2 * (((N - 2 * a : ℕ) : ℝ) * B) := by
          rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
          push_cast
          ring
      _ < 1 / 2 := hkey
  linarith only [hA, hB]

end Main

end PMC



