import ProbMethods.Chapter06.LocalLemma
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# §6.2 — Colouring hypergraphs by the local lemma

Zhao, *Probabilistic Methods in Combinatorics*, §6.2.

The local-lemma strengthening of §1.3's `PMC.twoColorable_of_card_lt_two_pow`: instead of
bounding the *total* number of edges, it is enough that no edge meets too many others.

Colourings are subsets `S ⊆ V` (the vertices coloured one way), so the sample space is
`Finset V` with the uniform weight. The event "edge `i` is monochromatic" is determined by
the coordinates in `edge i`, which is what discharges the local lemma's independence
hypothesis via `PMC.card_inter_mul_of_determinedBy`.
-/

open Finset

namespace PMC

section Coloring

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- The event that edge `i` is monochromatic: the colouring `S` either contains all of it
or misses all of it. -/
def monoEvent (edge : ι → Finset V) (i : ι) : Finset (Finset V) :=
  (univ : Finset (Finset V)).filter fun S => edge i ⊆ S ∨ edge i ∩ S = ∅

/-- Being monochromatic on `edge i` depends only on the colours of `edge i`'s vertices. -/
theorem determinedBy_monoEvent (edge : ι → Finset V) (i : ι) :
    DeterminedBy (edge i) (monoEvent edge i) := by
  intro S T hST
  have hsub : edge i ⊆ S ↔ edge i ⊆ T := by
    constructor
    · intro h x hx
      have : x ∈ S ∩ edge i := mem_inter.mpr ⟨h hx, hx⟩
      rw [hST] at this
      exact (mem_inter.mp this).1
    · intro h x hx
      have : x ∈ T ∩ edge i := mem_inter.mpr ⟨h hx, hx⟩
      rw [← hST] at this
      exact (mem_inter.mp this).1
  have hdis : edge i ∩ S = ∅ ↔ edge i ∩ T = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
    constructor
    · intro h ⟨x, hx⟩
      rw [mem_inter] at hx
      have : x ∈ T ∩ edge i := mem_inter.mpr ⟨hx.2, hx.1⟩
      rw [← hST, mem_inter] at this
      exact h ⟨x, mem_inter.mpr ⟨hx.1, this.1⟩⟩
    · intro h ⟨x, hx⟩
      rw [mem_inter] at hx
      have : x ∈ S ∩ edge i := mem_inter.mpr ⟨hx.2, hx.1⟩
      rw [hST, mem_inter] at this
      exact h ⟨x, mem_inter.mpr ⟨hx.1, this.1⟩⟩
  simp only [monoEvent, mem_filter, mem_univ, true_and]
  rw [hsub, hdis]

/-- A `k`-edge is monochromatic under exactly `2 * 2 ^ (n - k)` of the `2 ^ n` colourings:
all of it one colour, or all of it the other. -/
theorem card_monoEvent (edge : ι → Finset V) (i : ι) {k : ℕ} (hk : 1 ≤ k)
    (hcard : #(edge i) = k) :
    #(monoEvent edge i) = 2 * 2 ^ (Fintype.card V - k) := by
  classical
  have hdet := determinedBy_monoEvent edge i
  rw [hdet.card_eq]
  have hsdiff : #((univ : Finset V) \ edge i) = Fintype.card V - k := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hcard]
  -- the traces on `edge i` that are monochromatic are exactly `∅` and `edge i`
  have htrace : (edge i).powerset.filter (fun U => U ∈ monoEvent edge i)
      = {∅, edge i} := by
    ext U
    simp only [mem_filter, mem_powerset, monoEvent, mem_univ, true_and, mem_insert,
      mem_singleton]
    constructor
    · rintro ⟨hUsub, hU | hU⟩
      · exact Or.inr (Finset.Subset.antisymm hUsub hU)
      · refine Or.inl (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_)
        have : x ∈ edge i ∩ U := mem_inter.mpr ⟨hUsub hx, hx⟩
        rw [hU] at this
        exact notMem_empty x this
    · rintro (rfl | rfl)
      · exact ⟨empty_subset _, Or.inr (by simp)⟩
      · exact ⟨Subset.rfl, Or.inl Subset.rfl⟩
  have hne : (∅ : Finset V) ≠ edge i := by
    intro h
    rw [← h] at hcard
    simp at hcard
    omega
  rw [htrace, card_insert_of_notMem (by simpa using hne), card_singleton, hsdiff]
  ring

/-! ### The uniform weight on colourings -/

/-- The uniform weight on the `2 ^ n` colourings of `V`. -/
noncomputable def unifColoring (V : Type*) [Fintype V] : Finset V → ℝ :=
  fun _ => 1 / 2 ^ Fintype.card V

lemma unifColoring_apply (S : Finset V) :
    unifColoring V S = 1 / 2 ^ Fintype.card V := rfl

lemma unifColoring_nonneg (S : Finset V) : 0 ≤ unifColoring V S := by
  rw [unifColoring_apply]; positivity

lemma sum_unifColoring : ∑ S : Finset V, unifColoring V S = 1 := by
  rw [Finset.sum_congr rfl fun S _ => unifColoring_apply S, Finset.sum_const, nsmul_eq_mul,
    card_univ, Fintype.card_finset]
  push_cast
  rw [mul_one_div, div_self (by positivity)]

/-- Under the uniform weight, probability is counting. -/
lemma wprob_unifColoring (A : Finset (Finset V)) :
    wprob (unifColoring V) A = #A / 2 ^ Fintype.card V := by
  rw [wprob, Finset.sum_congr rfl fun S _ => unifColoring_apply S, Finset.sum_const,
    nsmul_eq_mul, mul_one_div]

/-- **Independence for the uniform colouring**, in the exact shape the local lemma wants:
events determined by disjoint blocks of vertices have multiplicative probability. -/
lemma wprob_unifColoring_mul_of_determinedBy {C : Finset V} {A A' : Finset (Finset V)}
    (hA : DeterminedBy C A) (hA' : DeterminedBy ((univ : Finset V) \ C) A') :
    wprob (unifColoring V) (A ∩ A')
      = wprob (unifColoring V) A * wprob (unifColoring V) A' := by
  have h : (#(A ∩ A') : ℝ) * 2 ^ Fintype.card V = #A * #A' := by
    exact_mod_cast card_inter_mul_of_determinedBy hA hA'
  have hpos : (0 : ℝ) < 2 ^ Fintype.card V := by positivity
  rw [wprob_unifColoring, wprob_unifColoring, wprob_unifColoring, div_mul_div_comm,
    div_eq_div_iff (by positivity) (by positivity)]
  calc (#(A ∩ A') : ℝ) * (2 ^ Fintype.card V * 2 ^ Fintype.card V)
      = (#(A ∩ A') * 2 ^ Fintype.card V) * 2 ^ Fintype.card V := by ring
    _ = #A * #A' * 2 ^ Fintype.card V := by rw [h]

/-! ### The dependency graph: sharing a vertex -/

/-- Two edges are dependent exactly when they share a vertex. -/
def sharesVertex (edge : ι → Finset V) (i : ι) : Finset ι :=
  univ.filter fun j => j ≠ i ∧ (edge i ∩ edge j).Nonempty

@[simp] lemma mem_sharesVertex {edge : ι → Finset V} {i j : ι} :
    j ∈ sharesVertex edge i ↔ j ≠ i ∧ (edge i ∩ edge j).Nonempty := by
  simp [sharesVertex]

/-- If `A j` is determined by the vertices of `edge j` for every `j`, then "none of the
edges in `T` is monochromatic" is determined by any block containing all of them. -/
theorem determinedBy_noneOf {A : ι → Finset (Finset V)} {C : ι → Finset V}
    (hA : ∀ j, DeterminedBy (C j) (A j)) {D : Finset V} {T : Finset ι}
    (hT : ∀ j ∈ T, C j ⊆ D) : DeterminedBy D (noneOf A T) := by
  classical
  revert hT
  induction T using Finset.induction_on with
  | empty => intro _; simpa using determinedBy_univ D
  | @insert i T _ ih =>
      intro hT
      rw [noneOf_insert]
      exact ((hA i).mono (hT i (mem_insert_self i T))).compl.inter
        (ih fun j hj => hT j (mem_insert_of_mem hj))

/-- **§6.2 — 2-colouring a hypergraph by the local lemma** (Zhao, Theorem 6.2.1).

If every edge of a `k`-uniform hypergraph meets at most `d` others, and
`e (d+1) 2^(1-k) ≤ 1`, then the hypergraph is 2-colourable: some set `S` of vertices both
fails to contain and fails to miss every edge.

This strengthens §1.3's `PMC.twoColorable_of_card_lt_two_pow`, which bounds the *total*
number of edges: here the bound is local, on how many edges any one edge meets, so it
applies to arbitrarily large hypergraphs.

The three inputs are `PMC.lovasz_local_lemma_symmetric`, `PMC.card_monoEvent` for the
probability `2 ^ (1-k)`, and `PMC.wprob_unifColoring_mul_of_determinedBy` for independence
— the last via `PMC.determinedBy_monoEvent`, since edges sharing no vertex give events on
disjoint blocks of coordinates. -/
theorem exists_two_coloring_of_local_lemma' (edge : ι → Finset V) {k d : ℕ}
    (hk : 1 ≤ k) (hd : 0 < d) (hcard : ∀ i, k ≤ #(edge i))
    (hdeg : ∀ i, #(sharesVertex edge i) ≤ d)
    (hep : Real.exp 1 * ((d : ℝ) + 1) * (2 / 2 ^ k) ≤ 1) :
    ∃ S : Finset V, ∀ i, ¬ edge i ⊆ S ∧ (edge i ∩ S).Nonempty := by
  classical
  by_cases hι : Nonempty ι
  · obtain ⟨i0⟩ := hι
    -- each event has probability `2 ^ (1 - #(edge i)) ≤ 2 ^ (1 - k)`
    have hprob : ∀ i, wprob (unifColoring V) (monoEvent edge i) ≤ 2 / 2 ^ k := by
      intro i
      have hm : 1 ≤ #(edge i) := le_trans hk (hcard i)
      have hmn : #(edge i) ≤ Fintype.card V := by
        rw [← card_univ]
        exact card_le_card (subset_univ _)
      rw [wprob_unifColoring, card_monoEvent edge i hm rfl]
      have hval : ((2 * 2 ^ (Fintype.card V - #(edge i)) : ℕ) : ℝ) / 2 ^ Fintype.card V
          = 2 / 2 ^ #(edge i) := by
        push_cast
        rw [div_eq_div_iff (by positivity) (by positivity)]
        calc (2 : ℝ) * 2 ^ (Fintype.card V - #(edge i)) * 2 ^ #(edge i)
            = 2 * (2 ^ (Fintype.card V - #(edge i)) * 2 ^ #(edge i)) := by ring
          _ = 2 * 2 ^ Fintype.card V := by
              rw [← pow_add, Nat.sub_add_cancel hmn]
      rw [hval]
      refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
      exact pow_le_pow_right₀ (by norm_num) (hcard i)
    -- edges sharing no vertex are independent
    have hindep : ∀ (i : ι) (T : Finset ι), Disjoint T (insert i (sharesVertex edge i)) →
        wprob (unifColoring V) (monoEvent edge i ∩ noneOf (monoEvent edge) T)
          = wprob (unifColoring V) (monoEvent edge i)
            * wprob (unifColoring V) (noneOf (monoEvent edge) T) := by
      intro i T hT
      refine wprob_unifColoring_mul_of_determinedBy (determinedBy_monoEvent edge i) ?_
      refine determinedBy_noneOf (fun j => determinedBy_monoEvent edge j) ?_
      intro j hj x hx
      have hjnot : j ∉ insert i (sharesVertex edge i) := Finset.disjoint_left.mp hT hj
      have hji : j ≠ i := by
        intro h
        exact hjnot (by rw [h]; exact mem_insert_self i _)
      have hempty : edge i ∩ edge j = ∅ := by
        by_contra h
        exact hjnot (mem_insert_of_mem
          (mem_sharesVertex.mpr ⟨hji, Finset.nonempty_iff_ne_empty.mpr h⟩))
      rw [mem_sdiff]
      refine ⟨mem_univ x, fun hxi => ?_⟩
      have hmem : x ∈ edge i ∩ edge j := mem_inter.mpr ⟨hxi, hx⟩
      rw [hempty] at hmem
      exact notMem_empty x hmem
    have hpos := lovasz_local_lemma_symmetric (unifColoring V) unifColoring_nonneg
      sum_unifColoring (monoEvent edge) (sharesVertex edge) hd (by positivity)
      (fun i => by simp) hdeg hindep hprob
      (by calc Real.exp 1 * (2 / 2 ^ k) * ((d : ℝ) + 1)
              = Real.exp 1 * ((d : ℝ) + 1) * (2 / 2 ^ k) := by ring
            _ ≤ 1 := hep)
    -- a positive-probability event is nonempty, and its members are the good colourings
    have hne : (noneOf (monoEvent edge) (univ : Finset ι)).Nonempty := by
      rcases Finset.eq_empty_or_nonempty (noneOf (monoEvent edge) (univ : Finset ι)) with
        h | h
      · rw [h, wprob_empty] at hpos; linarith
      · exact h
    obtain ⟨S, hS⟩ := hne
    refine ⟨S, fun i => ?_⟩
    have hSi : S ∉ monoEvent edge i := mem_noneOf.mp hS i (mem_univ i)
    simp only [monoEvent, mem_filter, mem_univ, true_and, not_or] at hSi
    exact ⟨hSi.1, Finset.nonempty_iff_ne_empty.mpr hSi.2⟩

  · exact ⟨∅, fun i => absurd ⟨i⟩ hι⟩

/-- **Theorem 6.2.1.** A `k`-uniform hypergraph in which every edge meets at most `d` others
is 2-colourable once `e (d+1) 2^{1-k} ≤ 1` — equivalently, once every edge meets at most
`e⁻¹ 2^{k-1} - 1` others, which is how the notes state it.

The uniform case of `PMC.exists_two_coloring_of_local_lemma'`, which only needs the edges to
have size *at least* `k`. -/
theorem exists_two_coloring_of_local_lemma (edge : ι → Finset V) {k d : ℕ}
    (hk : 1 ≤ k) (hd : 0 < d) (hcard : ∀ i, #(edge i) = k)
    (hdeg : ∀ i, #(sharesVertex edge i) ≤ d)
    (hep : Real.exp 1 * ((d : ℝ) + 1) * (2 / 2 ^ k) ≤ 1) :
    ∃ S : Finset V, ∀ i, ¬ edge i ⊆ S ∧ (edge i ∩ S).Nonempty :=
  exists_two_coloring_of_local_lemma' edge hk hd (fun i => le_of_eq (hcard i).symm) hdeg hep


/-- The numeric side condition of Corollary 6.2.2: `2e(k² - k + 1) ≤ 2ᵏ` for `k ≥ 9`.

Induction from `k = 9`, where `2e·73 ≈ 396.9 ≤ 512`. The step needs only
`k² + k + 1 ≤ 2(k² - k + 1)`, i.e. `k² - 3k + 1 ≥ 0`, which holds from `k = 3` on — so `9` is
forced by the base case, not by the induction. -/
private lemma two_exp_mul_le_two_pow {m : ℕ} (hm : 9 ≤ m) :
    2 * Real.exp 1 * ((m : ℝ) * ((m : ℝ) - 1) + 1) ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base =>
      have he := Real.exp_one_lt_d9
      norm_num
      nlinarith [he]
  | succ m hm ih =>
      have hmR : (9 : ℝ) ≤ m := by exact_mod_cast hm
      push_cast
      have hstep : ((m : ℝ) + 1) * (((m : ℝ) + 1) - 1) + 1
          ≤ 2 * ((m : ℝ) * ((m : ℝ) - 1) + 1) := by nlinarith
      have hepos : (0 : ℝ) < 2 * Real.exp 1 := by positivity
      calc 2 * Real.exp 1 * (((m : ℝ) + 1) * (((m : ℝ) + 1) - 1) + 1)
          ≤ 2 * Real.exp 1 * (2 * ((m : ℝ) * ((m : ℝ) - 1) + 1)) :=
            mul_le_mul_of_nonneg_left hstep (le_of_lt hepos)
        _ = 2 * (2 * Real.exp 1 * ((m : ℝ) * ((m : ℝ) - 1) + 1)) := by ring
        _ ≤ 2 * 2 ^ m := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = 2 ^ (m + 1) := by
            push_cast
            ring

/-- **Corollary 6.2.2.** For `k ≥ 9`, every `k`-uniform `k`-regular hypergraph is
2-colourable. (`k`-regular: every vertex lies in exactly `k` edges.)

The degree count is the content: an edge has `k` vertices, each lying in `k` edges, one of
which is the edge itself, so it meets at most `k(k-1)` others. Then `e(k(k-1)+1)2^{1-k} ≤ 1`
holds from `k = 9` on. -/
theorem exists_two_coloring_of_regular (edge : ι → Finset V) {k : ℕ} (hk : 9 ≤ k)
    (hcard : ∀ i, #(edge i) = k)
    (hreg : ∀ v : V, #((univ : Finset ι).filter fun j => v ∈ edge j) = k) :
    ∃ S : Finset V, ∀ i, ¬ edge i ⊆ S ∧ (edge i ∩ S).Nonempty := by
  classical
  -- each edge meets at most `k(k-1)` others
  have hdeg : ∀ i, #(sharesVertex edge i) ≤ k * (k - 1) := by
    intro i
    have hsub : sharesVertex edge i
        ⊆ (edge i).biUnion fun v => ((univ : Finset ι).filter fun j => v ∈ edge j).erase i := by
      intro j hj
      rw [mem_sharesVertex] at hj
      obtain ⟨v, hv⟩ := hj.2
      rw [mem_inter] at hv
      refine Finset.mem_biUnion.mpr ⟨v, hv.1, ?_⟩
      rw [Finset.mem_erase, mem_filter]
      exact ⟨hj.1, mem_univ _, hv.2⟩
    have hfib : ∀ v ∈ edge i,
        #(((univ : Finset ι).filter fun j => v ∈ edge j).erase i) = k - 1 := by
      intro v hv
      have hmem : i ∈ (univ : Finset ι).filter fun j => v ∈ edge j :=
        mem_filter.mpr ⟨mem_univ _, hv⟩
      rw [Finset.card_erase_of_mem hmem, hreg v]
    calc #(sharesVertex edge i)
        ≤ ∑ v ∈ edge i, #(((univ : Finset ι).filter fun j => v ∈ edge j).erase i) :=
          le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
      _ = ∑ _v ∈ edge i, (k - 1) := Finset.sum_congr rfl hfib
      _ = k * (k - 1) := by rw [Finset.sum_const, hcard i, smul_eq_mul]
  -- the numeric condition
  have hkR : (9 : ℝ) ≤ k := by exact_mod_cast hk
  have hcast : ((k * (k - 1) : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
    have h1 : (1 : ℕ) ≤ k := by omega
    push_cast [h1]
    ring
  have hep : Real.exp 1 * (((k * (k - 1) : ℕ) : ℝ) + 1) * (2 / 2 ^ k) ≤ 1 := by
    rw [hcast]
    have hnum := two_exp_mul_le_two_pow hk
    rw [div_eq_mul_inv, ← mul_assoc, mul_comm (Real.exp 1 * ((k : ℝ) * ((k : ℝ) - 1) + 1)) 2,
      ← mul_assoc]
    rw [mul_inv_le_iff₀ (by positivity), one_mul]
    calc 2 * Real.exp 1 * ((k : ℝ) * ((k : ℝ) - 1) + 1) ≤ 2 ^ k := hnum
      _ = 2 ^ k := rfl
  exact exists_two_coloring_of_local_lemma edge (by omega) (by
    have : 0 < k * (k - 1) := by
      refine Nat.mul_pos (by omega) (by omega)
    exact this) hcard hdeg hep


end Coloring

end PMC
