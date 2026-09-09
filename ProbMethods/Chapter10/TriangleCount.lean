import ProbMethods.Chapter10.LoomisWhitney
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Counting triangles by entropy — a Shearer application

Zhao, *Probabilistic Methods in Combinatorics*, Chapter 10 (§10.4 supplies the tool).

**This particular bound is not a numbered result in the notes.** §10.4's own triangle
content is Theorem 10.4.9, about triangle-*intersecting* families, which is a different
statement and still open here. What follows is the standard Shearer application, included
because it demonstrates that `PMC.card_pow_le_prod_card_projSet` is usable off the shelf:
a graph with `m` edges has few triangles:
writing `t` for the number of *ordered* triangles (so `t = 6 ·` the number of triangles),

`t ^ 2 ≤ (2 m) ^ 3`.

This is `PMC.card_pow_le_prod_card_projSet` at `ι = Fin 3` and `k = 2` — the very same
instance as Loomis–Whitney — with one extra observation: the trace of the ordered triangles
on any two coordinates consists of *ordered edges*, of which there are exactly `2 m`. So
each of the three shadows in the Loomis–Whitney product is at most `2 m`.
-/

open Finset

namespace PMC

section TriangleCount

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordered triangles of `G`, as functions `Fin 3 → V`. -/
def orderedTriangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Fin 3 → V) :=
  univ.filter fun x => ∀ i j, i ≠ j → G.Adj (x i) (x j)

/-- The ordered edges of `G`. -/
def orderedEdges (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V) :=
  univ.filter fun q => G.Adj q.1 q.2

/-- There are exactly `2 m` ordered edges. Fibring over the first endpoint turns the count
into the degree sum, which is `Mathlib`'s handshake lemma. -/
theorem card_orderedEdges (G : SimpleGraph V) [DecidableRel G.Adj] :
    #(orderedEdges G) = 2 * #G.edgeFinset := by
  classical
  rw [← G.sum_degrees_eq_twice_card_edges]
  rw [orderedEdges, Finset.card_eq_sum_card_fiberwise
    (f := fun q : V × V => q.1) (t := (univ : Finset V)) (fun q _ => mem_univ q.1)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_nbij' (fun q => q.2) (fun w => (v, w)) ?_ ?_ ?_ ?_
  · intro q hq
    rw [mem_coe, mem_filter, mem_filter] at hq
    rw [mem_coe, SimpleGraph.mem_neighborFinset]
    exact hq.2 ▸ hq.1.2
  · intro w hw
    rw [mem_coe, SimpleGraph.mem_neighborFinset] at hw
    rw [mem_coe, mem_filter, mem_filter]
    exact ⟨⟨mem_univ _, hw⟩, rfl⟩
  · intro q hq
    rw [mem_coe, mem_filter, mem_filter] at hq
    exact Prod.ext hq.2.symm rfl
  · intro w _
    rfl

/-- **The trace on two coordinates injects into a set of pairs.**

Stated for arbitrary indices `a b` and an arbitrary target `E`, so the triangle application
supplies only the fact that a triangle's `a`-th and `b`-th vertices are adjacent. -/
theorem card_projSet_pair_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty V]
    (a b : ι) (A : Finset (ι → V)) (E : Finset (V × V))
    (hE : ∀ x ∈ A, (x a, x b) ∈ E) :
    #(projSet {a, b} A) ≤ #E := by
  classical
  set v₀ := Classical.arbitrary V with hv₀
  refine Finset.card_le_card_of_injOn
    (fun u => ((u a).getD v₀, (u b).getD v₀)) ?_ ?_
  · intro u hu
    rw [mem_coe, mem_projSet] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    have ha : a ∈ ({a, b} : Finset ι) := by simp
    have hb : b ∈ ({a, b} : Finset ι) := by simp
    simp only [if_pos ha, if_pos hb, Option.getD_some]
    exact hE x hx
  · intro u hu u' hu' heq
    rw [mem_coe, mem_projSet] at hu
    rw [mem_coe, mem_projSet] at hu'
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨x', hx', rfl⟩ := hu'
    have ha : a ∈ ({a, b} : Finset ι) := by simp
    have hb : b ∈ ({a, b} : Finset ι) := by simp
    simp only [if_pos ha, if_pos hb, Option.getD_some, Prod.mk.injEq] at heq
    funext i
    by_cases hi : i ∈ ({a, b} : Finset ι)
    · rw [if_pos hi, if_pos hi]
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · rw [heq.1]
      · rw [Finset.mem_singleton.mp hi', heq.2]
    · rw [if_neg hi, if_neg hi]

/-- **The triangle-counting bound.**

`t ^ 2 ≤ (2 m) ^ 3`, where `t` counts *ordered* triangles and `m = #G.edgeFinset`. Since
`t = 6 ·` (number of triangles), this is the familiar
`#triangles ≤ (2m)^{3/2} / 6`. -/
theorem card_orderedTriangles_sq_le (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    (#(orderedTriangles G) : ℝ) ^ 2 ≤ ((2 * #G.edgeFinset : ℕ) : ℝ) ^ 3 := by
  classical
  rcases (orderedTriangles G).eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.card_empty, Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0)]
    positivity
  -- Shearer at `ι = Fin 3`, `k = 2`: the three 2-subsets cover each coordinate twice
  have hshear := card_pow_le_prod_card_projSet (orderedTriangles G) hne univ
    (fun j : Fin 3 => univ \ {j}) 2 (by
      intro i
      have hf : (univ : Finset (Fin 3)).filter
          (fun j => i ∈ (univ : Finset (Fin 3)) \ {j}) = univ.erase i := by
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_singleton, mem_erase,
          and_true]
        exact ne_comm
      rw [hf, Finset.card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin])
  -- each shadow consists of ordered edges
  have hpair : ∀ j : Fin 3,
      #(projSet ((univ : Finset (Fin 3)) \ {j}) (orderedTriangles G))
        ≤ #(orderedEdges G) := by
    intro j
    obtain ⟨a, b, hab, hset⟩ : ∃ a b : Fin 3, a ≠ b ∧
        (univ : Finset (Fin 3)) \ {j} = {a, b} := by
      fin_cases j
      · exact ⟨1, 2, by decide, by decide⟩
      · exact ⟨0, 2, by decide, by decide⟩
      · exact ⟨0, 1, by decide, by decide⟩
    rw [hset]
    refine card_projSet_pair_le a b _ _ ?_
    intro x hx
    rw [orderedTriangles, mem_filter] at hx
    rw [orderedEdges, mem_filter]
    exact ⟨mem_univ _, hx.2 a b hab⟩
  have hbound : ∏ j : Fin 3,
      (#(projSet ((univ : Finset (Fin 3)) \ {j}) (orderedTriangles G)) : ℝ)
      ≤ ∏ _j : Fin 3, ((2 * #G.edgeFinset : ℕ) : ℝ) := by
    refine Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _) fun j _ => ?_
    rw [← card_orderedEdges G]
    exact_mod_cast hpair j
  calc (#(orderedTriangles G) : ℝ) ^ 2
      ≤ ∏ j : Fin 3,
          (#(projSet ((univ : Finset (Fin 3)) \ {j}) (orderedTriangles G)) : ℝ) := hshear
    _ ≤ ∏ _j : Fin 3, ((2 * #G.edgeFinset : ℕ) : ℝ) := hbound
    _ = ((2 * #G.edgeFinset : ℕ) : ℝ) ^ 3 := by
        rw [Finset.prod_const, card_univ, Fintype.card_fin]

end TriangleCount

end PMC
