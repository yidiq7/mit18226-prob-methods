import ProbMethods.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# §1.0 — Large bipartite subgraphs

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 1.0.1.
-/

open Finset

namespace PMC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Flip the colour of the single vertex `a`, leaving every other vertex alone. -/
private def flipAt (a : V) (c : V → Bool) : V → Bool := Function.update c a (!c a)

omit [Fintype V] in
private lemma flipAt_self (a : V) (c : V → Bool) : flipAt a c a = !c a := by
  simp [flipAt]

omit [Fintype V] in
private lemma flipAt_of_ne {a x : V} (h : x ≠ a) (c : V → Bool) : flipAt a c x = c x := by
  simp [flipAt, h]

omit [Fintype V] in
private lemma flipAt_involutive (a : V) :
    Function.Involutive (flipAt a : (V → Bool) → V → Bool) := by
  intro c
  funext x
  rcases eq_or_ne x a with rfl | hx
  · simp [flipAt_self]
  · simp [flipAt_of_ne hx]

/-- At least half of the two-colourings cut a fixed edge `s(a, b)`: flipping the colour of
`a` sends every colouring leaving the edge monochromatic to one that cuts it, injectively. -/
private lemma card_univ_le_two_mul_card_filter_crossing (a b : V) (hab : a ≠ b) :
    #(univ : Finset (V → Bool)) ≤
      2 * #(univ.filter fun c : V → Bool => crossing c s(a, b)) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (V → Bool))) (p := fun c : V → Bool => crossing c s(a, b) = true)
  have key : #(univ.filter fun c : V → Bool => ¬ (crossing c s(a, b) = true))
      ≤ #(univ.filter fun c : V → Bool => crossing c s(a, b) = true) := by
    refine Finset.card_le_card_of_injOn (flipAt a) ?_ (flipAt_involutive a).injective.injOn
    intro c hc
    rw [Finset.mem_coe, mem_filter] at hc
    rw [Finset.mem_coe, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have hmono : c a = c b := by simpa using hc.2
    have hnot : ∀ x : Bool, ((!x) != x) = true := fun x => by cases x <;> rfl
    simp only [crossing_mk, flipAt_self, flipAt_of_ne hab.symm, hmono, hnot]
  omega

omit [DecidableEq V] in
/-- `cutEdges G c` counted edge by edge. -/
private lemma card_cutEdges_eq (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    #(cutEdges G c) = ∑ e ∈ G.edgeFinset, if crossing c e then 1 else 0 :=
  Finset.card_filter _ _

/-- **Large bipartite subgraph** (Zhao, Theorem 1.0.1).

Every graph with `m` edges has a bipartite subgraph with at least `m / 2` edges.

Stated as a max-cut bound: some two-colouring `c` of the vertices cuts at least half the
edges, i.e. `#G.edgeFinset ≤ 2 * #(cutEdges G c)`. The bichromatic edges of `c` are exactly
the edges of a bipartite subgraph of `G`.

The book's proof colours each vertex black or white independently and uniformly, and notes
that each edge is cut with probability `1 / 2`, so the expected number of cut edges is
`m / 2`; some colouring meets the expectation. -/
theorem exists_cut_two_mul_card_edgeFinset_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ c : V → Bool, #G.edgeFinset ≤ 2 * #(cutEdges G c) := by
  have key : ∑ _c : V → Bool, #G.edgeFinset ≤ ∑ c : V → Bool, 2 * #(cutEdges G c) :=
    calc ∑ _c : V → Bool, #G.edgeFinset
        = ∑ _e ∈ G.edgeFinset, #(univ : Finset (V → Bool)) := by simp [mul_comm]
      _ ≤ ∑ e ∈ G.edgeFinset, 2 * #(univ.filter fun c : V → Bool => crossing c e) := by
          apply Finset.sum_le_sum
          intro e he
          induction e using Sym2.ind with
          | _ a b =>
            have hadj : G.Adj a b := by simpa using he
            exact card_univ_le_two_mul_card_filter_crossing a b hadj.ne
      _ = 2 * ∑ e ∈ G.edgeFinset, #(univ.filter fun c : V → Bool => crossing c e) := by
          rw [Finset.mul_sum]
      _ = 2 * ∑ c : V → Bool, #(cutEdges G c) := by
          congr 1
          simp only [card_cutEdges_eq, Finset.card_filter]
          exact Finset.sum_comm
      _ = ∑ c : V → Bool, 2 * #(cutEdges G c) := by rw [Finset.mul_sum]
  obtain ⟨c, -, hc⟩ := Finset.exists_le_of_sum_le univ_nonempty key
  exact ⟨c, hc⟩

end PMC
