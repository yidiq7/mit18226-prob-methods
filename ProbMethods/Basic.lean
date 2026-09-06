/-
Formalization of Yufei Zhao, *Probabilistic Methods in Combinatorics*
(MIT 18.226 lecture notes).
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Shared definitions

Every project-specific definition that appears in a theorem *statement* lives in this
file. Chapter files contain statements and proofs only; they never introduce a
definition their own statement mentions. This keeps the statement layer in one place,
where `statement-immutability` can guard it.

## Main definitions

* `PMC.crossing`, `PMC.cutEdges` — the edges of a graph cut by a two-colouring
  (§1.0, large bipartite subgraph).
* `PMC.TwoColorable` — property B for a family of sets (§1.3).
* `PMC.RamseyProp` — the defining property of the Ramsey number `R(k, l)` (§1.1).
* `PMC.CompleteBipartiteChoosable` — `k`-choosability of `K_{n,n}` (§1.4).
-/

open Finset

namespace PMC

/-! ### Cuts of a graph -/

section Cut
variable {V : Type*}

/-- `crossing c e` is `true` when the two endpoints of the edge `e` receive different
colours under `c`. -/
def crossing (c : V → Bool) : Sym2 V → Bool :=
  Sym2.lift ⟨fun a b => c a != c b, by
    intro a b; show (c a != c b) = (c b != c a); cases c a <;> cases c b <;> rfl⟩

@[simp] lemma crossing_mk (c : V → Bool) (a b : V) : crossing c s(a, b) = (c a != c b) := rfl

variable [Fintype V] [DecidableEq V]

/-- The edges of `G` crossing the cut induced by the two-colouring `c`. These are exactly
the edges of the bipartite subgraph of `G` obtained by keeping only bichromatic edges. -/
def cutEdges (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) : Finset (Sym2 V) :=
  {e ∈ G.edgeFinset | crossing c e}

omit [DecidableEq V] in
@[simp] lemma mem_cutEdges {G : SimpleGraph V} [DecidableRel G.Adj] {c : V → Bool} {a b : V} :
    s(a, b) ∈ cutEdges G c ↔ G.Adj a b ∧ c a ≠ c b := by
  simp [cutEdges]

omit [DecidableEq V] in
lemma cutEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    cutEdges G c ⊆ G.edgeFinset := filter_subset _ _

end Cut

/-! ### Property B -/

/-- A family of sets is *2-colourable* (has *property B*) when the ground set admits a
two-colouring under which no member of the family is monochromatic. -/
def TwoColorable {α : Type*} (E : Finset (Finset α)) : Prop :=
  ∃ c : α → Bool, ∀ e ∈ E, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

/-! ### Ramsey numbers -/

/-- `RamseyProp n k l` says that every red/blue colouring of the edges of `Kₙ` contains a
red `K_k` or a blue `K_l`.

A colouring is encoded as a simple graph `G` on `Fin n`: red edges are the edges of `G`,
blue edges are the edges of `Gᶜ`. So a red `K_k` is a `k`-clique of `G`, and a blue `K_l`
is a `l`-clique of `Gᶜ`. The Ramsey number `R(k, l)` is the least `n` with `RamseyProp n k l`;
the lower-bound theorems of §1.1 are stated as `¬ RamseyProp n k l`, which is exactly
`R(k, l) > n` given that `RamseyProp · k l` is upward closed (`RamseyProp.mono`). -/
def RamseyProp (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree k ∨ ¬ Gᶜ.CliqueFree l

lemma not_ramseyProp_iff {n k l : ℕ} :
    ¬ RamseyProp n k l ↔ ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree l := by
  simp [RamseyProp, not_forall, not_or]

/-! ### List colourings of `K_{n,n}` -/

/-- `K_{n,n}` is `k`-choosable: for every assignment of colour lists of size `k` to the
`2n` vertices there is a proper colouring picking each vertex's colour from its own list.

Vertices are `Fin n ⊕ Fin n`, with the two summands the two sides. In `K_{n,n}` two
vertices are adjacent exactly when they lie on opposite sides, so a colouring is proper
precisely when no colour appears on both sides.

Colours are taken in `ℕ`. This is no loss of generality: only finitely many colours occur
in the lists, so any colour set can be transported along an injection into `ℕ`. -/
def CompleteBipartiteChoosable (n k : ℕ) : Prop :=
  ∀ L : Fin n ⊕ Fin n → Finset ℕ, (∀ v, #(L v) = k) →
    ∃ f : Fin n ⊕ Fin n → ℕ, (∀ v, f v ∈ L v) ∧ ∀ i j, f (Sum.inl i) ≠ f (Sum.inr j)

end PMC
