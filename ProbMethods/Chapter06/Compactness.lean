import ProbMethods.Chapter06.Coloring
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact

/-!
# §6.2 — the compactness argument (Theorem 6.2.6)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 6.2.6 and the remark after it: the
local lemma applies to finite systems, but a colouring of an **infinite** hypergraph can be
obtained from colourings of all its finite pieces by compactness.

`PMC.exists_two_coloring_of_finite` is that step, in the generality the notes' remark states
it: for a family of finite edges on an arbitrary vertex set, if every *finite* set of vertices
carries a colouring with no edge inside it monochromatic, then some colouring of the whole
vertex set has no edge monochromatic at all.

    (∀ X : Finset V, ∃ c, ∀ i, edge i ⊆ X → edge i is bichromatic under c)
      → ∃ c, ∀ i, edge i is bichromatic under c

Combined with §6.2's finite results — `PMC.exists_two_coloring_of_local_lemma'` for the
`e (d+1) 2^{1-k} ≤ 1` regime, `PMC.exists_two_coloring_of_weight_sum` for the non-uniform one —
this gives Theorem 6.2.6 and is the mechanism behind Theorems 6.2.10 and 6.2.11, whose systems
live on `ℤ`.

## How the compactness goes

`V → Bool` is compact (Tychonoff: `Bool` is compact and a product of compacts is compact), and
for each finite `X` the good colourings form a **closed** set: the condition "edge `i` is
bichromatic" is the finite union over pairs `u, v ∈ edge i` of `{c | c u ≠ c v}`, each of which
is the preimage of a set in a discrete space under a continuous evaluation. The family is
directed downwards — a colouring good on `X ∪ Y` is good on both — and every member is
nonempty by hypothesis, so the intersection over all finite `X` is nonempty. Any member of it
is a global colouring, since every edge is finite and so lies inside some `X`: its own vertex
set.

What is *not* imported from the finite case is any bound on the number of edges: `ι` may be
arbitrary. That is the point of the compactness step — the local lemma's hypotheses are local,
and only the finite conclusions have to be assembled.
-/

open Finset

namespace PMC

section Compactness

variable {V : Type*} [DecidableEq V] {ι : Type*}

/-- Edge `i` is bichromatic under `c`: it has two vertices of different colours. -/
def Bichromatic (edge : ι → Finset V) (c : V → Bool) (i : ι) : Prop :=
  ∃ u ∈ edge i, ∃ v ∈ edge i, c u ≠ c v

/-- The colourings that are good on every edge lying inside `X`. -/
def goodOn (edge : ι → Finset V) (X : Finset V) : Set (V → Bool) :=
  {c | ∀ i, edge i ⊆ X → Bichromatic edge c i}

lemma isClosed_ne_at (u v : V) : IsClosed {c : V → Bool | c u ≠ c v} := by
  have hcont : Continuous fun c : V → Bool => (c u, c v) :=
    (continuous_apply u).prodMk (continuous_apply v)
  have hset : {c : V → Bool | c u ≠ c v}
      = (fun c : V → Bool => (c u, c v)) ⁻¹' {p : Bool × Bool | p.1 ≠ p.2} := rfl
  rw [hset]
  exact (isClosed_discrete _).preimage hcont

lemma isClosed_bichromatic (edge : ι → Finset V) (i : ι) :
    IsClosed {c : V → Bool | Bichromatic edge c i} := by
  have hset : {c : V → Bool | Bichromatic edge c i}
      = ⋃ u ∈ (edge i : Set V), ⋃ v ∈ (edge i : Set V), {c : V → Bool | c u ≠ c v} := by
    ext c
    simp only [Set.mem_iUnion, Bichromatic, exists_prop, mem_coe]
    exact Iff.rfl
  rw [hset]
  refine (edge i).finite_toSet.isClosed_biUnion fun u _ => ?_
  exact (edge i).finite_toSet.isClosed_biUnion fun v _ => isClosed_ne_at u v

lemma isClosed_goodOn (edge : ι → Finset V) (X : Finset V) : IsClosed (goodOn edge X) := by
  have hset : goodOn edge X
      = ⋂ i : ι, {c : V → Bool | edge i ⊆ X → Bichromatic edge c i} := by
    ext c
    simp [goodOn, Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter fun i => ?_
  by_cases hi : edge i ⊆ X
  · have : {c : V → Bool | edge i ⊆ X → Bichromatic edge c i}
        = {c : V → Bool | Bichromatic edge c i} := by
      ext c
      simp [hi]
    rw [this]
    exact isClosed_bichromatic edge i
  · have : {c : V → Bool | edge i ⊆ X → Bichromatic edge c i} = Set.univ := by
      ext c
      simp [hi]
    rw [this]
    exact isClosed_univ

/-- **The compactness step of Theorem 6.2.6.** If every finite set of vertices carries a
colouring good on the edges inside it, some colouring is good on every edge.

`ι` and `V` are arbitrary: the finite conclusions are all that is assembled. -/
theorem exists_two_coloring_of_finite (edge : ι → Finset V)
    (hfin : ∀ X : Finset V, ∃ c : V → Bool, ∀ i, edge i ⊆ X → Bichromatic edge c i) :
    ∃ c : V → Bool, ∀ i, Bichromatic edge c i := by
  classical
  -- the good sets are nonempty, closed, compact, and directed downwards
  have hne : ∀ X : Finset V, (goodOn edge X).Nonempty := by
    intro X
    obtain ⟨c, hc⟩ := hfin X
    exact ⟨c, hc⟩
  have hclosed : ∀ X : Finset V, IsClosed (goodOn edge X) := isClosed_goodOn edge
  have hcompact : ∀ X : Finset V, IsCompact (goodOn edge X) := fun X =>
    (hclosed X).isCompact
  have hdir : Directed (· ⊇ ·) (goodOn edge) := by
    intro X Y
    refine ⟨X ∪ Y, ?_, ?_⟩
    · intro c hc i hi
      exact hc i (hi.trans Finset.subset_union_left)
    · intro c hc i hi
      exact hc i (hi.trans Finset.subset_union_right)
  obtain ⟨c, hc⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ hdir hne hcompact hclosed
  refine ⟨c, fun i => ?_⟩
  have := Set.mem_iInter.mp hc (edge i)
  exact this i Finset.Subset.rfl


/-! ### What remains of Theorem 6.2.6

The compactness step above is the general half. Getting Theorem 6.2.6 exactly as stated needs
the *finite* half transported into it, and that transport is bookkeeping rather than
mathematics — recorded here so it is visible, and published as a task:

* the vertex type of `PMC.exists_two_coloring_of_local_lemma'` is a `Fintype`, so for a finite
  `X` one applies it on `↥X`, carrying each edge inside `X` across with `Finset.subtype` (which
  preserves cardinality, hence the `k ≤ #(edge i)` hypothesis);
* its index type is a `Fintype` too, so `{i // edge i ⊆ X}` has to be finite. It is, and the
  degree hypothesis is what makes it so: at most `d + 1` indices can carry any one edge (two
  indices with the same edge intersect, since edges are nonempty), and there are at most
  `2^{#X}` edges inside `X`;
* the neighbourhood of an index within the sub-family is contained in its neighbourhood in the
  whole family, so the degree bound `d` survives restriction;
* finally a colouring is returned as a `Finset V` of "black" vertices, and
  `c := fun v => decide (v ∈ S)` is bichromatic on an edge exactly when the edge is neither
  inside `S` nor disjoint from it — which is what `PMC.exists_two_coloring_of_local_lemma'`
  provides.

The same transport turns `PMC.exists_two_coloring_of_weight_sum` (Theorem 6.2.4) into its
infinite form, and it is the mechanism Theorems 6.2.10 and 6.2.11 use on `ℤ`. -/


/-- **Theorem 6.2.6** (Zhao): a hypergraph on a possibly infinite vertex set, whose edges are
finite with at least `k` vertices and meet at most `d` others, is 2-colourable once
`e (d+1) 2^{1-k} ≤ 1`.

The compactness half is `PMC.exists_two_coloring_of_finite`; what this statement needs in
addition is the transport of `PMC.exists_two_coloring_of_local_lemma'` onto each finite vertex
set, whose route is recorded above. -/
theorem exists_two_coloring_infinite (edge : ι → Finset V) {k d : ℕ}
    (hk : 1 ≤ k) (hd : 0 < d) (hcard : ∀ i, k ≤ #(edge i))
    (hdeg : ∀ i, ∃ N : Finset ι, #N ≤ d ∧
      ∀ j, j ≠ i → (edge i ∩ edge j).Nonempty → j ∈ N)
    (hep : Real.exp 1 * ((d : ℝ) + 1) * (2 / 2 ^ k) ≤ 1) :
    ∃ c : V → Bool, ∀ i, Bichromatic edge c i := by
  sorry

end Compactness

end PMC
