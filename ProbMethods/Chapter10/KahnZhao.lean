import ProbMethods.Chapter10.Shearer
import ProbMethods.Chapter10.OrderChain
import ProbMethods.Chapter10.Swapping

/-!
# §10.4 — Kahn–Zhao: independent sets in a `d`-regular graph (Theorem 10.4.12)

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 10.4.12: an `n`-vertex `d`-regular
graph has at most `i(K_{d,d})^{n/(2d)} = (2^{d+1} - 1)^{n/(2d)}` independent sets.

The fractional exponent is an artifact of taking logarithms; cleared of it, the theorem is a
statement about natural numbers with no roots in it,

    i(G)^(2d) ≤ (2^{d+1} - 1)^n,

and that is how it is stated here (`PMC.card_indepSets_pow_le`).

## The two halves

*Bipartite case* (Kahn), `PMC.card_indepR_pow_le_of_bipartite`: with `V = A ∪ B` and `X` the
indicator tuple of a uniformly random independent set,

    d·log i(G) = d·H(X_A) + d·H(X_B | X_A)
               ≤ ∑_{b ∈ B} H(X_{N(b)}) + d·∑_{b ∈ B} H(X_b | X_{N(b)})
               ≤ #B · log (2^{d+1} - 1),

using Shearer on the side `A` covered by the neighbourhoods `N(b)` (`PMC.shearer_subset`),
block subadditivity plus "conditioning on more reduces entropy" on the side `B`
(`PMC.tupleEntropy_union_le`), and one inequality per `b ∈ B`.

*Reduction* (Zhao), `PMC.card_indepSets_pow_le`: the bipartite double cover is bipartite and
`d`-regular, `i(G)² ≤ i(G × K₂)` is the swapping trick (`PMC.card_indepSets_sq_le_card_indepCover`),
and the two combine to the general case.

## The per-vertex step

The notes finish each `b ∈ B` with `d` conditionally independent copies of `X_b`, reading

    H(X_{N(b)}) + d·H(X_b | X_{N(b)}) = H(X_b^{(1)}, …, X_b^{(d)}, X_{N(b)}) ≤ log i(K_{d,d}).

The route taken here is the same inequality with the copies replaced by an entropy
maximisation, which is shorter and is where `2^{d+1} - 1` actually comes from:

* `X_b` is determined unless `X_{N(b)}` is all-`false`, so
  `H(X_b | X_{N(b)}) ≤ P(X_{N(b)} = 0)·log 2`;
* `H(X_{N(b)}) + d·log 2·P(X_{N(b)} = 0) ≤ log (2^d + (2^d - 1))` by the Gibbs variational
  principle (`PMC.wentropy_add_wmean_le_log_sum_exp`) applied to the energy that gives the
  all-`false` mask weight `2^d` and each of the other `2^d - 1` masks weight `1`.

The maximum `2^{d+1} - 1` is `i(K_{d,d})`, as it must be: the extremal distribution *is* the
uniform independent set of `K_{d,d}`.
-/

open Finset

namespace PMC

section KahnZhao

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The independent sets of a relation. `PMC.indepSets` is the `SimpleGraph` version; a
relation is what both of the graphs in this argument (`G` and its double cover) come as. -/
def indepR (r : V → V → Prop) [DecidableRel r] : Finset (Finset V) :=
  (univ : Finset (Finset V)).filter fun S => ∀ u ∈ S, ∀ v ∈ S, ¬ r u v

lemma mem_indepR {r : V → V → Prop} [DecidableRel r] {S : Finset V} :
    S ∈ indepR r ↔ ∀ u ∈ S, ∀ v ∈ S, ¬ r u v := by
  rw [indepR, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

lemma empty_mem_indepR (r : V → V → Prop) [DecidableRel r] : (∅ : Finset V) ∈ indepR r :=
  mem_indepR.mpr fun _ hu => absurd hu (Finset.notMem_empty _)

lemma card_indepR_pos (r : V → V → Prop) [DecidableRel r] : 0 < #(indepR r) :=
  card_pos.mpr ⟨∅, empty_mem_indepR r⟩

/-- The neighbourhood of `v`. -/
def nbrs (r : V → V → Prop) [DecidableRel r] (v : V) : Finset V :=
  (univ : Finset V).filter fun u => r v u

@[simp] lemma mem_nbrs {r : V → V → Prop} [DecidableRel r] {v u : V} :
    u ∈ nbrs r v ↔ r v u := by simp [nbrs]

/-- The probability space of the argument: the independent sets, to be taken uniformly. -/
abbrev IndepSpace (r : V → V → Prop) [DecidableRel r] := {S : Finset V // S ∈ indepR r}

/-- The uniform weight on independent sets. -/
noncomputable def indepWeight (r : V → V → Prop) [DecidableRel r] : IndepSpace r → ℝ :=
  fun _ => (1 : ℝ) / Fintype.card (IndepSpace r)

/-- The indicator tuple of the random independent set. -/
def indepInd (r : V → V → Prop) [DecidableRel r] (v : V) (S : IndepSpace r) : Bool :=
  decide (v ∈ S.1)


/-! ### The masks of a sub-tuple

`X_S` takes values in `V → Option Bool`, of which only the `2^{#S}` masks supported on `S`
are attainable. Both the entropy maximisation and the "`X_b` is determined" step need to
name those, and to single out the all-`false` one. -/

section Masks

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The all-`false` mask on `S`: the value of `X_S` at an independent set missing `S`. -/
def falseMask (S : Finset V) : V → Option Bool := fun v => if v ∈ S then some false else none

/-- The masks supported on `S` — the possible values of `X_S`. -/
def maskSet (S : Finset V) : Finset (V → Option Bool) :=
  Fintype.piFinset fun v => if v ∈ S then {some true, some false} else {none}

lemma masked_mem_maskSet (X : V → Ω → Bool) (S : Finset V) (ω : Ω) :
    masked X S ω ∈ maskSet S := by
  refine Fintype.mem_piFinset.mpr fun v => ?_
  by_cases h : v ∈ S
  · simp only [maskSet, masked, if_pos h]
    cases X v ω <;> simp
  · simp [masked, h]

lemma falseMask_mem_maskSet (S : Finset V) : falseMask S ∈ maskSet (V := V) S := by
  refine Fintype.mem_piFinset.mpr fun v => ?_
  by_cases h : v ∈ S <;> simp [falseMask, h]

lemma card_maskSet (S : Finset V) : #(maskSet (V := V) S) = 2 ^ #S := by
  rw [maskSet, Fintype.card_piFinset]
  have hterm : ∀ v : V, #(if v ∈ S then ({some true, some false} : Finset (Option Bool))
      else {none}) = if v ∈ S then 2 else 1 := by
    intro v
    by_cases h : v ∈ S <;> simp [h]
  rw [Finset.prod_congr rfl fun v _ => hterm v, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const]

/-- A mask differs from the all-`false` one exactly by having a `true` somewhere on `S`. -/
lemma exists_true_of_ne_falseMask {X : V → Ω → Bool} {S : Finset V} {ω : Ω}
    (h : masked X S ω ≠ falseMask S) : ∃ v ∈ S, X v ω = true := by
  obtain ⟨v, hv⟩ := Function.ne_iff.mp h
  by_cases hvS : v ∈ S
  · refine ⟨v, hvS, ?_⟩
    simp only [masked, falseMask, if_pos hvS, ne_eq, Option.some.injEq] at hv
    revert hv
    cases X v ω <;> simp
  · exact absurd (by simp [masked, falseMask, hvS]) hv

end Masks

variable (r : V → V → Prop) [DecidableRel r]

lemma card_indepSpace : Fintype.card (IndepSpace r) = #(indepR r) := Fintype.card_coe _

@[simp] lemma indepWeight_apply (S : IndepSpace r) :
    indepWeight r S = (1 : ℝ) / Fintype.card (IndepSpace r) := rfl

lemma indepWeight_eq :
    indepWeight r = fun _ : IndepSpace r => (1 : ℝ) / Fintype.card (IndepSpace r) := rfl

lemma card_indepSpace_pos : 0 < Fintype.card (IndepSpace r) := by
  rw [card_indepSpace]
  exact card_indepR_pos r

lemma indepWeight_nonneg : ∀ S : IndepSpace r, 0 ≤ indepWeight r S := by
  intro S
  rw [indepWeight_apply]
  positivity

lemma sum_indepWeight : ∑ S : IndepSpace r, indepWeight r S = 1 := by
  have h : (0 : ℝ) < Fintype.card (IndepSpace r) := by
    exact_mod_cast card_indepSpace_pos r
  rw [indepWeight_eq, Finset.sum_const, card_univ, nsmul_eq_mul, mul_one_div, div_self (ne_of_gt h)]


/-- **`X_b` is determined unless no neighbour of `b` was chosen.**
`H(X_b | X_{N(b)}) ≤ P(X_{N(b)} = 0) · log 2`. -/
lemma wcondEntropy_indepInd_le (b : V) :
    wcondEntropy (indepWeight r) (masked (indepInd r) (nbrs r b)) (indepInd r b)
      ≤ Real.log 2 * wdist (indepWeight r) (masked (indepInd r) (nbrs r b))
          (falseMask (nbrs r b)) := by
  classical
  have hT : ∀ ω : IndepSpace r, indepInd r b ω ∈
      (if masked (indepInd r) (nbrs r b) ω = falseMask (nbrs r b) then (univ : Finset Bool)
        else {false}) := by
    intro ω
    by_cases h : masked (indepInd r) (nbrs r b) ω = falseMask (nbrs r b)
    · rw [if_pos h]
      exact mem_univ _
    · rw [if_neg h, mem_singleton]
      obtain ⟨v, hvS, hv⟩ := exists_true_of_ne_falseMask h
      have hvmem : v ∈ ω.1 := of_decide_eq_true hv
      have hbnot : b ∉ ω.1 := by
        intro hb
        exact mem_indepR.mp ω.2 b hb v hvmem (mem_nbrs.mp hvS)
      exact decide_eq_false hbnot
  have hle := wcondEntropy_le_sum_log_card (indepWeight_nonneg r)
    (masked (indepInd r) (nbrs r b)) (indepInd r b)
    (fun u => if u = falseMask (nbrs r b) then (univ : Finset Bool) else {false}) hT
  have hterm : ∀ u : V → Option Bool,
      wdist (indepWeight r) (masked (indepInd r) (nbrs r b)) u
          * Real.log #(if u = falseMask (nbrs r b) then (univ : Finset Bool) else {false})
        = if u = falseMask (nbrs r b) then
            Real.log 2 * wdist (indepWeight r) (masked (indepInd r) (nbrs r b)) u else 0 := by
    intro u
    by_cases h : u = falseMask (nbrs r b)
    · rw [if_pos h, if_pos h, card_univ, Fintype.card_bool, Nat.cast_ofNat, mul_comm]
    · rw [if_neg h, if_neg h, Finset.card_singleton, Nat.cast_one, Real.log_one, mul_zero]
  rw [Finset.sum_congr rfl fun u _ => hterm u, Finset.sum_ite_eq' _ (falseMask (nbrs r b)),
    if_pos (mem_univ _)] at hle
  exact hle

/-- **The per-vertex inequality of the bipartite proof:**

    H(X_{N(b)}) + d·H(X_b | X_{N(b)}) ≤ log (2^{d+1} - 1) = log i(K_{d,d}).

The Gibbs variational principle at the energy that rewards the all-`false` mask by `2^d`,
whose partition function is `2^d + (2^d - 1)`. -/
lemma tupleEntropy_nbrs_add_mul_le (b : V) {d : ℕ} (hd : #(nbrs r b) = d) :
    tupleEntropy (indepWeight r) (indepInd r) (nbrs r b)
      + (d : ℝ) * wcondEntropy (indepWeight r) (masked (indepInd r) (nbrs r b))
          (indepInd r b)
      ≤ Real.log (2 ^ (d + 1) - 1) := by
  classical
  set S := nbrs r b with hSdef
  set w := indepWeight r with hwdef
  set X := indepInd r with hXdef
  set a : (V → Option Bool) → ℝ := fun u => if u = falseMask S then (d : ℝ) * Real.log 2 else 0
    with hadef
  have hw := indepWeight_nonneg r
  have hsum := sum_indepWeight r
  -- the partition function is `i(K_{d,d})`
  have h2d : Real.exp ((d : ℝ) * Real.log 2) = 2 ^ d := by
    rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), Real.rpow_natCast]
  have hexp : ∑ t ∈ maskSet S, Real.exp (a t) = 2 ^ (d + 1) - 1 := by
    rw [← Finset.add_sum_erase _ _ (falseMask_mem_maskSet S)]
    simp only [hadef, if_true]
    rw [h2d, Finset.sum_congr rfl (fun t ht => by
      rw [if_neg (Finset.ne_of_mem_erase ht), Real.exp_zero]),
      Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_erase_of_mem (falseMask_mem_maskSet S), card_maskSet, hd]
    have hcast : ((2 ^ d - 1 : ℕ) : ℝ) = 2 ^ d - 1 := by
      have h1 : (1 : ℕ) ≤ 2 ^ d := Nat.one_le_two_pow
      push_cast [Nat.cast_sub h1]
      ring
    rw [hcast]
    ring
  -- the mean of the energy
  have hmean : wmean w (fun ω => a (masked X S ω))
      = wdist w (masked X S) (falseMask S) * ((d : ℝ) * Real.log 2) := by
    rw [wmean_comp_eq_sum_wdist]
    simp only [hadef]
    have hterm : ∀ u : V → Option Bool,
        wdist w (masked X S) u * (if u = falseMask S then (d : ℝ) * Real.log 2 else 0)
          = if u = falseMask S then
              wdist w (masked X S) u * ((d : ℝ) * Real.log 2) else 0 := by
      intro u
      by_cases h : u = falseMask S
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl fun u _ => hterm u, Finset.sum_ite_eq' _ (falseMask S),
      if_pos (mem_univ _)]
  have hgibbs := wentropy_add_wmean_le_log_sum_exp hw hsum (masked X S) a
    (fun ω => masked_mem_maskSet X S ω)
  rw [hexp, hmean] at hgibbs
  have hcond := wcondEntropy_indepInd_le r b
  rw [← hSdef] at hcond
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hmul : (d : ℝ) * wcondEntropy w (masked X S) (X b)
      ≤ (d : ℝ) * (Real.log 2 * wdist w (masked X S) (falseMask S)) :=
    mul_le_mul_of_nonneg_left hcond hdnn
  have hte : tupleEntropy w X S = wentropy w (masked X S) := rfl
  rw [hte]
  nlinarith [hgibbs, hmul]

/-- **The entropy of the indicator tuple is `log i(G)`**: the step that turns entropy back
into a count. The full tuple determines the independent set, so `PMC.wentropy_uniform_of_injective`
applies. -/
lemma tupleEntropy_indepInd_univ :
    tupleEntropy (indepWeight r) (indepInd r) univ = Real.log #(indepR r) := by
  have hinj : Function.Injective (masked (indepInd r) (univ : Finset V)) := by
    intro S T h
    refine Subtype.ext (Finset.ext fun v => ?_)
    have hv := congrFun h v
    simp only [masked, if_pos (mem_univ v), Option.some.injEq, indepInd,
      decide_eq_decide] at hv
    exact hv
  have hval := wentropy_uniform_of_injective hinj (card_indepSpace_pos r)
  rw [show tupleEntropy (indepWeight r) (indepInd r) univ
      = wentropy (indepWeight r) (masked (indepInd r) univ) from rfl, indepWeight_eq, hval,
    card_indepSpace]


/-! ### The entropy skeleton

The three global steps of Kahn's argument — Shearer on one side, the chain rule with block
subadditivity on the other, and dropping the conditioning down to a neighbourhood — use
nothing about independent sets, or even about graphs. They are separated out here because
Galvin–Tetali (Theorem 10.4.14) is the *same* argument with a different per-vertex bound. -/

section Skeleton

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {β : Type*} [Fintype β] [DecidableEq β]

/-- **The entropy skeleton of the bipartite proof.** With `V = A ∪ B`, a neighbourhood map
`nb` sending each `b ∈ B` into `A`, and every vertex of `A` covered `d` times, a per-vertex
bound `H(X_{nb b}) + d·H(X_b | X_{nb b}) ≤ c` gives `d·H(X) ≤ #B·c`.

Reading the three inputs in order: `PMC.shearer_subset` turns `d·H(X_A)` into
`∑_{b ∈ B} H(X_{nb b})` — the covering multiplicity is regularity — `PMC.tupleEntropy_union_le`
turns `H(X)` into `H(X_A) + ∑_{b ∈ B} H(X_b | X_A)`, and `PMC.wcondEntropy_masked_antitone`
replaces `X_A` by `X_{nb b}` in each of those terms. -/
theorem mul_tupleEntropy_univ_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (X : V → Ω → β) (nb : V → Finset V) {A B : Finset V} (hdisj : Disjoint A B)
    (hcover : A ∪ B = univ) (hAS : ∀ b ∈ B, nb b ⊆ A) (d : ℕ)
    (hcov : ∀ a ∈ A, d ≤ #(B.filter fun b => a ∈ nb b)) {c : ℝ}
    (hper : ∀ b ∈ B, tupleEntropy w X (nb b)
      + (d : ℝ) * wcondEntropy w (masked X (nb b)) (X b) ≤ c) :
    (d : ℝ) * tupleEntropy w X univ ≤ (#B : ℝ) * c := by
  classical
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hshearer := shearer_subset hw hsum X A B nb d hAS hcov
  have hchain : tupleEntropy w X univ
      ≤ tupleEntropy w X A + ∑ b ∈ B, wcondEntropy w (masked X A) (X b) := by
    rw [← hcover]
    exact tupleEntropy_union_le hw hsum X A B hdisj
  have hdrop : ∀ b ∈ B, wcondEntropy w (masked X A) (X b)
      ≤ wcondEntropy w (masked X (nb b)) (X b) :=
    fun b hb => wcondEntropy_masked_antitone hw hsum X (hAS b hb)
      fun h => (Finset.disjoint_left.mp hdisj h) hb
  have h4 : (d : ℝ) * tupleEntropy w X univ
      ≤ (d : ℝ) * tupleEntropy w X A
        + (d : ℝ) * ∑ b ∈ B, wcondEntropy w (masked X A) (X b) := by
    have h := mul_le_mul_of_nonneg_left hchain hdnn
    rw [mul_add] at h
    exact h
  have h5 : (d : ℝ) * ∑ b ∈ B, wcondEntropy w (masked X A) (X b)
      ≤ ∑ b ∈ B, (d : ℝ) * wcondEntropy w (masked X (nb b)) (X b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (hdrop b hb) hdnn
  have h6 := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h6
  linarith

end Skeleton

/-- **Theorem 10.4.12, the bipartite case** (Kahn). For a `d`-regular graph with
bipartition `V = A ∪ B`,

    i(G)^d ≤ (2^{d+1} - 1)^{#B} = i(K_{d,d})^{#B}.

For a `d`-regular bipartite graph `#A = #B = n/2`, so this is the `i(G) ≤ i(K_{d,d})^{n/(2d)}`
of the notes with the root cleared.

The three inputs are Shearer on the `A` side (`PMC.shearer_subset`, where the covering
multiplicity `d` is exactly regularity), the chain rule with block subadditivity on the `B`
side (`PMC.tupleEntropy_union_le`), and the per-vertex maximisation
(`PMC.tupleEntropy_nbrs_add_mul_le`). -/
theorem card_indepR_pow_le_of_bipartite (hsymm : ∀ u v, r u v → r v u)
    {A B : Finset V} (hdisj : Disjoint A B) (hcover : A ∪ B = univ)
    (hbip : ∀ u v, r u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    {d : ℕ} (hreg : ∀ v, #(nbrs r v) = d) :
    #(indepR r) ^ d ≤ (2 ^ (d + 1) - 1) ^ #B := by
  classical
  have hw := indepWeight_nonneg r
  have hsum := sum_indepWeight r
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  -- the neighbourhood of a vertex of `B` lies in `A`
  have hAS : ∀ b ∈ B, nbrs r b ⊆ A := by
    intro b hb v hv
    rcases hbip b v (mem_nbrs.mp hv) with ⟨hbA, -⟩ | ⟨-, hvA⟩
    · exact absurd hb (Finset.disjoint_left.mp hdisj hbA)
    · exact hvA
  -- and each vertex of `A` lies in `d` of those neighbourhoods: its own neighbours
  have hcov : ∀ a ∈ A, d ≤ #(B.filter fun b => a ∈ nbrs r b) := by
    intro a ha
    rw [← hreg a]
    refine Finset.card_le_card fun v hv => ?_
    rw [mem_filter]
    refine ⟨?_, mem_nbrs.mpr (hsymm a v (mem_nbrs.mp hv))⟩
    rcases hbip a v (mem_nbrs.mp hv) with ⟨-, hvB⟩ | ⟨haB, -⟩
    · exact hvB
    · exact absurd haB (Finset.disjoint_left.mp hdisj ha)
  have hlog := tupleEntropy_indepInd_univ r
  -- the entropy inequality
  have hkey : (d : ℝ) * Real.log #(indepR r) ≤ (#B : ℝ) * Real.log (2 ^ (d + 1) - 1) := by
    have hskel := mul_tupleEntropy_univ_le hw hsum (indepInd r) (nbrs r) hdisj hcover hAS d
      hcov (fun b _ => tupleEntropy_nbrs_add_mul_le r b (hreg b))
    have hlogd : (d : ℝ) * tupleEntropy (indepWeight r) (indepInd r) univ
        = (d : ℝ) * Real.log #(indepR r) := by rw [hlog]
    linarith
  -- and back to a statement about natural numbers
  have hNpos : 0 < #(indepR r) := card_indepR_pos r
  have hMpos : 0 < 2 ^ (d + 1) - 1 := by
    have h : 1 < 2 ^ (d + 1) := Nat.one_lt_two_pow (by omega)
    omega
  have hcastM : ((2 ^ (d + 1) - 1 : ℕ) : ℝ) = 2 ^ (d + 1) - 1 := by
    have h1 : (1 : ℕ) ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
    push_cast [Nat.cast_sub h1]
    ring
  have hp1 : (0 : ℝ) < ((#(indepR r) ^ d : ℕ) : ℝ) := by exact_mod_cast pow_pos hNpos d
  have hp2 : (0 : ℝ) < (((2 ^ (d + 1) - 1) ^ #B : ℕ) : ℝ) := by
    exact_mod_cast pow_pos hMpos #B
  have hlogs : Real.log ((#(indepR r) ^ d : ℕ) : ℝ)
      ≤ Real.log (((2 ^ (d + 1) - 1) ^ #B : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow, hcastM]
    exact hkey
  have hexp := Real.exp_le_exp.mpr hlogs
  rw [Real.exp_log hp1, Real.exp_log hp2] at hexp
  exact_mod_cast hexp


end KahnZhao

section DoubleCover

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma indepR_adj_eq : indepR G.Adj = indepSets G :=
  Finset.ext fun _ => by rw [mem_indepR, mem_indepSets]

lemma indepR_coverAdj_eq : indepR (coverAdj G) = indepCover G :=
  Finset.ext fun _ => by rw [mem_indepR, mem_indepCover]

/-- The two sides of the bipartite double cover. -/
lemma nbrs_coverAdj (p : V × Bool) :
    nbrs (coverAdj G) p = (G.neighborFinset p.1).image fun v => (v, !p.2) := by
  ext q
  simp only [mem_nbrs, coverAdj, Finset.mem_image, SimpleGraph.mem_neighborFinset]
  constructor
  · intro ⟨hadj, hne⟩
    refine ⟨q.1, hadj, ?_⟩
    rw [Prod.ext_iff]
    refine ⟨rfl, ?_⟩
    revert hne
    cases p.2 <;> cases q.2 <;> simp
  · intro ⟨v, hv, hq⟩
    subst hq
    refine ⟨hv, ?_⟩
    cases p.2 <;> simp

lemma card_nbrs_coverAdj (p : V × Bool) :
    #(nbrs (coverAdj G) p) = G.degree p.1 := by
  rw [nbrs_coverAdj, Finset.card_image_of_injective _ (fun v v' h => (Prod.ext_iff.mp h).1),
    SimpleGraph.card_neighborFinset_eq_degree]

/-- **Theorem 10.4.12** (Kahn, Zhao). An `n`-vertex `d`-regular graph has at most
`i(K_{d,d})^{n/(2d)}` independent sets — stated free of roots as

    i(G)^(2d) ≤ (2^{d+1} - 1)^n.

Zhao's reduction: the bipartite double cover is bipartite and `d`-regular, so Kahn's case
applies to it, and the swapping trick `i(G)² ≤ i(G × K₂)`
(`PMC.card_indepSets_sq_le_card_indepCover`) transfers the bound back. -/
theorem card_indepSets_pow_le {d : ℕ} (hreg : ∀ v, G.degree v = d) :
    #(indepSets G) ^ (2 * d) ≤ (2 ^ (d + 1) - 1) ^ Fintype.card V := by
  classical
  set A : Finset (V × Bool) := (univ : Finset (V × Bool)).filter fun p => p.2 = false with hA
  set B : Finset (V × Bool) := (univ : Finset (V × Bool)).filter fun p => p.2 = true with hB
  have hmemA : ∀ p : V × Bool, p ∈ A ↔ p.2 = false := by
    intro p; rw [hA, mem_filter]; exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  have hmemB : ∀ p : V × Bool, p ∈ B ↔ p.2 = true := by
    intro p; rw [hB, mem_filter]; exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  have hcardB : #B = Fintype.card V := by
    have hBimg : B = (univ : Finset V).image fun v => (v, true) := by
      ext p
      rw [hmemB, Finset.mem_image]
      constructor
      · intro h
        exact ⟨p.1, mem_univ _, by simp [Prod.ext_iff, h]⟩
      · rintro ⟨v, -, hv⟩
        rw [← hv]
    rw [hBimg, Finset.card_image_of_injective _ (fun v v' h => (Prod.ext_iff.mp h).1),
      card_univ]
  -- Kahn's bound on the cover
  have hcover := card_indepR_pow_le_of_bipartite (coverAdj G)
    (fun p q h => ⟨h.1.symm, fun hpq => h.2 hpq.symm⟩)
    (A := A) (B := B)
    (Finset.disjoint_left.mpr fun p hpA hpB => by
      rw [hmemA] at hpA
      rw [hmemB] at hpB
      rw [hpA] at hpB
      exact Bool.false_ne_true hpB)
    (by
      ext p
      simp only [mem_union, mem_univ, iff_true, hmemA, hmemB]
      cases p.2 <;> simp)
    (by
      intro p q h
      have hne : p.2 ≠ q.2 := h.2
      revert hne
      cases hp : p.2 <;> cases hq : q.2 <;> intro hne
      · exact absurd rfl hne
      · exact Or.inl ⟨(hmemA p).mpr hp, (hmemB q).mpr hq⟩
      · exact Or.inr ⟨(hmemB p).mpr hp, (hmemA q).mpr hq⟩
      · exact absurd rfl hne)
    (d := d) (fun p => by rw [card_nbrs_coverAdj, hreg])
  rw [indepR_coverAdj_eq, hcardB] at hcover
  -- and the swapping trick
  have hswap := card_indepSets_sq_le_card_indepCover G
  calc #(indepSets G) ^ (2 * d)
      = (#(indepSets G) * #(indepSets G)) ^ d := by
        rw [pow_mul, pow_two]
    _ ≤ #(indepCover G) ^ d := Nat.pow_le_pow_left hswap d
    _ ≤ (2 ^ (d + 1) - 1) ^ Fintype.card V := hcover

end DoubleCover


end PMC
