import ProbMethods.Chapter10.Entropy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# §10.3 — Sidorenko's inequality for the three-edge path

Theorem 10.3.3 (Blakey–Roy 1965): Sidorenko's conjecture holds when `F` is a path with three
edges. In explicit finite form, for a graph `G` on `n` vertices with `m` edges,

    hom(P₄, G) · n² ≥ (2m)³,

which is `t(P₄, G) ≥ t(K₂, G)³` after dividing by `n⁴`.

The notes prove it by entropy: build a distribution on walks `x–y–z–w` by taking `xy` a
uniform random edge, then `z` a uniform neighbour of `y` and `w` a uniform neighbour of `z`,
and read off `H = 3H(X,Y) - 2H(X) ≥ 3 log(2m) - 2 log n`.

**Here the same proof is carried out without any conditional-entropy machinery.** Writing the
distribution's entropy out explicitly, the argument is exactly two applications of **Gibbs'
inequality** (`PMC.sum_mul_log_div_le`, §10.1):

* against the uniform distribution on vertices, `∑_v d(v) log d(v) ≥ 2m log(2m/n)` — this is
  the notes' `H(X) ≤ log n` step;
* against the uniform distribution on directed edges, giving AM–GM in the form
  `(1/N) ∑ log a_i ≤ log ((1/N) ∑ a_i)` — this is the step that converts the entropy
  identity into the bound on `hom(P₄, G)`.

Both are the same lemma, which is worth noticing: Gibbs' inequality *is* the entropy
inequality, so a proof that uses only Gibbs is the entropy proof, just written out.
-/

open Finset

namespace PMC

section Sidorenko

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The ordered pairs of adjacent vertices — the directed edges, of which there are `2m`. -/
def dirEdges : Finset (V × V) :=
  (univ : Finset (V × V)).filter fun p => G.Adj p.1 p.2

/-- The homomorphisms from the three-edge path: walks `x–y–z–w`, repetitions allowed. -/
def walk3 : Finset (V × V × V × V) :=
  (univ : Finset (V × V × V × V)).filter fun q =>
    G.Adj q.1 q.2.1 ∧ G.Adj q.2.1 q.2.2.1 ∧ G.Adj q.2.2.1 q.2.2.2

lemma card_dirEdges : #(dirEdges G) = ∑ v, G.degree v := by
  classical
  rw [dirEdges, Finset.card_eq_sum_card_fiberwise
    (f := fun p : V × V => p.1) (t := (univ : Finset V)) (fun p _ => mem_univ p.1)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    rw [mem_filter, mem_filter] at hp
    rw [SimpleGraph.mem_neighborFinset]
    exact hp.2 ▸ hp.1.2
  · intro p hp p' hp' h
    rw [mem_filter] at hp hp'
    exact Prod.ext (hp.2.trans hp'.2.symm) h
  · intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu
    exact ⟨(v, u), by rw [mem_filter, mem_filter]; exact ⟨⟨mem_univ _, hu⟩, rfl⟩, rfl⟩

/-- **The walk count, fibred over the middle edge.** A walk is a middle directed edge `(y,z)`
together with a neighbour of `y` and a neighbour of `z`, so
`hom(P₄, G) = ∑_{(y,z)} d(y) d(z)`. -/
lemma card_walk3 :
    #(walk3 G) = ∑ p ∈ dirEdges G, G.degree p.1 * G.degree p.2 := by
  classical
  have hmaps : ∀ q ∈ walk3 G, (q.2.1, q.2.2.1) ∈ dirEdges G := by
    intro q hq
    rw [walk3, mem_filter] at hq
    rw [dirEdges, mem_filter]
    exact ⟨mem_univ _, hq.2.2.1⟩
  rw [Finset.card_eq_sum_card_fiberwise (fun q hq => hmaps q (by rwa [← mem_coe]))]
  refine Finset.sum_congr rfl fun p hpmem => ?_
  have hp : G.Adj p.1 p.2 := by
    rw [dirEdges, mem_filter] at hpmem
    exact hpmem.2
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ←
    SimpleGraph.card_neighborFinset_eq_degree, ← Finset.card_product]
  refine Finset.card_bij' (fun q _ => (q.1, q.2.2.2)) (fun c _ => (c.1, p.1, p.2, c.2))
    ?_ ?_ ?_ ?_
  · intro q hq
    rw [mem_filter, walk3, mem_filter] at hq
    obtain ⟨⟨-, h1, -, h3⟩, hmid⟩ := hq
    have hy : q.2.1 = p.1 := congrArg Prod.fst hmid
    have hz : q.2.2.1 = p.2 := congrArg Prod.snd hmid
    rw [Finset.mem_product, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
    rw [hy] at h1
    rw [hz] at h3
    exact ⟨h1.symm, h3⟩
  · intro c hc
    rw [Finset.mem_product, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset] at hc
    rw [mem_filter, walk3, mem_filter]
    exact ⟨⟨mem_univ _, hc.1.symm, hp, hc.2⟩, rfl⟩
  · intro q hq
    rw [mem_filter] at hq
    have hy : q.2.1 = p.1 := congrArg Prod.fst hq.2
    have hz : q.2.2.1 = p.2 := congrArg Prod.snd hq.2
    obtain ⟨a, b, c, d⟩ := q
    simp only [Prod.mk.injEq] at hy hz ⊢
    simp_all
  · intro c _
    rfl

/-! ### Two consequences of Gibbs' inequality -/

/-- **Jensen for `log`**, in the form an averaging argument wants: the mean of the logs is at
most the log of the mean. Gibbs' inequality against the uniform distribution on `S`. -/
theorem sum_log_div_card_le_log_sum_div_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (hS : S.Nonempty) (a : ι → ℝ) (ha : ∀ i ∈ S, 0 < a i) :
    (∑ i ∈ S, Real.log (a i)) / #S ≤ Real.log ((∑ i ∈ S, a i) / #S) := by
  classical
  have hcard : (0 : ℝ) < #S := by exact_mod_cast Finset.card_pos.mpr hS
  have hA : (0 : ℝ) < ∑ i ∈ S, a i := Finset.sum_pos ha hS
  have hPsum : ∑ i : ι, (if i ∈ S then 1 / (#S : ℝ) else 0) = 1 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one_div,
      div_self (ne_of_gt hcard)]
  have hQsum : ∑ i : ι, (if i ∈ S then a i / (∑ j ∈ S, a j) else 0) ≤ 1 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div, div_self (ne_of_gt hA)]
  have hgibbs := sum_mul_log_div_le
    (fun i => if i ∈ S then 1 / (#S : ℝ) else 0)
    (fun i => if i ∈ S then a i / (∑ j ∈ S, a j) else 0)
    (fun i => by by_cases hi : i ∈ S <;> simp only [if_pos, if_neg, hi] <;> positivity)
    (fun i => by
      by_cases hi : i ∈ S
      · simp only [if_pos hi]
        exact le_of_lt (div_pos (ha i hi) hA)
      · simp [hi])
    (fun i hi => by
      have hiS : i ∈ S := by
        by_contra hcon
        simp only [if_neg hcon] at hi
        exact hi rfl
      simp only [if_pos hiS]
      exact ne_of_gt (div_pos (ha i hiS) hA))
    hPsum hQsum
  -- read the Gibbs sum off termwise
  have hterm : ∀ i : ι, (if i ∈ S then 1 / (#S : ℝ) else 0)
      * Real.log ((if i ∈ S then a i / (∑ j ∈ S, a j) else 0)
        / (if i ∈ S then 1 / (#S : ℝ) else 0))
      = if i ∈ S then (1 / (#S : ℝ)) * (Real.log (a i) - Real.log (∑ j ∈ S, a j)
          + Real.log (#S)) else 0 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [if_pos hi]
      have harg : (a i / (∑ j ∈ S, a j)) / (1 / (#S : ℝ))
          = a i * #S / (∑ j ∈ S, a j) := by
        field_simp
      rw [harg, Real.log_div (ne_of_gt (mul_pos (ha i hi) hcard)) (ne_of_gt hA),
        Real.log_mul (ne_of_gt (ha i hi)) (ne_of_gt hcard)]
      ring
    · simp only [if_neg hi, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_mem, Finset.univ_inter,
    ← Finset.mul_sum] at hgibbs
  have hsum : ∑ i ∈ S, (Real.log (a i) - Real.log (∑ j ∈ S, a j) + Real.log (#S))
      = (∑ i ∈ S, Real.log (a i)) - #S * Real.log (∑ j ∈ S, a j)
        + #S * Real.log (#S) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul]
  rw [hsum] at hgibbs
  have hc : (0 : ℝ) < 1 / (#S : ℝ) := by positivity
  have h2 : (∑ i ∈ S, Real.log (a i)) - #S * Real.log (∑ j ∈ S, a j)
      + #S * Real.log (#S) ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have hpos := mul_pos hc hcon
    linarith [hgibbs]
  rw [div_le_iff₀ hcard, Real.log_div (ne_of_gt hA) (ne_of_gt hcard)]
  linarith [h2]

/-- **The degree sum against the uniform distribution**: `∑_v d(v) log d(v) ≥ 2m log(2m/n)`.
Gibbs' inequality again, with `P(v) = d(v)/2m`. This is the notes' `H(X) ≤ log n` step. -/
theorem sum_degree_mul_log_degree_ge (hD : 0 < ∑ v, G.degree v) :
    ((∑ v, G.degree v : ℕ) : ℝ)
        * Real.log (((∑ v, G.degree v : ℕ) : ℝ) / (Fintype.card V : ℝ))
      ≤ ∑ v, (G.degree v : ℝ) * Real.log (G.degree v) := by
  classical
  set D : ℝ := ((∑ v, G.degree v : ℕ) : ℝ) with hDdef
  have hDpos : (0 : ℝ) < D := by rw [hDdef]; exact_mod_cast hD
  have hVne : Nonempty V := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hD
    exact absurd hD (lt_irrefl 0)
  have hn : (0 : ℝ) < Fintype.card V := by
    have := Fintype.card_pos (α := V); exact_mod_cast this
  have hPsum : ∑ v : V, (G.degree v : ℝ) / D = 1 := by
    rw [← Finset.sum_div, hDdef]
    push_cast
    rw [div_self (by rw [hDdef] at hDpos; exact_mod_cast ne_of_gt hDpos)]
  have hgibbs := sum_mul_log_div_le (fun v : V => (G.degree v : ℝ) / D)
    (fun _ : V => 1 / (Fintype.card V : ℝ))
    (fun v => by positivity) (fun _ => by positivity)
    (fun v _ => by positivity) hPsum
    (by rw [Finset.sum_const, card_univ, nsmul_eq_mul, mul_one_div, div_self (ne_of_gt hn)])
  have hterm : ∀ v : V, ((G.degree v : ℝ) / D)
      * Real.log ((1 / (Fintype.card V : ℝ)) / ((G.degree v : ℝ) / D))
      = ((G.degree v : ℝ) / D) * (Real.log D - Real.log (Fintype.card V))
        - ((G.degree v : ℝ) / D) * Real.log (G.degree v) := by
    intro v
    rcases Nat.eq_zero_or_pos (G.degree v) with h0 | hpos
    · rw [h0]
      simp
    · have hdpos : (0 : ℝ) < G.degree v := by exact_mod_cast hpos
      have harg : (1 / (Fintype.card V : ℝ)) / ((G.degree v : ℝ) / D)
          = D / ((Fintype.card V : ℝ) * G.degree v) := by
        field_simp
      rw [harg, Real.log_div (ne_of_gt hDpos) (by positivity),
        Real.log_mul (ne_of_gt hn) (ne_of_gt hdpos)]
      ring
  rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hPsum, one_mul] at hgibbs
  have hsplit : ∑ v : V, ((G.degree v : ℝ) / D) * Real.log (G.degree v)
      = (∑ v : V, (G.degree v : ℝ) * Real.log (G.degree v)) / D := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hsplit] at hgibbs
  rw [Real.log_div (ne_of_gt hDpos) (ne_of_gt hn)]
  have := hgibbs
  rw [sub_nonpos] at this
  calc D * (Real.log D - Real.log (Fintype.card V))
      ≤ D * ((∑ v : V, (G.degree v : ℝ) * Real.log (G.degree v)) / D) := by
        exact mul_le_mul_of_nonneg_left this (le_of_lt hDpos)
    _ = ∑ v : V, (G.degree v : ℝ) * Real.log (G.degree v) := by
        field_simp


/-! ### The two weighted fiberings -/

lemma card_dirEdges_fiber_fst (v : V) :
    #((dirEdges G).filter fun p => p.1 = v) = G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    rw [mem_filter, dirEdges, mem_filter] at hp
    rw [SimpleGraph.mem_neighborFinset]
    exact hp.2 ▸ hp.1.2
  · intro p hp p' hp' h
    rw [mem_filter] at hp hp'
    exact Prod.ext (hp.2.trans hp'.2.symm) h
  · intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu
    exact ⟨(v, u), by rw [mem_filter, dirEdges, mem_filter]; exact ⟨⟨mem_univ _, hu⟩, rfl⟩, rfl⟩

lemma card_dirEdges_fiber_snd (v : V) :
    #((dirEdges G).filter fun p => p.2 = v) = G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    rw [mem_filter, dirEdges, mem_filter] at hp
    rw [SimpleGraph.mem_neighborFinset]
    exact (hp.2 ▸ hp.1.2).symm
  · intro p hp p' hp' h
    rw [mem_filter] at hp hp'
    exact Prod.ext h (hp.2.trans hp'.2.symm)
  · intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu
    exact ⟨(u, v), by
      rw [mem_filter, dirEdges, mem_filter]
      exact ⟨⟨mem_univ _, hu.symm⟩, rfl⟩, rfl⟩

lemma sum_dirEdges_fst (f : V → ℝ) :
    ∑ p ∈ dirEdges G, f p.1 = ∑ v, (G.degree v : ℝ) * f v := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun p (_ : p ∈ dirEdges G) => mem_univ p.1)
    (fun p : V × V => f p.1)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl fun p hp => (by rw [(mem_filter.mp hp).2] : f p.1 = f v),
    Finset.sum_const, card_dirEdges_fiber_fst, nsmul_eq_mul]

lemma sum_dirEdges_snd (f : V → ℝ) :
    ∑ p ∈ dirEdges G, f p.2 = ∑ v, (G.degree v : ℝ) * f v := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun p (_ : p ∈ dirEdges G) => mem_univ p.2)
    (fun p : V × V => f p.2)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl fun p hp => (by rw [(mem_filter.mp hp).2] : f p.2 = f v),
    Finset.sum_const, card_dirEdges_fiber_snd, nsmul_eq_mul]

lemma degree_pos_of_mem_dirEdges {p : V × V} (hp : p ∈ dirEdges G) :
    0 < G.degree p.1 ∧ 0 < G.degree p.2 := by
  rw [dirEdges, mem_filter] at hp
  constructor
  · rw [SimpleGraph.degree_pos_iff_exists_adj]
    exact ⟨p.2, hp.2⟩
  · rw [SimpleGraph.degree_pos_iff_exists_adj]
    exact ⟨p.1, hp.2.symm⟩


/-! ### Theorem 10.3.3 -/

/-- **Theorem 10.3.3 (Blakey–Roy 1965).** Sidorenko's conjecture holds for the three-edge
path: for every graph `G` on `n` vertices with `m` edges,

    hom(P₄, G) · n² ≥ (2m)³,

which after dividing by `n⁴` is `t(P₄, G) ≥ t(K₂, G)³`.

Two applications of Gibbs' inequality, in the shape of the notes' entropy computation:
AM–GM over the middle edge turns `hom(P₄, G) = ∑ d(y)d(z)` into `∑ d(v) log d(v)`, and the
degree sum against the uniform distribution on vertices bounds that below by
`2m log(2m/n)`. -/
theorem sidorenko_path3 :
    ((∑ v, G.degree v : ℕ) : ℝ) ^ 3 ≤ #(walk3 G) * (Fintype.card V : ℝ) ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos (∑ v, G.degree v) with hD0 | hD
  · rw [hD0, Nat.cast_zero, zero_pow (by norm_num)]
    positivity
  -- the setting: `D = 2m > 0`, so there is an edge and `n > 0`
  set D : ℝ := ((∑ v, G.degree v : ℕ) : ℝ) with hDdef
  have hDpos : (0 : ℝ) < D := by rw [hDdef]; exact_mod_cast hD
  obtain ⟨v₀, -, hv₀⟩ : ∃ v ∈ (univ : Finset V), 0 < G.degree v := by
    by_contra hcon
    push_neg at hcon
    have : ∑ v, G.degree v = 0 :=
      Finset.sum_eq_zero fun v hv => Nat.le_zero.mp (hcon v hv)
    omega
  obtain ⟨u₀, hu₀⟩ := (G.degree_pos_iff_exists_adj v₀).mp hv₀
  have hn : (0 : ℝ) < Fintype.card V := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v₀⟩
    exact_mod_cast this
  have hEne : (dirEdges G).Nonempty := by
    refine ⟨(v₀, u₀), ?_⟩
    rw [dirEdges, mem_filter]
    exact ⟨mem_univ _, hu₀⟩
  have hcardE : (#(dirEdges G) : ℝ) = D := by rw [card_dirEdges, hDdef]
  -- the walk count is positive: an edge traversed back and forth is a walk
  have hWpos : (0 : ℝ) < #(walk3 G) := by
    have : (v₀, u₀, v₀, u₀) ∈ walk3 G := by
      rw [walk3, mem_filter]
      exact ⟨mem_univ _, hu₀, hu₀.symm, hu₀⟩
    have hne : (walk3 G).Nonempty := ⟨_, this⟩
    have := Finset.card_pos.mpr hne
    exact_mod_cast this
  -- AM–GM over the middle edge
  have hapos : ∀ p ∈ dirEdges G, (0 : ℝ) < (G.degree p.1 : ℝ) * G.degree p.2 := by
    intro p hp
    obtain ⟨h1, h2⟩ := degree_pos_of_mem_dirEdges G hp
    have h1' : (0 : ℝ) < G.degree p.1 := by exact_mod_cast h1
    have h2' : (0 : ℝ) < G.degree p.2 := by exact_mod_cast h2
    positivity
  have hsuma : ∑ p ∈ dirEdges G, ((G.degree p.1 : ℝ) * G.degree p.2) = #(walk3 G) := by
    rw [card_walk3]
    push_cast
    rfl
  have hjensen := sum_log_div_card_le_log_sum_div_card (dirEdges G) hEne
    (fun p => (G.degree p.1 : ℝ) * G.degree p.2) hapos
  rw [hsuma, hcardE] at hjensen
  -- the log of the product splits into the two weighted fiberings
  have hsplit : ∑ p ∈ dirEdges G, Real.log ((G.degree p.1 : ℝ) * G.degree p.2)
      = 2 * ∑ v, (G.degree v : ℝ) * Real.log (G.degree v) := by
    have hterm : ∀ p ∈ dirEdges G, Real.log ((G.degree p.1 : ℝ) * G.degree p.2)
        = Real.log (G.degree p.1) + Real.log (G.degree p.2) := by
      intro p hp
      obtain ⟨h1, h2⟩ := degree_pos_of_mem_dirEdges G hp
      have h1' : (G.degree p.1 : ℝ) ≠ 0 := by
        have : (0 : ℝ) < G.degree p.1 := by exact_mod_cast h1
        exact ne_of_gt this
      have h2' : (G.degree p.2 : ℝ) ≠ 0 := by
        have : (0 : ℝ) < G.degree p.2 := by exact_mod_cast h2
        exact ne_of_gt this
      exact Real.log_mul h1' h2'
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      sum_dirEdges_fst G (fun v => Real.log (G.degree v)),
      sum_dirEdges_snd G (fun v => Real.log (G.degree v))]
    ring
  rw [hsplit] at hjensen
  -- and the degree sum is bounded below by Gibbs against the uniform distribution
  have hstepA := sum_degree_mul_log_degree_ge G hD
  rw [← hDdef] at hstepA
  -- combine: `2 log (D/n) ≤ log (hom / D)`
  have hcomb : 2 * Real.log (D / Fintype.card V) ≤ Real.log (#(walk3 G) / D) := by
    have h1 : 2 * (D * Real.log (D / Fintype.card V))
        ≤ 2 * ∑ v, (G.degree v : ℝ) * Real.log (G.degree v) := by linarith [hstepA]
    have h2 : 2 * (D * Real.log (D / Fintype.card V)) / D ≤ Real.log (#(walk3 G) / D) := by
      calc 2 * (D * Real.log (D / Fintype.card V)) / D
          ≤ (2 * ∑ v, (G.degree v : ℝ) * Real.log (G.degree v)) / D := by
            exact div_le_div_of_nonneg_right h1 hDpos.le
        _ ≤ Real.log (#(walk3 G) / D) := hjensen
    calc 2 * Real.log (D / Fintype.card V)
        = 2 * (D * Real.log (D / Fintype.card V)) / D := by
          field_simp
      _ ≤ Real.log (#(walk3 G) / D) := h2
  -- exponentiate
  have hDn : (0 : ℝ) < D / Fintype.card V := by positivity
  have hWD : (0 : ℝ) < #(walk3 G) / D := by positivity
  have hsq : Real.log ((D / Fintype.card V) ^ 2)
      = 2 * Real.log (D / Fintype.card V) := by
    rw [Real.log_pow]
    norm_num
  have hfinal : (D / Fintype.card V) ^ 2 ≤ #(walk3 G) / D := by
    rw [← Real.log_le_log_iff (by positivity) hWD, hsq]
    exact hcomb
  rw [div_pow, div_le_div_iff₀ (by positivity) hDpos] at hfinal
  calc D ^ 3 = D ^ 2 * D := by ring
    _ ≤ #(walk3 G) * (Fintype.card V : ℝ) ^ 2 := by linarith [hfinal]


/-- **Theorem 10.3.3 in the notes' density form**: `t(P₄, G) ≥ t(K₂, G)³`, where
`t(F, G) = hom(F, G) / n^{v(F)}` is the homomorphism density — the probability that a uniform
random map of vertices is a homomorphism. This is Sidorenko's conjecture for the three-edge
path. -/
theorem sidorenko_path3_density (hn : 0 < Fintype.card V) :
    (((∑ v, G.degree v : ℕ) : ℝ) / (Fintype.card V : ℝ) ^ 2) ^ 3
      ≤ (#(walk3 G) : ℝ) / (Fintype.card V : ℝ) ^ 4 := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have h := sidorenko_path3 G
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  calc ((∑ v, G.degree v : ℕ) : ℝ) ^ 3 * (Fintype.card V : ℝ) ^ 4
      ≤ (#(walk3 G) * (Fintype.card V : ℝ) ^ 2) * (Fintype.card V : ℝ) ^ 4 := by
        exact mul_le_mul_of_nonneg_right h (by positivity)
    _ = #(walk3 G) * ((Fintype.card V : ℝ) ^ 2) ^ 3 := by ring


end Sidorenko

end PMC
