import ProbMethods.Chapter06.ProductLLL
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.ZMod.Basic

/-!
# §6.4 — a directed cycle of length divisible by `k`

`PMC.exists_labelling_with_successor` (in `ProductLLL.lean`) is the probabilistic half of
Theorem 6.4.3: it labels the vertices by `ZMod k` so that every vertex has an out-neighbour
carrying the next label. This file is the combinatorial half, which turns such a labelling
into a directed cycle whose length is divisible by `k`.

**Mathlib has no digraph walks**, and this development does not build any. Choosing one
out-neighbour with the next label at every vertex packages the labelling as a *successor
function* `f : V → V`, and then a directed cycle is exactly a periodic orbit of `f`. So the
cycle comes from `Function.minimalPeriod`: the orbit of a periodic point consists of
distinct vertices by `Function.iterate_injOn_Iio_minimalPeriod`, and the labels increment
along it, so returning to the start forces the length to vanish in `ZMod k`.

A directed cycle of length `p` is recorded here as a `c : ℕ → V` with `r (c n) (c (n+1))`
for every `n`, with `c (n + p) = c n`, and injective on `Set.Iio p` — that is, `p` distinct
vertices joined in a directed cyclic order, with no `SimpleGraph.Walk` analogue needed.
-/

open Finset Function

namespace PMC

section DivisibleCycle

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- The orbit of a periodic point of the successor function is a directed cycle whose length
is divisible by `k`. Split out of `PMC.exists_cycle_of_successor` so that the pigeonhole step
can supply the periodic point from either side of the repetition it finds. -/
private theorem cycle_of_periodic {k : ℕ} (r : V → V → Prop) (f : V → V) (x : V → ZMod k)
    (hr : ∀ v, r v (f v)) (hiter : ∀ (n : ℕ) (v : V), x (f^[n] v) = x v + n)
    (u : V) (m : ℕ) (hm : 0 < m) (hu : f^[m] u = u) :
    ∃ (p : ℕ) (c : ℕ → V), 0 < p ∧ k ∣ p ∧ (∀ n, r (c n) (c (n + 1))) ∧
      (∀ n, c (n + p) = c n) ∧ Set.InjOn c (Set.Iio p) := by
  have hpos : 0 < minimalPeriod f u := IsPeriodicPt.minimalPeriod_pos hm hu
  have hfix : f^[minimalPeriod f u] u = u := isPeriodicPt_minimalPeriod f u
  refine ⟨minimalPeriod f u, fun n => f^[n] u, hpos, ?_, fun n => ?_, fun n => ?_, ?_⟩
  · -- the labels increment along the orbit, so `p` steps back to the start kills `p`
    have h : x u + (minimalPeriod f u : ZMod k) = x u := by
      rw [← hiter (minimalPeriod f u) u, hfix]
    exact (ZMod.natCast_eq_zero_iff _ _).mp (by linear_combination h)
  · show r (f^[n] u) (f^[n + 1] u)
    rw [Function.iterate_succ_apply']
    exact hr _
  · show f^[n + minimalPeriod f u] u = f^[n] u
    rw [Function.iterate_add_apply, hfix]
  · exact iterate_injOn_Iio_minimalPeriod

/-- **Cycle extraction.** If a labelling `x : V → ZMod k` admits a successor function `f` —
every vertex is sent to one of its `r`-out-neighbours, whose label is one more — then `r` has
a directed cycle whose length is divisible by `k`.

Iterating `f` from any vertex must repeat in a finite type, which produces a periodic point;
the cycle is its orbit. -/
theorem exists_cycle_of_successor [Nonempty V] {k : ℕ} (r : V → V → Prop)
    (f : V → V) (x : V → ZMod k) (hr : ∀ v, r v (f v)) (hx : ∀ v, x (f v) = x v + 1) :
    ∃ (p : ℕ) (c : ℕ → V), 0 < p ∧ k ∣ p ∧ (∀ n, r (c n) (c (n + 1))) ∧
      (∀ n, c (n + p) = c n) ∧ Set.InjOn c (Set.Iio p) := by
  have hiter : ∀ (n : ℕ) (v : V), x (f^[n] v) = x v + n := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
        intro v
        rw [Function.iterate_succ_apply', hx, ih v]
        push_cast
        ring
  obtain ⟨v₀⟩ := ‹Nonempty V›
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] v₀)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine cycle_of_periodic r f x hr hiter (f^[i] v₀) (j - i) (by omega) ?_
    rw [← Function.iterate_add_apply]
    have hji : j - i + i = j := by omega
    rw [hji, ← hfij]
  · refine cycle_of_periodic r f x hr hiter (f^[j] v₀) (i - j) (by omega) ?_
    rw [← Function.iterate_add_apply]
    have hij' : i - j + j = i := by omega
    rw [hij', hfij]

/-- **Theorem 6.4.3, for a digraph of out-degree exactly `δ`.** If every vertex of a
loopless digraph has out-degree exactly `δ` and in-degree at most `D`, and

    e ((k-1)/k) ^ δ (D + δD + 1) ≤ 1,

then the digraph has a directed cycle whose length is divisible by `k`.

Both halves are now in place: `PMC.exists_labelling_with_successor` provides the labelling,
and choosing the promised out-neighbour at each vertex turns it into the successor function
`PMC.exists_cycle_of_successor` consumes. The `choose` step is where "every vertex has *an*
out-neighbour with the next label" becomes "*the* chosen out-neighbour", which is exactly
what makes the orbit argument available. -/
theorem exists_cycle_length_dvd [DecidableEq V] [Nonempty V] (r : V → V → Prop)
    [DecidableRel r] {k δ D : ℕ} [NeZero k] (hD : 1 ≤ D) (hloop : ∀ v, ¬ r v v)
    (hout : ∀ v, #((univ : Finset V).filter fun u => r v u) = δ)
    (hin : ∀ v, #((univ : Finset V).filter fun u => r u v) ≤ D)
    (hep : Real.exp 1 * (((k : ℝ) - 1) / k) ^ δ * ((D + δ * D : ℕ) + 1) ≤ 1) :
    ∃ (p : ℕ) (c : ℕ → V), 0 < p ∧ k ∣ p ∧ (∀ n, r (c n) (c (n + 1))) ∧
      (∀ n, c (n + p) = c n) ∧ Set.InjOn c (Set.Iio p) := by
  obtain ⟨x, hx⟩ := exists_labelling_with_successor r hD hloop hout hin hep
  choose f hf hfx using hx
  exact exists_cycle_of_successor r f x hf hfx

/-- **Theorem 6.4.3 (Alon–Linial 1989), first-pass constant.** Every loopless digraph with
minimum out-degree `δ` and maximum in-degree `D` satisfying

    e ((k-1)/k) ^ δ (D + δD + 1) ≤ 1

contains a directed cycle whose length is divisible by `k`.

This is the notes' hypothesis — out-degree at *least* `δ` — obtained from the exactly-`δ`
case by **deleting out-edges**: choose `δ` out-neighbours at each vertex
(`Finset.exists_subset_card_eq`) and run the argument on the resulting sub-digraph, whose
out-degree is exactly `δ` and whose in-degree only dropped. A cycle of the sub-digraph is a
cycle of the original.

The reduction is needed rather than a monotonicity argument: the probability bound wants
out-degree *large* (more out-neighbours, more chances to avoid the bad event) while the
dependency-degree bound wants it *small*, so no single inequality on `δ` serves both. -/
theorem exists_cycle_length_dvd_of_le_outdegree [DecidableEq V] [Nonempty V]
    (r : V → V → Prop) [DecidableRel r] {k δ D : ℕ} [NeZero k] (hD : 1 ≤ D)
    (hloop : ∀ v, ¬ r v v)
    (hout : ∀ v, δ ≤ #((univ : Finset V).filter fun u => r v u))
    (hin : ∀ v, #((univ : Finset V).filter fun u => r u v) ≤ D)
    (hep : Real.exp 1 * (((k : ℝ) - 1) / k) ^ δ * ((D + δ * D : ℕ) + 1) ≤ 1) :
    ∃ (p : ℕ) (c : ℕ → V), 0 < p ∧ k ∣ p ∧ (∀ n, r (c n) (c (n + 1))) ∧
      (∀ n, c (n + p) = c n) ∧ Set.InjOn c (Set.Iio p) := by
  classical
  choose S hS hScard using fun v => Finset.exists_subset_card_eq (hout v)
  have hmem : ∀ v u, u ∈ S v → r v u := by
    intro v u hu
    have := hS v hu
    rw [mem_filter] at this
    exact this.2
  obtain ⟨p, c, hp, hkp, hstep, hper, hinj⟩ :=
    exists_cycle_length_dvd (fun v u => u ∈ S v) (k := k) (δ := δ) (D := D) hD
      (fun v hv => hloop v (hmem v v hv))
      (fun v => by
        have hfil : (univ : Finset V).filter (fun u => u ∈ S v) = S v := by ext u; simp
        rw [hfil, hScard v])
      (fun v => le_trans (Finset.card_le_card (fun u hu => by
        rw [mem_filter] at hu ⊢
        exact ⟨mem_univ u, hmem u v hu.2⟩)) (hin v))
      hep
  exact ⟨p, c, hp, hkp, fun n => hmem _ _ (hstep n), hper, hinj⟩

/-- The analytic step behind Theorem 6.4.3's stated constant: `k (1 + log M) ≤ δ` turns the
local lemma's numeric hypothesis `e ((k-1)/k)^δ M ≤ 1` into a bound on `k`.

The chain is `(k-1)/k = 1 - 1/k ≤ exp(-1/k)`, so `((k-1)/k)^δ ≤ exp(-δ/k)` and the left
side is at most `exp(1 - δ/k) M`, which is `≤ 1` exactly when `1 + log M ≤ δ/k`. -/
private lemma exp_pow_mul_le_one {k δ : ℕ} {M : ℝ} (hk : 0 < k) (hM : 0 < M)
    (h : (k : ℝ) * (1 + Real.log M) ≤ δ) :
    Real.exp 1 * (((k : ℝ) - 1) / k) ^ δ * M ≤ 1 := by
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbase : ((k : ℝ) - 1) / k = 1 - 1 / k := by field_simp
  have hb0 : 0 ≤ ((k : ℝ) - 1) / k := by
    rw [hbase, sub_nonneg, div_le_one hk0]; exact hk1
  have hb : ((k : ℝ) - 1) / k ≤ Real.exp (-(1 / k)) := by
    rw [hbase]
    have := Real.add_one_le_exp (-(1 / (k : ℝ)))
    linarith
  have hpow : (((k : ℝ) - 1) / k) ^ δ ≤ Real.exp (-((δ : ℝ) / k)) := by
    calc (((k : ℝ) - 1) / k) ^ δ ≤ Real.exp (-(1 / (k : ℝ))) ^ δ := pow_le_pow_left₀ hb0 hb δ
      _ = Real.exp (-((δ : ℝ) / k)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have hlog : 1 - (δ : ℝ) / k ≤ -Real.log M := by
    have h1 : 1 + Real.log M ≤ (δ : ℝ) / k := by
      rw [le_div_iff₀ hk0]; linarith
    linarith
  calc Real.exp 1 * (((k : ℝ) - 1) / k) ^ δ * M
      ≤ Real.exp 1 * Real.exp (-((δ : ℝ) / k)) * M := by
        have := mul_le_mul_of_nonneg_left hpow (Real.exp_pos 1).le
        exact mul_le_mul_of_nonneg_right this hM.le
    _ = Real.exp (1 - (δ : ℝ) / k) * M := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-Real.log M) * M :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hlog) hM.le
    _ = 1 := by rw [Real.exp_neg, Real.exp_log hM]; field_simp

/-- **Theorem 6.4.3 in the notes' form**, with the first-pass dependency degree. Every
loopless digraph with minimum out-degree `δ` and maximum in-degree `D` contains a directed
cycle of length divisible by `k` as long as

    k (1 + log (1 + D + δD)) ≤ δ,   i.e.   k ≤ δ / (1 + log (1 + D + δD)).

The notes state `k ≤ δ / (1 + log (1 + δD))`. The extra `D` is the price of the
straightforward dependency digraph counted by `PMC.card_digraph_dependency_le`; recovering
their constant needs the smaller dependency digraph of their final trick, which shrinks `N`
and so plugs into the same assembly. -/
theorem exists_cycle_length_dvd_of_log_bound [DecidableEq V] [Nonempty V]
    (r : V → V → Prop) [DecidableRel r] {k δ D : ℕ} [NeZero k] (hD : 1 ≤ D)
    (hloop : ∀ v, ¬ r v v)
    (hout : ∀ v, δ ≤ #((univ : Finset V).filter fun u => r v u))
    (hin : ∀ v, #((univ : Finset V).filter fun u => r u v) ≤ D)
    (hlog : (k : ℝ) * (1 + Real.log ((D + δ * D : ℕ) + 1)) ≤ δ) :
    ∃ (p : ℕ) (c : ℕ → V), 0 < p ∧ k ∣ p ∧ (∀ n, r (c n) (c (n + 1))) ∧
      (∀ n, c (n + p) = c n) ∧ Set.InjOn c (Set.Iio p) := by
  refine exists_cycle_length_dvd_of_le_outdegree r hD hloop hout hin ?_
  exact exp_pow_mul_le_one (Nat.pos_of_ne_zero (NeZero.ne k)) (by positivity) hlog

end DivisibleCycle

end PMC
