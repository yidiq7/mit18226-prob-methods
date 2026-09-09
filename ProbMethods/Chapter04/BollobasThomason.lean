import ProbMethods.Chapter04.Threshold

/-!
# §4.3 — Lemma 4.3.7, the Bollobás–Thomason inequality

Zhao, *Probabilistic Methods in Combinatorics*, Lemma 4.3.7: for a monotone property `F` and
any `m ≥ 1`,

    P(Ω_p ∉ F) ≤ P(Ω_{p/m} ∉ F) ^ m.

This is the non-asymptotic engine behind Theorem 4.3.6 ("every sequence of non-trivial monotone
properties has a threshold"), which the notes derive from it — so it is the piece worth having,
and the asymptotic statement follows without any further probability.

## The route

Two steps, and only the first is a coupling.

1. **`m` independent copies.** Let `q = 1 - (1 - p/m)^m`. Sampling `Ω_{p/m}` independently `m`
   times and taking the union gives exactly `Ω_q`, because an element is absent from the union
   iff it is absent from all `m` copies. Since `F` is *upward closed*, the union lies outside
   `F` only if every copy does, and the copies are independent, so

       P(Ω_q ∉ F) ≤ P(Ω_{p/m} ∉ F) ^ m.

   In this framework the `m` copies are `Fin m → Finset α` with the product weight, and the
   union is `fun X => Finset.univ.biUnion X`; `PMC.pweight` and the product machinery in
   `ProbMethods/Product.lean` are what make "independent" mechanical rather than a definition
   to re-establish.

2. **`q ≤ p`.** Bernoulli's inequality gives `(1 - p/m)^m ≥ 1 - p`, i.e. `q ≤ p`, and for a
   monotone `F` the map `p ↦ P(Ω_p ∉ F)` is *antitone*: more edges can only help a monotone
   property. That antitonicity is the non-strict form of task #50
   (`PMC.strictMonoOn_sum_bweight`); it can be taken from there once #50 lands, or proved
   directly by the same one-coordinate coupling, which is the easier half.

Stated without the notes' non-triviality hypothesis on `F`, which the inequality does not need:
at `F = ∅` both sides are `1`, and at `F = univ` the left side is `0`.
-/

open Finset

namespace PMC

section BollobasThomason

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Lemma 4.3.7 (Bollobás–Thomason).** For an upward-closed family `F` and `m ≥ 1`,

    P(Ω_p ∉ F) ≤ P(Ω_{p/m} ∉ F) ^ m,

where `Ω_p` is the random subset including each element independently with probability `p`. -/
theorem sum_bweight_notMem_le_pow {F : Finset (Finset α)} (hF : IsMonotoneFamily F)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    (∑ X ∈ (univ : Finset α).powerset.filter (fun X => X ∉ F), bweight p X)
      ≤ (∑ X ∈ (univ : Finset α).powerset.filter (fun X => X ∉ F),
          bweight (p / m) X) ^ m := by
  sorry

end BollobasThomason

end PMC
