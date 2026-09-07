import ProbMethods.Weighted

/-!
# §4.1, §4.2, §4.4 — First moments in a random graph

Zhao, *Probabilistic Methods in Combinatorics*, §4.1 (triangles), §4.2 (thresholds for
fixed subgraphs) and §4.4 (clique number).

Both sections open with the same computation, so both live here. Each is stated as a finite
identity; the `n → ∞` threshold phrasing is the part this project's conventions keep out of
statements.

Graphs are edge sets in `Sym2 V`, so `PMC.bweight p` is the `G(n, p)` distribution
(`ProbMethods/Weighted.lean`), and both results are immediate from
`PMC.sum_bweight_mul_card_filter`.
-/

open Finset

namespace PMC

/-- An injective map induces an injection on unordered pairs. Mathlib has `Sym2.map` but no
injectivity lemma for it. -/
private lemma sym2_map_injective {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Sym2.map f) := by
  intro x y h
  induction x using Sym2.ind with
  | _ a b =>
    induction y using Sym2.ind with
    | _ c d =>
      simp only [Sym2.map_pair_eq, Sym2.eq_iff] at h ⊢
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hf h1, hf h2⟩
      · exact Or.inr ⟨hf h1, hf h2⟩

/-- **The expected number of `k`-cliques in `G(n, p)` is `C(n, k) * p ^ C(k, 2)`**
(Zhao, §4.4).

An identity, with no hypothesis on `p` or `k`: the patterns are the edge sets spanned by
the `C(n, k)` vertex `k`-sets, each carrying `C(k, 2)` edges. Forcing the right-hand side
below `1` is what bounds the clique number from above. -/
theorem sum_bweight_mul_card_cliqueSets {V : Type*} [Fintype V] [DecidableEq V]
    (p : ℝ) (k : ℕ) :
    ∑ E ∈ (univ : Finset (Sym2 V)).powerset, bweight p E * (#(cliqueSets k E) : ℝ)
      = (Fintype.card V).choose k * p ^ (k.choose 2) := by
  have h := sum_bweight_mul_card_filter (α := Sym2 V) p
    (powersetCard k (univ : Finset V)) spannedEdges (k.choose 2)
    (fun t ht => by
      rw [mem_powersetCard] at ht
      rw [card_spannedEdges, ht.2])
  rw [card_powersetCard, card_univ] at h
  exact h

/-- **The expected number of triangles in `G(n, p)` is `C(n, 3) * p ^ 3`** (Zhao, §4.1) —
the `k = 3` case of the clique count.

With `p ≍ 1 / n` this is bounded, which is the quantitative content of the threshold in the
notes. -/
theorem sum_bweight_mul_card_triangles {V : Type*} [Fintype V] [DecidableEq V] (p : ℝ) :
    ∑ E ∈ (univ : Finset (Sym2 V)).powerset, bweight p E * (#(triangles E) : ℝ)
      = (Fintype.card V).choose 3 * p ^ 3 := by
  have h := sum_bweight_mul_card_cliqueSets (V := V) p 3
  rw [show Nat.choose 3 2 = 3 from by decide] at h
  simp only [triangles_eq]
  exact h

/-- **The expected number of copies of a fixed graph `H` in `G(n, p)`** (Zhao, §4.2).

A copy is an embedding `f : W ↪ V` whose image edge set lies in `E`, so the count is over
embeddings rather than over subgraphs — the notes' "labelled copies". The expectation is
exactly `(number of embeddings) * p ^ e(H)`.

Again an identity with no hypothesis on `p`, and again immediate from
`PMC.sum_bweight_mul_card_filter`: an embedding carries `H` to an edge set of the same size,
since `Sym2.map` of an injection is injective. Specialising `H` to a triangle or a `k`-clique
recovers the two results above up to the labelled-versus-unlabelled factor. -/
theorem sum_bweight_mul_card_copies {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (p : ℝ) (H : Finset (Sym2 W)) :
    ∑ E ∈ (univ : Finset (Sym2 V)).powerset,
        bweight p E * (#((univ : Finset (W ↪ V)).filter
          fun f : W ↪ V => H.image (Sym2.map ⇑f) ⊆ E) : ℝ)
      = Fintype.card (W ↪ V) * p ^ #H := by
  classical
  have h := sum_bweight_mul_card_filter (α := Sym2 V) p
    (univ : Finset (W ↪ V)) (fun f : W ↪ V => H.image (Sym2.map ⇑f)) (#H)
    (fun f _ => card_image_of_injective _ (sym2_map_injective f.injective))
  rwa [card_univ] at h

end PMC
