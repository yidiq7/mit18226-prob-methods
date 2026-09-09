import ProbMethods.Chapter10.EdgeCount

/-!
# §10.4 — Theorem 10.4.9: triangle-intersecting families

Zhao, *Probabilistic Methods in Combinatorics*, Theorem 10.4.9 (Chung, Graham, Frankl and
Shearer 1986): every triangle-intersecting family of graphs on `n` labelled vertices has
size `< 2 ^ (C(n,2) - 2)`.

The assembly of everything in §10.4. For each vertex set `S` of size `⌈n/2⌉`, the block
`PMC.block S` — edges inside `S` or inside its complement — meets every triangle
(`PMC.exists_pair_same_side`), so the family's trace on that block is *intersecting* and
`PMC.card_pow_le_prod_of_traces_intersecting` applies. The exponent then comes out of two
counting facts: every block has the same size `r` and every edge lies in the same number `k`
of blocks (`PMC.choose_mul_block_eq`), and the blocks are small — `2r < C(n,2)` — because
the split is balanced (`PMC.two_mul_choose_two_add_lt`).

`⌈n/2⌉` rather than `⌊n/2⌋`: `PMC.card_blocks_containing` needs blocks of size at least two,
and `⌈n/2⌉ ≥ 2` already at `n = 3`, whereas `⌊3/2⌋ = 1`. The two choices give the same `r`.
-/

open Finset

namespace PMC

section TriangleIntersecting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G` contains a triangle: there are three vertices all of whose edges lie in `G`.

Phrased through a 3-element vertex set rather than three explicit edges, so that no
non-diagonality proofs appear in the statement. -/
def HasTri (G : Finset (Edge V)) : Prop :=
  ∃ t : Finset V, #t = 3 ∧ ∀ e : Edge V, (∀ z ∈ e.1, z ∈ t) → e ∈ G

/-- **Every block meets every triangle.** Two of a triangle's three vertices lie on the same
side of `S`, and the edge between them is in the block. -/
theorem nonempty_inter_block_of_hasTri {G : Finset (Edge V)} (h : HasTri G) (S : Finset V) :
    (G ∩ block S).Nonempty := by
  obtain ⟨t, ht, hall⟩ := h
  obtain ⟨x, hx, y, hy, hxy, hside⟩ := exists_pair_same_side (t := t) (by omega) S
  have hnd : ¬ (s(x, y) : Sym2 V).IsDiag := fun hd => hxy (Sym2.mk_isDiag_iff.mp hd)
  refine ⟨⟨s(x, y), hnd⟩, ?_⟩
  rw [mem_inter]
  refine ⟨hall _ ?_, ?_⟩
  · intro z hz
    rw [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  · rw [block, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl fun z hz => ?_
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact h1
      · exact h2
    · refine Or.inr fun z hz => ?_
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact h1
      · exact h2

/-- **Theorem 10.4.9.** Every triangle-intersecting family of graphs on `n` labelled
vertices has size `< 2 ^ (C(n,2) - 2)`. -/
theorem card_lt_of_triangle_intersecting {n : ℕ} (hn : 3 ≤ n)
    (𝒢 : Finset (Finset (Edge (Fin n))))
    (htri : ∀ G ∈ 𝒢, ∀ G' ∈ 𝒢, HasTri (G ∩ G')) :
    #𝒢 < 2 ^ (n.choose 2 - 2) := by
  classical
  rcases 𝒢.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty]
    positivity
  set m := (n + 1) / 2 with hmdef
  have hm2 : 2 ≤ m := by omega
  have hmn : m ≤ n := by omega
  have hcardV : Fintype.card (Fin n) = n := Fintype.card_fin n
  set b := n - m with hbdef
  have hmb : m + b = n := by omega
  have hbal1 : b ≤ m + 1 := by omega
  have hbal2 : m ≤ b + 1 := by omega
  set r := m.choose 2 + b.choose 2 with hrdef
  set k := (n - 2).choose (m - 2) + (n - 2).choose m with hkdef
  set N := n.choose m with hNdef
  set J := (univ : Finset (Fin n)).powersetCard m with hJdef
  have hJcard : #J = N := by
    rw [hJdef, Finset.card_powersetCard, card_univ, hcardV, hNdef]
  have hNpos : 0 < N := by rw [hNdef]; exact Nat.choose_pos hmn
  have hkpos : 0 < k := by
    have : 0 < (n - 2).choose (m - 2) := Nat.choose_pos (by omega)
    omega
  have hC2two : 2 ≤ n.choose 2 := by
    have h3 : 3 ≤ n.choose 2 := by simpa using Nat.choose_le_choose 2 hn
    omega
  -- every block has size `r`
  have hblock : ∀ S ∈ J, #(block S) = r := by
    intro S hS
    rw [hJdef, Finset.mem_powersetCard] at hS
    rw [card_block, hS.2, hcardV, hrdef, hbdef]
  -- the double count and the (strict) balanced-split bound
  have hdc : N * r = n.choose 2 * k := by
    have h := choose_mul_block_eq (V := Fin n) hm2
    rw [hcardV] at h
    rw [hNdef, hrdef, hkdef, hbdef]
    exact h
  have hstrict : 2 * r < n.choose 2 := by
    have h := two_mul_choose_two_add_lt hbal1 hbal2 (by omega : 2 ≤ m + b)
    rw [hmb] at h
    rw [hrdef]
    exact h
  have h2kN : 2 * k < N := by
    have h1 : 2 * k * n.choose 2 < N * n.choose 2 := by
      calc 2 * k * n.choose 2 = 2 * (n.choose 2 * k) := by ring
        _ = 2 * (N * r) := by rw [hdc]
        _ = N * (2 * r) := by ring
        _ < N * n.choose 2 := mul_lt_mul_of_pos_left hstrict hNpos
    exact Nat.lt_of_mul_lt_mul_right h1
  -- the container bound, with the traces intersecting because blocks meet triangles
  have hcov : ∀ e : Edge (Fin n), k ≤ #(J.filter fun S => e ∈ block S) := by
    intro e
    have h := card_blocks_containing (V := Fin n) e hm2
    rw [hcardV] at h
    rw [hJdef, h]
  have hint : ∀ S ∈ J, ∀ G ∈ 𝒢, ∀ G' ∈ 𝒢, (G ∩ G' ∩ block S).Nonempty :=
    fun S _ G hG G' hG' => nonempty_inter_block_of_hasTri (htri G hG G' hG') S
  have hcont := card_pow_le_prod_of_traces_intersecting 𝒢 hne J block k hcov hint
  have hprod : ∀ S ∈ J, ((2 : ℝ) ^ #(block S) / 2) = (2 : ℝ) ^ r / 2 := by
    intro S hS
    rw [hblock S hS]
  rw [Finset.prod_congr rfl hprod, Finset.prod_const, hJcard] at hcont
  -- exponent arithmetic
  have hexp : r * N < (n.choose 2 - 2) * k + N := by
    have hsplit : (n.choose 2 - 2) * k + 2 * k = n.choose 2 * k := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have hrN : r * N = n.choose 2 * k := by rw [mul_comm r N, hdc]
    omega
  have hlt : ((2 : ℝ) ^ r / 2) ^ N < ((2 : ℝ) ^ (n.choose 2 - 2)) ^ k := by
    rw [div_pow, ← pow_mul, ← pow_mul, div_lt_iff₀ (by positivity), ← pow_add]
    exact pow_lt_pow_right₀ (by norm_num) hexp
  have hcast : (#𝒢 : ℝ) < (2 : ℝ) ^ (n.choose 2 - 2) :=
    lt_of_pow_lt_pow_left₀ k (by positivity) (lt_of_le_of_lt hcont hlt)
  exact_mod_cast hcast

end TriangleIntersecting

end PMC
