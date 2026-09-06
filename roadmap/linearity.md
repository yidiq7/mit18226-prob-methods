# Chapter 2 — Linearity of Expectations

Phase 1 covered §2.3, which is complete. Phase 2 opens the rest of the chapter. Each
section below records what is formalized, what route to take when the book's own proof
does not transfer, and — for §2.6 — why the node is deferred outright.

Definitions these sections need are absent from Mathlib and are authored at the
centralized layer in `ProbMethods/Basic.lean` before any task references them.

## Turán's theorem and independent sets (§2.3)

Mathlib has Turán's theorem in structural form
(`SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`): the extremal `K_{r+1}`-free
graphs are the Turán graphs. It does not have the edge-count bound the notes derive, nor
Caro–Wei. Both are nodes here.

### caro_wei
`PMC.exists_isIndepSet_caro_wei` — Theorem 2.3.2 (Caro 1979, Wei 1981).

Every graph has an independent set of size at least `∑ v, 1 / (d v + 1)`.

Zhao's proof: take a uniformly random ordering of the vertices and keep every vertex that
precedes all of its neighbours. The kept set is independent, and `v` is kept exactly when
it comes first among `{v} ∪ N(v)`, which happens with probability `1 / (d v + 1)`; so the
expected size is `∑ v, 1 / (d v + 1)` and some ordering does at least as well.

Remark 2.3.4 gives a derandomization that is likely the easier Lean route: repeatedly
remove a vertex of smallest degree together with its neighbours, charging weight
`1 / (d v + 1)` to each vertex removed. Total weight removed per step is at most 1, so the
process runs for at least `∑ v, 1 / (d v + 1)` steps, each contributing one vertex to an
independent set. Either proof is acceptable.

### caro_wei_clique
`PMC.exists_isClique_caro_wei` — Corollary 2.3.5.

Every `n`-vertex graph has a clique of size at least `∑ v, 1 / (n - d v)`. Apply
`caro_wei` to the complement, where `v` has degree `n - 1 - d v`, so
`1 / (deg_{Gᶜ} v + 1) = 1 / (n - d v)`.

### turan_edges
`PMC.card_edgeFinset_le_of_cliqueFree` — Theorem 2.3.6 (Turán 1941).

An `n`-vertex `K_{r+1}`-free graph has at most `(1 - 1/r) · n² / 2` edges.

Zhao's proof: `K_{r+1}`-freeness bounds the clique from `caro_wei_clique` by `r`, so
`r ≥ ∑_v 1/(n - d_v) ≥ n / (n - (1/n) ∑_v d_v) = n / (n - 2m/n)` by the AM–HM inequality
(equivalently, convexity of `x ↦ 1/x`). Rearranging gives `m ≤ (1 - 1/r) n² / 2`.

This is the one node in phase 1 with a real analytic step. Do not hand-roll the AM–HM
inequality: Mathlib has it as `Finset.sq_sum_div_le_sum_sq_div` (Sedrakyan's lemma, aka
Titu's or Engel's form, in `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`), which
gives `∑ (f i)^2 / g i ≥ (∑ f i)^2 / ∑ g i`. Taking `f ≡ 1` and `g v = n - d v` is exactly
the step needed. `Finset.sum_degrees_eq_twice_card_edges` supplies `∑ v, d v = 2 * m`.

## Hamiltonian paths in tournaments (§2.1)

`PMC.beats` and `PMC.hamiltonPaths` (`ProbMethods/Basic.lean`) encode a tournament on
`Fin n` as a function `t : Sym2 (Fin n) → Bool`, read against the linear order on `Fin n`:
on the edge `s(a, b)` with `a < b`, `true` means `a` beats `b`. Diagonal values `t s(a, a)`
are never consulted, so every tournament is represented equally often and the averaging
argument can range over all `2 ^ Fintype.card (Sym2 (Fin n))` functions. This is the same
larger-uniform-space device the Chapter 1 counting proofs converged on independently.

A Hamilton path is an ordering `σ : Equiv.Perm (Fin n)` of the vertices, `σ i` being the
vertex in position `i`, with every consecutive pair directed forwards. Consecutive
positions are picked out by `(j : ℕ) = (i : ℕ) + 1` over a pair `i j : Fin n`, rather than
by indexing over `Fin (n - 1)`, so the definition carries no truncated subtraction.

The definitions were checked against small cases before being committed: over all `64`
tournaments on `3` vertices the Hamilton-path counts total `96 = 3! * 2 ^ 4`, over all `8`
tournaments on `2` vertices they total `8 = 2! * 2 ^ 2`, and `beats t a b = !beats t b a`
evaluates to `true` for every `t` and every `a ≠ b` on `Fin 3`. Those totals are exactly
the identity the counting proof needs.

### szele
`PMC.exists_tournament_factorial_le_hamiltonPaths` — Theorem 2.1.2 (Szele 1943), per the
notes the first use of the probabilistic method.

Some tournament on `n` vertices has at least `n! / 2 ^ (n - 1)` Hamilton paths, stated
multiplicatively as `n ! ≤ #(hamiltonPaths t) * 2 ^ (n - 1)` to avoid division and
truncated subtraction.

Zhao's proof orients each edge independently and uniformly. A fixed ordering is a Hamilton
path with probability `2 ^ (1 - n)` because it constrains `n - 1` distinct edges, so the
expectation is `n! * 2 ^ (1 - n)` and some tournament meets it. In counting form: summing
`#(hamiltonPaths t)` over all `t` and exchanging the order of summation gives
`n! * 2 ^ (M - (n - 1))` with `M = Fintype.card (Sym2 (Fin n))`, and the maximum is at
least the mean. That the `n - 1` consecutive pairs are *distinct* edges is the one step
worth care — it holds because a path visits distinct vertices.

The minimisation half of Question 2.1.1 is not a node: the notes leave it as an exercise
and it is not a probabilistic argument.

## Sum-free subsets (§2.2)

Theorem 2.2.1 (Erdős 1965): every set of `n` nonzero integers contains a sum-free subset
of size at least `n / 3`.

**The book's proof does not transfer.** It draws `θ` uniformly from `[0, 1]` and takes
`A_θ = {a ∈ A : {aθ} ∈ (1/3, 2/3)}`, then computes `E|A_θ| = n/3`. That is an average over
a continuum against Lebesgue measure — outside this project's counting convention, and it
would drag `MeasureTheory` into Chapter 2 for a single result.

**Take the discrete route instead** (the Alon–Spencer version). Choose a prime
`p ≡ 2 (mod 3)` with `p > 2 * max |a|`, write `p = 3k + 2`, and let
`M = {k+1, …, 2k+1} ⊆ ZMod p`, which is sum-free. For `θ ∈ {1, …, p-1}` put
`A_θ = {a ∈ A : (a * θ : ZMod p) ∈ M}`. Each `A_θ` is sum-free *as a set of integers*,
because `a + b = c` over `ℤ` forces `aθ + bθ = cθ` in `ZMod p`. Since `a ≢ 0`, the map
`θ ↦ aθ` permutes the nonzero residues, so each `a` lies in `A_θ` for exactly
`#M = k + 1` of the `p - 1` choices. Hence `∑_θ #A_θ = n(k+1)` and some `θ` achieves
`#A_θ ≥ n(k+1)/(3k+1) > n/3`.

Prime selection is available rather than something to build: Dirichlet's theorem is in
Mathlib as `Nat.forall_exists_prime_gt_and_eq_mod (ha : IsUnit a) (n : ℕ) : ∃ p > n,
p.Prime ∧ (p : ZMod q) = a`, in `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`. Take
`q = 3` and `a = 2`.

### sumfree
`PMC.exists_sumFree_subset` — Theorem 2.2.1. Stated as `#A ≤ 3 * #B` so the claim stays in
`ℕ` with no division. `PMC.SumFree` is in `ProbMethods/Basic.lean`, defined over any `Add`
structure as `∀ a ∈ A, ∀ b ∈ A, a + b ∉ A`.

The definition was checked before committing: `{1}`, `{3,4,5}` and `{1,3,5,7}` evaluate
sum-free, while `{1,2}`, `{1,2,3}` and `{0,5}` do not — the last because `5 + 0 = 5`, which
is why the theorem needs `0 ∉ A`.

## Sampling (§2.4)

Proposition 2.4.4: every tetrahedron-free 3-graph on `n ≥ 4` vertices has at most
`(7/10) * C(n, 3)` edges.

The averaging half is routine — edge density is preserved by averaging over 5-subsets. The
other half is a finite case check: every tetrahedron-free 3-graph on `5` vertices has at
most `7` of its `10` triples. That is a search over `2 ^ 10 = 1024` hypergraphs, which
`decide` can in principle do, but kernel reduction at that size is where the node will
live or die. Note also that `verify-decide-instance` blocks new `Decidable` instances, so
whatever is written must ride on instances Mathlib already provides.

Statement not yet authored; the 3-graph and tetrahedron-free definitions are needed first.

## Unbalancing lights (§2.5)

Theorem 2.5.1 is asymptotic — `(sqrt(2/π) + o(1)) * n^(3/2)` — so by the roadmap's
convention it is not published in that form. **An explicit-constant version is available,
and is what we will state.** The notes give the exact expectation in passing:
`E|S_n| = n * 2^(1-n) * C(n-1, ⌊(n-1)/2⌋)` for `S_n` a sum of `n` independent uniform
`±1`. Summing over the `n` rows gives

    ∃ x y ∈ {±1}^n,  ∑_{i,j} a_ij x_i y_j  ≥  n^2 * C(n-1, ⌊(n-1)/2⌋) / 2^(n-1),

which is the book's bound with the central limit theorem removed — the CLT is used only to
turn that closed form into `sqrt(2/π) * n^(3/2)`. Stating it this way keeps the node in
Chapter 2 rather than deferring it behind Chapter 9's machinery.

Theorem 2.5.2 is **not** a node: its proof rests on a compactness argument producing an
unspecified constant `c_k`, which is not something a `prove` task can be checked against.

Statement not yet authored.

## Crossing number inequality (§2.6) — DEFERRED

**Not formalizable against the current Mathlib, and not a node in any planned phase.**

The crossing number is defined through *drawings* of a graph in the plane, and the proof of
Theorem 2.6.2 runs through Euler's formula and a count of faces. Mathlib has no planarity
development at all: searching the library for `Planar`, `crossingNumber`, or Euler's
formula turns up nothing but the words "Planar graphs" in one docstring. Formalizing this
node means first building topological graph theory, which is a larger undertaking than the
rest of this book put together.

Recorded here so that a later orchestrator does not rediscover it from scratch. If Mathlib
gains a planarity development, §2.6 becomes a phase of its own.
