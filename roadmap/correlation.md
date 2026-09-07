# Chapter 7 — Correlation Inequalities

## The finding: §7.1 is upstream

**Mathlib already proves the Fortuin–Kasteleyn–Ginibre inequality.** `fkg`, in
`Mathlib/Combinatorics/SetFamily/FourFunctions.lean`, states it for *any*
log-supermodular measure on a distributive lattice:

    (∑ a, μ a * f a) * (∑ a, μ a * g a) ≤ (∑ a, μ a) * ∑ a, μ a * (f a * g a)

for monotone nonnegative `f`, `g` and `μ` with `μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)`. It is
derived there from the Ahlswede–Daykin **four functions theorem**, which Mathlib also has,
along with **Holley's inequality** and the **Harris–Kleitman** inequality
(`Combinatorics/SetFamily/HarrisKleitman.lean`).

So Zhao's Theorem 7.1.x — the Harris–FKG inequality — is not work. It is recorded as
`upstream` and must never be published as a task.

### harris_fkg — the bridge, proved
`PMC.pweight_fkg`: for a product measure on subsets and monotone nonnegative `f`, `g`,

    E[f] * E[g] ≤ E[f * g]

All this contributes over Mathlib's `fkg` is the log-supermodularity hypothesis and the
normalisation `∑ w = 1`. The hypothesis holds **with equality** for a product measure
(`PMC.pweight_mul_pweight`), which is the precise sense in which "independent coordinates"
is what makes FKG applicable:

    w T * w U = w (T ∩ U) * w (T ∪ U)

proved by writing `pweight` as one product over the ground set
(`PMC.pweight_eq_prod`) and checking the four cases `i ∈ T`, `i ∈ U` pointwise.

**The lesson for the rest of the book: check Mathlib's `Combinatorics/SetFamily` before
planning a chapter.** That directory turned out to hold FKG, Ahlswede–Daykin, Holley,
Harris–Kleitman, Kleitman's lemma and Kruskal–Katona — several of which are chapter-level
results here. §1.2's Sperner/LYM/EKR were already known to be upstream; this is the same
lesson one chapter later.

## Applications to random graphs (§7.2) — proved

### fkg_random_graphs
`PMC.pweight_correlate`: for **upward-closed** properties `A` and `B` of a random subset,

    weight(A) * weight(B) ≤ weight(A ∧ B)

This is the form applications use. It comes from `pweight_fkg` applied to the indicator
functions, which are monotone exactly because the properties are upward-closed — that
passage from monotone *functions* to monotone *events* is the whole content added here.

With `α := Sym2 V` it reads "monotone graph properties correlate in `G(n, p)`".

### fkg_triangle
`PMC.pweight_hasTriangle_correlate`: containing a triangle correlates with any monotone
property. `hasTriangle_mono` is immediate (`spannedEdges t ⊆ E ⊆ F`), and `HasTriangle`
needed an explicit `DecidablePred` instance — it *is* decidable, being a bounded
existential over `powersetCard 3 univ`, but instance search does not unfold a `def`. That
instance is now in `Basic.lean`, which is also what makes `HasTriangle` usable in a
`filter` at all.

Further applications in the notes follow the same pattern: state the property, prove it
upward-closed, apply `pweight_correlate`. No probability is involved beyond this point —
which is the useful upshot of the chapter being upstream.

One caveat worth recording: `PMC.bweight` (the constant-`p` form used in Chapter 4) and
`PMC.pweight` are the same measure when `p` is constant, but they are *defined* differently
— `bweight` by cardinality exponents, `pweight` by products. A bridging lemma
`bweight p = pweight (fun _ => p)` would let Chapter 4's results and FKG be used together;
it is not yet proved.
