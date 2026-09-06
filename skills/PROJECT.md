# Probabilistic Methods in Combinatorics — project conventions

Formalizing Yufei Zhao's *Probabilistic Methods in Combinatorics* (MIT 18.226) in
Lean 4 + Mathlib.

## Independence requirement — read this first

This is an **independent** formalization. Do not consult, search for, clone, read, or
copy from Meta's ATLAS formalization of this book, or any derivative of it, under any
circumstances. Work only from the lecture notes and from Mathlib. If you find yourself
looking at someone else's Lean rendering of one of these theorems, stop.

## Where things live

- `ProbMethods/Basic.lean` — **every project definition that appears in a statement**.
  This file is the orchestrator's. Do not add to it, edit it, or shadow a definition
  from it in your own file. If your proof needs a new definition, define it *locally in
  your target file*; if it needs a change to a shared one, say so on the issue instead
  of making the change.
- `ProbMethods/ChapterNN/*.lean` — statements and proofs, one file per group of results.
- `roadmap/` — the plan. `roadmap/<group>.md` has the mathematics behind your target,
  including the book's own proof sketch. **Read your target's entry before starting.**

## Your task is one `sorry`

Replace the `sorry` in your target declaration. Do not touch the statement — not its
name, binders, hypotheses, or conclusion. Do not touch other declarations, other files,
imports of other files, or docstrings you were not asked to change.

Helper lemmas are welcome; put them in your target file, above the target, in the `PMC`
namespace, `private` unless they are genuinely reusable. **A helper's statement is not
machine-checked against anything** — the orchestrator reads it as mathematics, so state
helpers honestly and do not smuggle an assumption into one.

## Imports

Use targeted imports, never `import Mathlib`. Measured on this project: a file importing
all of Mathlib elaborates in ~49s, the same file with targeted imports in ~7s, and CI
builds every file on every PR. `ProbMethods/Basic.lean` already gives you `SimpleGraph`,
`Finset`, cliques, `ℝ` and ordered big operators; add specific modules on top when you
need them.

## Style

- `autoImplicit` is **off** repo-wide. An undefined identifier is an error, not a
  silent new variable. This is deliberate — do not turn it back on.
- Namespace everything `PMC`.
- Prefer a named Mathlib lemma to heavy automation. `decide` on anything with a
  variable-sized search space, and `native_decide` anywhere, will fail the gate.
- No new axioms. The axiom policy is `net_zero`: a PR may not increase the trust
  surface. `sorry` policy is `block`: a PR may not leave a net-new `sorry`.

## Finite probability is formalized by counting

Chapters 1–3 argue over finite probability spaces. **Do not reach for
`MeasureTheory`/`ProbabilityTheory` for these.** "Colour each vertex uniformly at random,
so the expected number of cut edges is `m / 2`, so some colouring achieves it" becomes:
sum a `Finset`-valued quantity over all `2 ^ n` colourings, and apply
`Finset.exists_le_of_sum_le` or `Finset.exists_lt_of_sum_lt` to extract a witness at
least the mean. The union bound becomes `Finset.card_biUnion_le_card_mul`, or
`Finset.card_le_card` applied to an explicit union of bad sets.

Often the shortest honest Lean proof is not the book's probabilistic one — a greedy or
extremal argument that gives the same bound is perfectly acceptable, and the roadmap
notes where one exists. You are proving the statement, not transcribing the paragraph.

## Before you push

```bash
lake build          # must be clean: no errors, no `sorry` warnings in your file
```

The gate re-runs this clean-room, and additionally checks statement immutability, the
kernel-level statement comparator, axiom honesty, `sorry` count, and `Decidable`
instance drift. A green local `lake build` is necessary, not sufficient.
