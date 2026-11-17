# P4-Q2-PZ37ANE — certified common Gibbs/Haar ordinary-L² zero classes

Date: 2026-11-17 JST.
Authoritative branch: `formal/real-hilbert-uniform-coercive-strong-limit`.
Pinned Lean: `v4.30.0-rc2`.
Pinned mathlib: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
Policy: append-only / tighten-only / overwrite-forbidden / same-root. Original Wilson model and all prior proofs unchanged.

## Exact mathematical scope

Fix any finite lattice H, beta >= 0 and the original nontrivial SU(2) carrier. On the *same* genuine periodic boundary/open-positive-half closure, define muPlus as the pushforward of the unchanged **full-periodic interacting Wilson Gibbs probability** and lambdaPlus as the original boundary Haar times open-half Haar.

For the unaltered original time-one physical two-mode Wilson cylinder F(c0,c1) from ANC:

1. Every such F is square-integrable under lambdaPlus by compactness, measurability and the certified original pointwise mode bound.
2. Its product-Haar real L² class has F as its exact almost-everywhere representative.
3. For all real coefficients c0,c1, the real L² class of F under muPlus vanishes if and only if the class under lambdaPlus vanishes:

   `[F(c0,c1)]_{L²(muPlus)} = 0 ↔ [F(c0,c1)]_{L²(lambdaPlus)} = 0`.

4. The **same** original physical two-mode coefficient pair, top-eigenspace orthogonal in the ORIGINAL physical one-slab Hilbert space, yields nonzero real L² classes simultaneously under genuine periodic muPlus and original product Haar lambdaPlus.

This is equality of the zero kernels of **the two coefficient assignments**, not equality or even quantitative uniform equivalence of the two Hilbert norms. It uses ANB mutual absolute continuity, ANC a.e.-zero equivalence, and AND's genuine periodic Gibbs-L² class. No independent ANE one-slab OS identification, positive reflection-form lower bound, completion, or continuum Yang–Mills mass-gap claim is made.

## Four machine-audited theorem statements

One additive 220-line Lean source:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicPositiveClosureCommonL2ZeroClassesV5_PZ37ANE.lean`.

1. `p4Q2PZ37ANE_timeOneOriginalHaar_memLp`.
2. `p4Q2PZ37ANE_timeOneOriginalHaarL2_coeFn`.
3. `p4Q2PZ37ANE_timeOneGibbsL2_eq_zero_iff_HaarL2_eq_zero`.
4. `p4Q2PZ37ANE_exists_common_nonzero_originalTimeOneGibbsAndHaarL2`.

All four independently reported only `propext`, `Classical.choice`, `Quot.sound`; none reported `sorryAx`. Both checks finished with 8,860/8,860 Lean jobs and changed-file warning/error 0/0.

## Failure retained as a version-bound CodeAI/MemoryOS repair observation

- First exact source `3413365cf4ea1df24cec523b8deac4e891188dc1`, [CI 44072873596](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44072873596), changed-Lean job `134003260971` completed FAILURE. Real diagnostics: `line 118:6 unexpected token 'λ'; expected command`, plus a cascading `line 116:55 unsolved goals`. Downstream `sorryAx` occurred in failed elaboration outputs only and was never certified or merged.
- Verified structural explanation: `λ` is Lean4 lambda syntax, so the local binder `let λ := ...` was not a legal ordinary variable name. This was a parsing failure, not evidence of a mathematical obstruction or absent theorem.
- Same-PR repair replaced this local `λ` and all corresponding uses by `haar`, without changing theorem statements or assumptions.
- Final source `d9a1e4e685ba49d3155456f02e21524d5ff54bd3`, [exact-source CI 44073515475](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44073515475), required changed Lean job `134005466236` and receipt job `134007067146`: completed SUCCESS. Four theorem axioms standard-three; sorryAx none; changed-file warnings/errors zero.
- Repair lesson is advisory/TEST_REQUIRED on any other HEAD. Source and independent CI observations—not this prose—carry proof authority. PR conversation contains the same append-only error evidence.

## Certified source/test-merge/integration tree

- Formal base: `6141d68f636a9773682ba4c2b7e8e4fb8ac138a9` (AND proof record).
- Certified source HEAD: `d9a1e4e685ba49d3155456f02e21524d5ff54bd3`.
- Certified source Git tree: `debd3dfa268edb5b0792717e333913c193f05d6a`.
- Test-merge ref: `ea13f54ba791e270c9a74cdf1f61aaed954d1c2a`, tree **identical** to certified source.
- [PR #6861](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6861): exact certified source merged via squash.
- Actual integrated Formal HEAD: `dc857262d472937f179b64c506733bb45dca7484`, tree **identical** to source and test merge.
- [Independent Formal push CI 44074295269](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44074295269), event=push, SHA=`dc857262d472937f179b64c506733bb45dca7484`: required Lean job `134008218505` and receipt job `134009891239`, both completed SUCCESS. Lean step completed SUCCESS; 8,860/8,860; all four audited standard-three only; sorryAx none; changed file warning/error zero.

## Next genuine obstruction (ANF and beyond)

The existing full-periodic Wilson OS reflection-positivity theorem accepts observables on the original open-half configuration and explicit integrability/transport data. ANE constructs ordinary L² classes on the **boundary/open-half closure**. Ordinary nonzero L² and mutual absolute continuity DO NOT imply nonzero OS quotient class. The next independent task is to construct a typed positive-time Wilson observable in the actual OS reflection-form domain (handling shared boundary correctly), verify its concrete reflection form and integrability, then prove its OS seminorm strictly positive—or preserve a demonstrated kernel obstruction. Only after this can physical OS Hilbert identification and one-slab intertwining be attempted. No unproved step is promoted to certification.
