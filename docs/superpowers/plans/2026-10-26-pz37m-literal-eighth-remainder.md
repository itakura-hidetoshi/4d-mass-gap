# PZ37M literal Wilson eighth-order remainder implementation plan

> **For agentic workers:** Use superpowers:executing-plans, then one fresh whole-branch reviewer.

**Goal:** Connect the genuine interacting Wilson minor to the evaluated seventh coefficient with an eighth-order remainder.

**Architecture:** Integrate the true degree-six exponential Taylor polynomial under the original one- and two-slab Haar measures. Combine seventh-order row errors with first-order boundary differences, bound the degree-eight through twelve jet tail, and substitute the PZ37K/L coefficient identities.

**Tech Stack:** Lean v4.30.0-rc2, mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

**Spec:** User's inherited research contract; authoritative base b96a9bcdbabdfc87b06e2a56d87c3da6de41a749 and PZ37B/K/L source definitions.

## Global Constraints

- Genuine normalized SU(2) Haar and original Wilson action; middle spatial action occurs twice in Q.
- No new axioms, sorry, admit, native_decide, substituted posterior, or assumed cancellation.
- Fixed finite H and fixed boundary remainder constants only. No volume-uniform U0 or rank-three/mass-gap conclusion.
- Exact PR HEAD build, changed-file zero diagnostics, public theorem axiom audit, successful completion receipt before squash merge.

## Review Focus

- Signs and factorial 720 in the sixth Taylor term.
- Genuine iterated Haar integrals and full two-slab action, including intermediate spatial terms.
- Seventh-order row error times first-order difference gives eighth order; error products must also be bounded.
- All higher jet coefficients through degree twelve are retained and bounded.
- Nonminimal Vandermonde and minimal loop correction are correctly distinguished; no universal nonzero claim.

## Task 1: Genuine sixth Taylor rows

**Files:** Create `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSexticRowsV5_PZ37M.lean`.
**Interfaces:** Consumes PZ3 integrated quintic identities and PZ37B Taylor6 definitions; produces one/two literal Haar row seventh-remainder bounds.

- [ ] State and kernel-check the intended degree-six exponential bound, initially with an unsolved goal in a scratch test.
- [ ] Prove the degree-six scalar bound from Real.exp_bound and integrate it under genuine Haar.
- [ ] Identify the integrals with PZ37B Taylor6, and audit all exported theorem axioms.

## Task 2: Eighth-order minor stability and jet tail

**Files:** Create `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalEighthMinorEstimatesV5_PZ37M.lean` for reusable scalar estimates and `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSixthJetEighthTailV5_PZ37M.lean` for the physical jet.
**Interfaces:** Consumes PZ37B exact jet determinant; produces real eighth-order stability, first-order jet row differences, eighth-order jet tail.

- [ ] State and kernel-check the intended bounds in scratch before filling proofs.
- [ ] Bound finite polynomial sums and all six determinant error terms.
- [ ] Verify the complete exact jet identity yields the stated tail, without discarding coefficients.

## Task 3: Literal coefficient and evaluated cases

**Files:** Create `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLiteralSeventhCoefficientV5_PZ37M.lean`.
**Interfaces:** Consumes Tasks 1/2 and PZ37K/L; produces actual minor remainder at every H and explicit nonminimal/minimal specializations.

- [ ] Prove a nonnegative fixed-boundary constant K for the existing domain |beta| <= 1 and |beta*(2*M_H)| <= 1.
- [ ] Substitute exact evaluated coefficients, retaining the minimal boundary-loop wedge.
- [ ] Run changed-source preflight, dependency-closed Lean CI, complete exported-axiom audit and independent whole-branch review.
- [ ] Verify exact-head completion receipt, squash, and reread canonical HEAD.
