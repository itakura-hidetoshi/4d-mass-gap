# P4-Q2-PZ37AKM — original AJA Haar-budget comparison under H-uniform coercivity

Verified original-model mathematical statements against exact-source Lean CI on
2026-11-12 JST. Theorem source and actual test merge had identical Git trees;
the formal theorem squash has the identical tree. The independent formal-push
audit is recorded in the append-only completion section after its workflow ends.

## Physical model, fixed scope, original parameters

The sole theorem canonical branch is
`formal/real-hilbert-uniform-coercive-strong-limit`.
For each original finite spatial H and positive beta, use the original
physical SU(2) Wilson one-slab transfer P and S=P/||P|| on the actual
gauge-invariant Haar L² Hilbert space, the unchanged signed centered ZW source
f0, full S-fixed top eigenspace with orthogonal projection Q, and genuine
excited source Q^perp f0. No substituted source or artificial finite model
enters the statements.

Use the *unchanged* original AJA Haar certificate

```text
B_(H,beta) = m_(H,beta)^2 * Measure.real mu_H
  {U | u_(H,beta)(U) < -m_(H,beta)}
V_H = ||f0_H||^2
T_(H,beta) = ||Q f0_H||^2
E_(H,beta) = ||Q^perp f0_H||^2
L_(H,beta) = AKK's genuine mass-squared affine Ward full-top floor.
```

The AKL original uniformly positive coupling cutoff beta_* is
`twoSidedTwelveSpatialUniformGapCutoff 9 (by norm_num)`, with beta_*>0
and no H argument. Let q=3071/3072, so 0<q<1.

## Kernel-certified mathematical comparison

For every finite H, every **0<beta<=beta_***, every n>=1, AKM proves

```text
L_(H,beta) <= T_(H,beta) <= ||S_(H,beta)^n f0_H||^2
  <= T_(H,beta) + (q^n * ||Q^perp f0_H||)^2

and

B_(H,beta) <= V_H/16 .
```

The middle exact power-energy split is the unchanged AJZ orthogonal
Pythagoras; the excited tail inherits the AKL pointwise uniform
restriction bound and the original AJI tail-decay estimate. The
mass-squared Ward floor is the genuine AKK scalar, and the AJA ceiling
is the genuine AJX Haar/variance theorem. Each is evaluated at the same
H, beta, and physical source.

### Strict original AJA witness: certified sufficient and necessary tests

**Sufficient** at a chosen actual finite n>=1:

```text
T_(H,beta) + (q^n * ||Q^perp f0_H||)^2 < B_(H,beta)
  ==> ||S_(H,beta)^n f0_H||^2 < B_(H,beta).
```

The premise is an independent unverified numerical top-vs-Haar
comparison. This theorem is a conditional construction, not a claim that
its premise is true.

**Necessary** for any actual strict finite-power AJA witness:

```text
L_(H,beta) < B_(H,beta)
T_(H,beta) < B_(H,beta)
(15/16) * V_H < ||Q^perp f0_H||^2 .
```

These are genuine necessary tests, not new assumptions appended to the
original model. The existing AKE theorem separately gives the
finite-power-witness iff full-top energy<B characterization for beta>0.
AKM refines its small-coupling quantitative upper envelope using the
same q for all H, not a volume-dependent q_H.

### Compatible no-witness interval

For every H and positive beta satisfying both beta<=beta_* and
beta<=kappa_H=log(2)/(2p_H), AKM proves *simultaneously*

```text
||S_(H,beta)|_(full-top orthogonal)|| <= q
NOT exists n, ||S_(H,beta)^n f0_H||^2 < B_(H,beta).
```

This is not a contradiction. Coercivity removes only the excited part,
not the nonzero original full-top component. The earlier AKI theorem
specifically forbids any strict original AJA power witness at the
original beta0=log(3/2)/64 and H=0. Thus the blanket demand for
unconditional witnesses for every original H at beta0 is false.

## New exact Lean declarations

One [new AKM Lean leaf](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/37f0fd533bd4a1758215f6c612e67114834b1f2d/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUniformCoercivityAJAHaarBudgetBridgeV5_PZ37AKM.lean),
237 lines added, 0 deleted; imports certified AKL, AKE, AKK and AJX.
All five declarations have explicit `#print axioms`:

1. `p4Q2PZ37AKM_originalPower_uniformGeometricEnvelope`
2. `p4Q2PZ37AKM_originalAJA_HaarWardCoercivitySandwich`
3. `p4Q2PZ37AKM_originalAJA_witness_of_uniformEnvelope_below_budget`
4. `p4Q2PZ37AKM_originalAJA_witness_necessaryWardTopAngle`
5. `p4Q2PZ37AKM_originalUniformCoercivity_and_logarithmicAJANoGo`

All declarations are in `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`.

## Debugging and exact-source proof provenance

Initial source `a3b1781cc360f4ff6d387e763f9ae4150bd31309`,
[CI 43175247834](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43175247834):
**FAILURE**. The sole new error was an unresolved concrete
`norm_nonneg _` type in the natural-power operator norm comparison at
line 106. Two independent declarations were standard-three-only; three
dependent declarations carried error-propagated `sorryAx`, hence none
of those error-propagated terms is accepted as proof.

Second source `a067ceb205ff27d229114c45a1351455baf0829e`,
[CI 43176234582](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43176234582):
**FAILURE**. The norm type error was repaired by explicitly proving
`0 <= ||RM||`. One remaining elaboration mismatch at line 138:
`add_le_add_left` produced `tail+top`, opposite the original AJZ
Pythagoras goal `top+tail`. The corrected proof uses
`add_le_add_right` without changing any statement.

Final source `94608e9a90f36799d7586fc8447fab6f4194f673`,
[exact-source CI 43176986881](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43176986881):
**completed/SUCCESS**; actual Lean job `131043528950` built
**11,451/11,451**, all five exact complete multiline `#print axioms`
arrays equal `[propext, Classical.choice, Quot.sound]`, new
`sorryAx` absent, changed AKM warning/error 0/0. Independent
receipt job `131045584416` completed/SUCCESS, reporting exact source
SHA and `source_result=success`, `state=success`.

Source tree `a311ed1efd7e4f5931681265fc69758ead193523`;
actual test-merge `63d49dbbaf960465475163eb2ebd25eb3e363a75`
has this same tree. Formal PR
[#6686](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6686)
is MERGED as `37f0fd533bd4a1758215f6c612e67114834b1f2d`,
with the same tree and one new file only.

Pinned Lean `v4.30.0-rc2` and mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`
are unchanged. No old physical definition, hypothesis, Lean file, root,
pinned environment, workflow or witness predicate was weakened.

## Open proof obligations and boundaries

AKM does NOT prove any of the following:

- Actual unconditioned inequality `T_(H,beta)<B_(H,beta)`, or a
  numerical original finite-power AJA witness at some otherwise
  unspecified H,beta.
- Membership of the original numerical beta0 in the AKL common cutoff.
- A common finite witness exponent uniform over H; the gap `B-T`
  may be H-dependent or nonpositive.
- Positive coercivity on the full top-containing space, an unscaled
  raw-transfer H-uniform lower bound, an original GL-source Rayleigh
  lower bound, strong-limit Hamiltonian spectral gap or continuum 4D
  Yang-Mills mass gap.

The unproved original-Haar top-vs-budget comparison is retained explicitly
as an obstruction (NO_DATA), not converted to a premise of an
unconditional theorem. The AKI and AKK finite-H non-witness findings
remain valid.

append-only / tighten-only / overwrite-forbidden / same-root. Formal has
the Lean leaf and proof record. Main will receive only the identical
proof-record blob and public-document appendices, never the formal-only
Lean leaf. Documentation-only Strict Lean is not manually dispatched.
