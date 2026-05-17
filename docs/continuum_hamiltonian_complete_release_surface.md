# Continuum Hamiltonian complete release surface

This document is the reviewer-facing release surface for the physical 4D Yang--Mills continuum Hamiltonian route inside the MGAP4D MathlibAnalytic lane.

It is documentation-only. It does not create a tag. It does not replace independent replay. It does not claim external mathematical consensus. It summarizes what is now explicitly built in Lean and what remains a public external-audit boundary.

## Route summarized

```text
physical 4D Yang-Mills continuum Hamiltonian lane
  -> continuum Hamiltonian mass-gap witness hardening
  -> positive exact normalized mass-gap theorem
  -> release adoption
  -> complete mass-gap derivation
  -> complete release adoption
  -> external audit readiness gate
```

## Built Lean surfaces

The current complete release path is represented by the following Lean modules:

```text
MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapWitnessHardening
MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapTheorem
MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapReleaseAdoption
MGAP4D.MathlibAnalytic.ContinuumHamiltonianCompleteMassGapDerivation
MGAP4D.MathlibAnalytic.ContinuumHamiltonianCompleteMassGapReleaseAdoption
MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
```

The top-level theorem surface records:

```text
0 < exactGapValueReal
exactGapValueReal = (33 : Real) / 20
continuumHamiltonianMassGapWitnessData.continuumHamiltonianToMassGapChainReady
theoremWitnessOnly
noExternalConsensusClaim
publicBoundaryHeld
finalReleaseHeld
```

## CI checkpoint

```text
Repository: itakura-hidetoshi/4d-mass-gap
Pull request: #44
Branch: kuos/self-adjoint-hphys-bridge-adoption-v0-1
Head commit: a032caed7121bc14df3bf286e723cd90a76fd2cb
CI merge ref: 8a4761d7ff9ea9b1f3b9c2c0b2a3ca338dacb178
Workflow: Full Local Check CI
Workflow run ID: 25988968639
Job ID: 76391524347
Result: success
Observed timestamp: 2026-05-17T11:05:17Z
```

The same head commit also had:

```text
Bridge Coherence CI: success
Lean Direct Elan CI: success
External Audit Readiness CI: success
Full Local Check CI: success
```

## Replay summary from the green run

```text
Lean files scanned: 472
sorry/admit/axiom/constant: 0/0/0/0
Major theorem specs audited: 12
Bridge files audited: 8
Ordered import edges audited: 5
Lean replay summary imports: 1233
Lean replay summary declaration_like_lines: 2786
Lean replay summary namespace_lines: 968
Lean replay summary total_lines: 29422
Continuum Hamiltonian exact mass-gap derivation build: 8368 jobs, success
Continuum Hamiltonian release-chain addendum build: 8369 jobs, success
External audit readiness gate build: 8376 jobs, success
Final lake build: 0 jobs, success
```

## Final gate build items

The external audit readiness gate stage built the following theorem / release modules:

```text
[8368/8376] MGAP4D.MathlibAnalytic.ExactValueTheoremBodyOrigin
[8369/8376] MGAP4D.MathlibAnalytic.FourLaneResidualClosure
[8370/8376] MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapWitnessHardening
[8371/8376] MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapTheorem
[8372/8376] MGAP4D.MathlibAnalytic.InternalReviewResidualClosureGate
[8373/8376] MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapReleaseAdoption
[8374/8376] MGAP4D.MathlibAnalytic.ContinuumHamiltonianCompleteMassGapDerivation
[8375/8376] MGAP4D.MathlibAnalytic.ContinuumHamiltonianCompleteMassGapReleaseAdoption
[8376/8376] MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
```

## What this release surface means

A successful replay of this checkpoint means:

```text
the pinned Lean and mathlib lane builds
the continuum-Hamiltonian theorem surface builds
the exact normalized value 33/20 is preserved through the route
the strict positivity theorem surface builds
the release-adoption and complete-derivation surfaces build
the external-audit-readiness gate sees the complete release adoption
the audit scripts pass on the same repository state
the public-boundary and final-release-boundary markers remain explicit
```

## What this release surface does not mean

This checkpoint does not claim:

```text
external mathematical consensus
independent peer-review completion
Clay-style public final theorem acceptance
that CI output alone replaces mathematical proof review
that audit scripts replace Lean kernel checking
that the external-audit-readiness gate replaces independent replay
a dimensional physical gap without choosing the reference scale E0
```

## Normalization boundary

The exact value is dimensionless in the normalized Hamiltonian convention:

```text
H_norm = H_phys / E0
normalizedGap = physicalGap / E0
physicalGap = E0 * normalizedGap
internal normalized units: E0 = 1
exact normalized value: 33/20
```

Therefore:

```text
physicalGap_dimensional = E0 * (33/20)
```

A dimensional physical interpretation requires an external reference energy scale `E0`.

## Reviewer checklist

```text
1. Checkout the exact commit or PR merge ref listed above.
2. Confirm the pinned toolchain: Lean 4.30.0-rc2 / mathlib4 v4.30.0-rc2.
3. Run: bash scripts/check.sh
4. Confirm forbidden-token audit: sorry/admit/axiom/constant = 0.
5. Confirm major theorem non-placeholder audit passes.
6. Confirm bridge coherence audit passes.
7. Confirm continuum Hamiltonian witness hardening audit passes.
8. Confirm external audit readiness replay certificate audit passes.
9. Confirm MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate builds.
10. Record any objections as external review notes; do not treat CI success as external consensus.
```

## Boundary invariant

```text
Lean theorem surface: present
CI replay evidence: present
External audit readiness: present
Independent external audit completion: not claimed
External consensus: not claimed
Public final theorem acceptance: not claimed
```
