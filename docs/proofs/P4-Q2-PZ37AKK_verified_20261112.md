# P4-Q2-PZ37AKK — squared Haar mass Ward floor for the genuine full top

## Certified scope

For each original finite `H : ℕ` and `β > 0`, use the unchanged SU(2) Wilson physical transfer `P`, its existing normalization `S = ‖P‖⁻¹ • P`, original signed centered ZW source `f₀`, normalized Haar measure, and complete top eigenspace projection `Q`. Write

$$
\lambda=\|P\|,\quad
c=Z_H(\beta)e^{-\beta p_H}r(\beta)^4,\quad
d=\beta e^{-3\beta p_H}V_H,\quad
L=\frac{d^2\lambda}{(\lambda-c)^2}.
$$

Here `Z_H(β)` denotes AIF's `p4Q2PZ37AIF_originalCrossingPartition H β`, and `r(β)` is ABN's original temporal Wilson coefficient. The scalars `c` and `d` are exactly AKI's existing original affine coefficient and Ward floor. The new auxiliary scalar `L` is a bound, not a new source, transfer normalization or Haar budget.

[The new Lean leaf](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/93ce9c8ad2f90904be598661f39161579c1a8447/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalMassSquaredWardFullTopFloorV5_PZ37AKK.lean) proves, without an additional physical hypothesis,

$$
0<\lambda-c,\qquad
d^2<L\le\|Qf_0\|^2\le\|S^n f_0\|^2
\quad\text{for every }n\in\mathbb N.
$$

The strict improvement over AKI's `d²` holds at every finite `H,β>0`, including couplings beyond the logarithmic cutoff. This does not by itself decide a new coupling or interval.

For the **unchanged original** AJA Haar budget
`B = m² · μ{A : u(A) < -m}`, the leaf also proves:

- `B ≤ L` implies that no natural power has energy strictly below `B`;
- an actual strict finite-power witness implies `L < B`.

The reverse implication is not claimed. In particular, the sign of `B - ‖Qf₀‖²` at `H=1` and the original fixed `β₀=log(3/2)/64` remains unproved here.

## Proof and same-root descent

1. Export the original estimate `λ ≤ I²`, where `I=∫ψ dμ` for the genuine nonnegative unit top eigenvector. This is the unweakened kernel-pairing estimate already inside AKG's proof; the old theorem and file remain untouched.
2. Retain AKJ's original affine pairing `(λ-c) F ≤ -d I`, with `F=⟨f₀,ψ⟩`. Existing `λ≤I`, `λ>0`, `d>0`, and `c≤λ` give `I>0` and then `λ-c>0`.
3. Square `d I ≤ (λ-c)(-F)` with its nonnegative left side, combine with `λ≤I²`, and divide by the positive squared denominator to obtain `L≤F²`.
4. Derive `Sψ=ψ` directly from the same original eigen-equation. This proves `ψ∈Top`; AJE's bound for **any** full-top vector gives `F²≤‖Qf₀‖²`. The proof does not identify `ψ` with the separately selected vacuum vector.
5. AJH's genuine full-top invariance supplies the lower bound for all natural powers, including `n=0`.
6. AIV already gives `0<λ<1`. Together with `c≥0`, this implies `(λ-c)²≤λ²<λ`, hence the strict comparison `d²<L`.

The new proof does not use top simplicity. No H-uniform positive floor, Hamiltonian spectral gap, thermodynamic-limit conclusion or continuum four-dimensional mass gap follows.

## Exact-source and independent formal-push evidence

[Theorem PR #6681](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6681) is merged. The source, actual PR test-merge and formal squash have the same Git tree.

| Object | Exact value |
|---|---|
| Canonical base | `c719c38beef68ae5dc489d91dfd16ad05ebb1f8f` |
| Source HEAD | `93ce9c8ad2f90904be598661f39161579c1a8447` |
| Actual test-merge | `5452166017dcd90faf895f1e59cc9a6019a465e8` |
| Formal squash | `e8fe2efec0413cc346fcd0e10c4b4d6472405c7c` |
| Common Git tree | `23315c7084b766284aae2865f49ff40e026c1457` |
| New Lean leaf blob | `5474c918678d85effa4529a4782c9bfced1b309a` |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

| Audit | Exact-source PR CI | Independent formal push CI |
|---|---|---|
| Workflow | [43161340043](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43161340043) | [43162137343](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43162137343) |
| Actual Lean job | `130993013711` | `130995580380` |
| Independent receipt job | `130995026749` | `130997690571` |
| Workflow / Lean job / step 17 / receipt | completed/SUCCESS | completed/SUCCESS |
| Dependency-aware build | 11449/11449 | 11449/11449 |
| New declaration axiom audits | 10/10 | 10/10 |
| Permitted axiom set | only `propext, Classical.choice, Quot.sound` | only `propext, Classical.choice, Quot.sound` |
| Changed AKK warning/error | 0/0 | 0/0 |
| `sorryAx` in actual job log | absent | absent |

The complete decoded job logs were inspected, including the target build and actual axiom output for every new named declaration. Post-build diagnostics/cache processing and the separate exact-SHA receipt completed successfully. Receipt logs identify the corresponding source/squash SHA and `source_result=success`; commit status agrees. The warning/error zero claim is scoped to the changed AKK leaf, not all historical dependencies.

The theorem PR adds exactly one leaf (309 lines) and deletes or modifies no existing Lean file. The formal record and public appendices are published separately. Main receives the identical proof-record blob and identical README/ROADMAP suffix, without this formal-only Lean leaf.

## Provenance correction: existing finite-volume top simplicity

A blanket statement that finite-volume top simplicity is absent or unproved is not consistent with the canonical source. The existing declaration
`periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_nonnegativeTopEigenvector`
has parameters `H,N : ℕ`, `0<N`, `β≥0`, and concludes that the same normalized physical Wilson full-top eigenspace equals the span of its nonnegative top vector. Simplicity is its conclusion, not a hypothesis.

That separate target was successfully built in [PR #5012](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5012), [run 36942001703](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/36942001703), job `110635772977`, at source `c0adda9073015aa1a6a26b95b6b4503f530f5440`: the actual log reports its target built and `Build completed successfully (8511 jobs)`. At the inspected canonical base, [the theorem file](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c719c38beef68ae5dc489d91dfd16ad05ebb1f8f/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceSimplicity.lean) is still blob `7ee74428ebd35cf87facc7bf97870ea16cd92f05`; the inspected Lean, manifest and Lake configuration blobs also match that historical source.

This is a correction of the inherited scope description, supported by the existing finite-volume theorem and its historical build. It does **not** claim a fresh current-head replay of that separate target, equality of its entire historical/current transitive source closure, or a theorem-specific axiom audit for it. AKK invokes none of its simplicity conclusions. The actual AJA budget difference and the uniform/continuum gap questions are separate.

## Preserved boundaries

- Original Wilson/Haar/ZW/AJA definitions, assumptions and source roots are unchanged.
- Lean/mathlib pins and heartbeat settings are unchanged.
- The AKF abstract scalar model remains distinct from this genuine Wilson result.
- A necessary floor comparison is not promoted to a witness construction.
- Append-only / tighten-only / overwrite-forbidden / same-root are retained.

Recorded after both complete CI audits on 2026-11-12 JST.
