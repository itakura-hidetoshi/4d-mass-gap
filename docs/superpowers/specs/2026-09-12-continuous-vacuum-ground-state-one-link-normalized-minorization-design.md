# Continuous-vacuum ground-state one-link normalized minorization design

## Authority

- Repository: `itakura-hidetoshi/4d-mass-gap`
- Canonical base branch: `formal/real-hilbert-uniform-coercive-strong-limit`
- Exact base SHA: `70c3807698e5353eb58ef90c31be491886cf54ff`
- Predecessor theorem unit: PR #3894, complete continuous-vacuum ground-state one-link weight pairwise Harnack.

## Goal

Normalize the exact complete continuous-vacuum ground-state one-link weight over normalized compact Haar measure and prove sharp volume-independent density and measure comparison with factor `exp (16 * beta)`, without the avoidable squared loss from an anchored `m / M` argument.

## Mathematical route

Let `w` denote the complete `ENNReal` one-link weight from PR #3894 and

`R = ENNReal.ofReal (Real.exp (16 * beta))`.

PR #3894 gives, for all `g h`,

`w g <= R * w h`.

With normalized Haar probability `mu`, define

`Z = ∫⁻ g, w g ∂mu`.

Integrating the pairwise comparison in the first variable gives

`Z <= R * w h`.

Swapping the pairwise comparison and integrating gives

`w h <= R * Z`.

Pointwise strict positivity and finiteness of `w h`, together with the two inequalities, give `0 < Z < ∞`. Hence the normalized density

`rho h = w h / Z`

is well-defined and satisfies

`R⁻¹ <= rho h <= R`.

Consequently the normalized fiber measure satisfies

`R⁻¹ • mu <= mu_fiber <= R • mu`.

The proof must use the pairwise Harnack directly. Do not replace it by anchor bounds `w(h)/R <= w(g) <= R*w(h)` followed by generic `m/M`, because that loses an unnecessary second factor and yields `exp (-32 * beta)`.

## Lean structure

Create one focused file:

`MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkNormalizedMinorization.lean`

It imports the PR #3894 Harnack file and `DoobWeightedConditionalMeasureComparison`.

The file should define the exact Haar normalization mass, normalized density, and normalized measure for the complete continuous-vacuum ground-state one-link weight. It should prove AEMeasurability/continuity as required, the two denominator inequalities, positive finite normalization mass, probability status, sharp normalized density lower/upper bounds, and corresponding Haar measure minorization/majorization.

## Boundary

This unit does not prove or claim:

- a global Poincare inequality;
- a joint conditional-variance theorem;
- six-color/twelve-spatial globalization;
- a spectral gap;
- a continuum mass gap;
- an RCD identification;
- any weakening of existing hypotheses.

## Verification

The PR remains Draft while CI runs. Success may be claimed only after the exact PR head has terminal `PR Lean Fast Check = completed / success`. During an active CI run, keep write-freeze. On failure, inspect only the first genuine Lean error and make the smallest proof-shape correction.