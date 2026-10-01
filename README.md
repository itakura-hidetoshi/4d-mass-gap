# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

**Current theorem status — through merged PR #4989:** the positive-beta finite-volume transfer-gap route remains closed with the explicit uniform floor 1/3072 and the uniform top-orthogonal power contraction q0 = 3071/3072. The common-carrier work has now advanced from merely proving conditional strong-limit preservation to auditing whether the specific independent-product carrier used in #4984 can support a nonzero strong limit of moving centered scale excitations.

PR #4988 proves the model-free Hilbert obstruction: a strongly convergent pairwise-orthogonal sequence has zero limit. PR #4989 proves the matching infinite-product geometry: distinct coordinate L² pullbacks have inner product equal to the product of their means, so centered coordinate pullbacks are pairwise orthogonal, and any strongly convergent centered fresh-coordinate sequence has zero limit.

This does **not yet prove** that every #4984 Wilson top-orthogonal image is centered relative to the interacting marginal constant-one vector. That Wilson-specific centering statement is tied to the still-open one-slab-top versus finite-OS-vacuum compatibility problem. The immediate H1 task is therefore to settle that centering/sector bridge and then construct the continuum limit in a genuinely scale-coherent carrier rather than silently treating independent scale coordinates as a continuum identification.

## Authority checkpoint — 2026-10-01 JST

| Item | Authoritative value |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Latest theorem-bearing snapshot | c46e2fad7d5a5a749e63650b7772c4d4973dc12f — merged PR #4989 |
| #4989 validated exact PR head | bee4f20f8007078ddbd6b061f64834513be674e9 |
| #4989 validation | PR Lean Fast Check run 36817103467: completed / success; exact-head completion receipt: success |
| #4989 artifact | 11141653528; sha256:9e9102467a6fe69ac43ccae7fba34b8203370966e9c3d4ff667027d1247c97a1 |
| Previous full strong-limit checkpoint | #4985 / 88870c84503e22797397f7082a1cfc9b4dc36322 |
| Lean | v4.30.0-rc2 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |

[Authoritative theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Detailed roadmap](ROADMAP.md)

The default branch main is **not theorem authority**. README / ROADMAP on main are documentation mirrors only. A docs-only merge may advance a branch pointer without changing the mathematical theorem snapshot.

Authority order is fixed:

1. fresh exact theorem-carrier SHA;
2. formal Lean artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

## Scope and current claim boundary

The repository contains the exact beta-zero endpoint

~~~text
physical transfer gap at beta = 0 = 1
~~~

and, on a nonempty positive-beta high-temperature interval, the finite-volume route now proves

~~~text
kappa_12(s,beta) * ||f - B f||^2 <= E_12(f)

1/2304 <= kappa_12(s,beta)

1/3072 <= physical top-eigenspace transfer gap

q0 = 3071/3072

||R_n^k x|| <= q0^k ||x||.
~~~

Those results are uniform in lattice scale and contain no lattice-volume, link-count or gauge-rank loss.

A complete continuum four-dimensional Yang--Mills existence and Wightman mass-gap theorem is **not yet claimed**. In particular:

- #4985 preserves the discrete contraction only under explicitly compatible strong-limit data;
- #4988/#4989 show that independent-product coordinate geometry can itself obstruct nonzero centered strong limits;
- the Wilson-specific centering relation needed to apply #4989 directly to #4984 is not yet closed;
- the one-slab normalized-transfer top sector is not silently identified with the finite periodic OS vacuum sector;
- the fixed discrete q0 is not by itself a physical continuum-time mass rate;
- the final continuum semigroup, Hamiltonian spectral gap and Wightman energy-momentum statement remain downstream.

## Closed finite-volume route

### 1. Tagged-link leakage, renewal and intrinsic constant line — #4935--#4971

The real-leakage, ordered Schur, renewal, two-boundary recurrence and all-L² tagged-link chain is closed. The endpoint is the intrinsic constant-line relative Poincaré inequality

~~~text
(1 - 2 Q) * ||f - B f||^2
  <= sum_e ||f - P_e f||^2,
0 < 1 - 2 Q.
~~~

These modules are retained dependencies and are not the active frontier.

### 2. Complete-order robustness — #4976--#4978

Because the one-link conditional expectations do not commute, the grouped twelve-color route required an explicit complete-order theorem rather than an informal reordering.

#4976 proves loss contraction for any complete duplicate-free tagged-link order. #4977 constructs the complete right-six plus left-six grouped order. #4978 proves the corresponding fixed-space, constant-projection absorption and strong convergence statements.

### 3. Genuine two-sided twelve-spatial frame — #4979--#4980

#4979 transports whole-color control across endpoint swap. #4980 proves

~~~text
kappa_12(s,beta)
  = (1 - sqrt(twoBoundaryOrderedLossRatio(s,beta)))^2 / 576

kappa_12(s,beta) * ||f - B f||^2 <= E_12(f),

0 < kappa_12(s,beta).
~~~

The factor 576 = 4 * 12² is fixed-cardinality only.

### 4. Physical centering and finite-volume gap — #4981

For a physical top-orthogonal vector x, after the Haar-to-vacuum transform U and genuine right-boundary lift R, #4981 proves

~~~text
B (R (U x)) = 0

||R(Ux) - B(R(Ux))||^2 = ||x||^2.
~~~

The existing receiver then gives

~~~text
3 * kappa_12(s,beta) / 4
  <= physical top-eigenspace transfer gap.
~~~

No global identification of the one-slab top line with the finite OS vacuum line is used here.

### 5. Explicit uniform gap and power decay — #4982--#4983

#4982 chooses a smaller common positive cutoff and proves

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= physical top-eigenspace transfer gap.
~~~

#4983 sets

~~~text
q0 = 3071/3072
~~~

and proves, uniformly in scale,

~~~text
||R_n|| <= q0 < 1
||R_n^k|| <= q0^k
||R_n^k x|| <= q0^k ||x||.
~~~

The associated -log(q0) is a discrete one-step rate only.

## H1 common-carrier work

### H1-A. Independent interacting product as a simultaneous finite-scale carrier — #4984 CLOSED

#4984 embeds every finite physical top-orthogonal sector isometrically into one interacting infinite-product boundary L² carrier by composing:

1. one-sided excitation boundary isometry;
2. reciprocal-vacuum transport to the actual interacting finite boundary marginal;
3. pullback along the corresponding product coordinate.

On every exact finite-scale image range, the transported transfer powers retain the same q0^k bound.

Important claim boundary: this carrier is a valid **kinematic simultaneous carrier**. #4984 did not prove that it is the correct continuum identification carrier.

### H1-B. Compatible strong limits preserve the gap — #4985 CLOSED

#4985 proves the sequence-level estimate

~~~text
I_n x_n -> x_limit
I_n R_n^k x_n -> y_limit

=> ||y_limit|| <= q0^k ||x_limit||.
~~~

It also defines PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryStrongLimitData and proves for any instance

~~~text
||T|| <= q0^k.
~~~

For k = 1,

~~~text
||T|| <= 3071/3072
1/3072 <= 1 - ||T||
||T|| < 1.
~~~

This theorem remains valid. What changed after #4988/#4989 is the audit of which concrete carrier can satisfy its nonzero strong-limit hypotheses.

### H1-C0. Pairwise-orthogonal strong-limit obstruction — #4988 CLOSED

#4988 proves the model-free theorem

~~~text
v_n -> x strongly
and inner(v_m, v_n) = 0 for m != n

=> x = 0.
~~~

This is the abstract Hilbert obstruction needed before interpreting any product-coordinate common carrier as a continuum limit space.

### H1-C1. Centered independent-coordinate geometry — #4989 CLOSED

#4989 proves for an arbitrary family of probability spaces that distinct coordinate pullbacks satisfy

~~~text
<I_i f, I_j g>
  = (integral f d mu_i) * (integral g d mu_j)
  for i != j.
~~~

Therefore, if f_i is centered against the coordinate constant-one vector, then the distinct coordinate pullbacks are orthogonal. Combining this with #4988 gives

~~~text
I_n f_n -> x strongly
and each f_n is centered

=> x = 0.
~~~

This is a **generic independent-product theorem**. It does not yet assert that the concrete #4984 Wilson top-orthogonal image is centered in the interacting marginal coordinate.

## Current frontier — H1-C / H1-D

The immediate problem is now a carrier-and-sector compatibility problem, not another finite-volume gap estimate.

### A. Close the Wilson-specific centering bridge

Determine and prove the exact relation between the #4984 finite top-orthogonal image and the interacting marginal constant-one vector.

The decisive statement has the form

~~~text
<1, marginalImage_n(x)> = 0
~~~

for the relevant physical excitation x.

If this is proved, #4989 applies directly and shows that moving those centered excitations through fresh independent product coordinates cannot converge strongly to a nonzero vector.

If it fails, the failure itself identifies the unresolved mismatch between the one-slab top sector and the finite OS vacuum sector and must be resolved before calling the limit physically vacuum-orthogonal.

### B. Use a genuinely scale-coherent continuum carrier

A nonzero continuum excitation limit needs embeddings that compare different scales coherently rather than putting each scale in an independent fresh coordinate.

Existing repository interfaces relevant to this step include:

- PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier, which stores gap-free isometric finite-to-continuum embeddings and vacuum preservation;
- PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer, which already expresses approximation/evolved convergence into an OS physical Hilbert space, but must be used without circularly assuming the gap conclusion being constructed;
- the same-root factorial OS direct-limit / regular vacuum-orthogonal carrier, which already has dense centered smoothed cylinder cores and finite-to-limit correlation convergence.

A fixed isometric embedding of the independent product into another Hilbert space does not by itself remove the #4989 geometry; an isometry preserves orthogonality. The cross-scale identification must therefore be introduced before, or instead of, the independent-coordinate limit presentation.

### C. Reconnect the uniform q0 estimate on that carrier

After the scale-coherent approximants are constructed, prove:

1. initial strong convergence of finite physical excitations;
2. evolved strong convergence under the finite physical top-orthogonal dynamics;
3. identification of the limiting operator on the correct vacuum-orthogonal OS sector;
4. transport of the already-proved q0^k bound to that operator.

No new finite-volume leakage/Schur/renewal estimate is required for this step.

## H1-D authority boundary — one-slab top sector vs OS vacuum sector

Do not identify by name:

- one-slab normalized-transfer top eigenspace;
- finite periodic OS vacuum line;
- canonical boundary vacuum;
- interacting marginal constant-one line;
- continuum physical vacuum line.

The mode-wise boundary closure, eigenlift and positive-half synthesis machinery can be used to prove the needed compatibility, but a global equality is not currently a theorem dependency.

## H2 continuum-scaling obstruction

The uniform fixed-step factor

~~~text
q0 = 3071/3072 < 1
~~~

is excellent for finite-volume and fixed-step comparison, but it cannot simply be used as the physical continuum-time factor when lattice spacing a_n -> 0.

For fixed t > 0,

~~~text
q0 ^ floor(t / a_n) -> 0.
~~~

That would give instantaneous collapse at every positive physical time rather than a nontrivial strongly continuous semigroup.

H2 therefore requires a spacing-scaled statement such as

~~~text
q_n = exp(-m_n a_n + o(a_n))
~~~

or an equivalent rescaled-defect / Dirichlet / generator formulation. The repository already contains floor-time, derived-rate and intrinsic-rate-to-physical-mass infrastructure for this stage.

## Downstream H3 / H4

After H1/H2 provide actual model-facing data, the intended route is

~~~text
finite-volume uniform coercivity
  -> scale-coherent continuum dynamics
  -> OS physical Hilbert + strongly continuous semigroup
  -> closed/self-adjoint Hamiltonian on the correct vacuum-orthogonal sector
  -> positive spectral gap
  -> Wightman / energy-momentum mass gap.
~~~

Substantial generic OS/Hamiltonian machinery already exists in the repository; the missing work is the model-facing compatibility and scaling data.

## Lean / CI workflow

Latest theorem validation:

~~~text
PR #4989 exact head:
  bee4f20f8007078ddbd6b061f64834513be674e9

PR Lean Fast Check:
  run 36817103467
  completed / success

exact-head completion receipt:
  success

artifact:
  11141653528
  sha256:9e9102467a6fe69ac43ccae7fba34b8203370966e9c3d4ff667027d1247c97a1
~~~

The changed theorem file passed the static forbidden-token audit and pinned Lean/mathlib compilation.

Recent Lean engineering lessons:

- inspect the complete changed module, not only the first reported line;
- preserve the pinned mathlib API rather than coding against current master;
- for dependent submodule carriers, prefer typed named theorems and local calc chains over broad change/rw;
- give reusable local instances explicit module-specific names when import composition can expose generated-name collisions;
- real L² inner-product expansion may produce the scalar factors in the opposite multiplication order; when the target is intentionally commutative, make mul_comm explicit rather than forcing elaboration through a larger rewrite;
- once an unchanged exact head is GREEN, do not rerun strict Lean validation merely for reassurance;
- docs-only README / ROADMAP updates are not theorem-bearing changes.

## Milestone map

| PR | Closed layer |
| --- | --- |
| #4976 | arbitrary complete duplicate-free tagged-link loss contraction |
| #4977 | complete grouped right-six + left-six order |
| #4978 | complete-order constant-line convergence |
| #4979 | whole left six-color displacement by endpoint swap |
| #4980 | volume-free genuine two-sided twelve-spatial relative frame |
| #4981 | physical top-orthogonal centering and positive finite-volume gap |
| #4982 | explicit uniform coefficient 1/2304 and transfer-gap floor 1/3072 |
| #4983 | uniform q0^k power decay, q0 = 3071/3072 |
| #4984 | simultaneous isometric realization in the interacting independent-product carrier |
| #4985 | conditional strong-limit preservation of q0^k and the one-step gap floor |
| #4988 | pairwise-orthogonal strongly convergent sequences have zero limit |
| #4989 | centered independent-coordinate pullbacks are pairwise orthogonal; centered fresh-coordinate strong limits are zero |

For the exact continuation sequence, see [ROADMAP.md](ROADMAP.md).

## Primary current modules

- MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopOrthogonalScaleCommonBoundaryStrongLimit.lean
- MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopOrthogonalScaleCommonBoundaryDecay.lean
- MGAP4D/MathlibAnalytic/RealHilbertPairwiseOrthogonalStrongLimit.lean
- MGAP4D/MathlibAnalytic/InfiniteProductProbabilityCoordinateL2Orthogonality.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonMassFreeAmbientTwoStepRecovery.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSApproximatingGapTransfer.lean
- MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumOrthogonal.lean
