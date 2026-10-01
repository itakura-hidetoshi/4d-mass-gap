# MGAP4D ROADMAP

## Authority checkpoint — 2026-10-01 JST

| Item | Value |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique authoritative theorem-carrier | formal/real-hilbert-uniform-coercive-strong-limit |
| Latest theorem-bearing snapshot | c46e2fad7d5a5a749e63650b7772c4d4973dc12f |
| Latest theorem merge | PR #4989 — centered scale-coordinate orthogonality in the independent product carrier |
| #4989 validated PR head | bee4f20f8007078ddbd6b061f64834513be674e9 |
| #4989 validation | PR Lean Fast Check 36817103467: completed / success; exact-head receipt success |
| Artifact | 11141653528; sha256:9e9102467a6fe69ac43ccae7fba34b8203370966e9c3d4ff667027d1247c97a1 |
| Lean | v4.30.0-rc2 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |

[Authoritative theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Overview](README.md)

The default branch main is a documentation mirror only and is not theorem authority.

Authority order:

1. fresh exact theorem-carrier SHA;
2. formal Lean artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

## 0. Current frontier

The finite-volume G route is closed and the H1 carrier audit has now exposed the next genuine obstruction.

The theorem-carrier proves, on one positive scale/volume/rank-independent interval:

~~~text
kappa_12(s,beta) * ||f - B f||^2 <= E_12(f)

B (R (U x)) = 0

1/2304 <= kappa_12(s,beta)

1/3072 <= finite-volume physical transfer gap

q0 = 3071/3072

||R_n^k x|| <= q0^k ||x||.
~~~

#4984 places all finite top-orthogonal sectors in one interacting independent-product boundary L² carrier. #4985 proves that any explicitly compatible strong limit in a common carrier preserves q0^k and the one-step gap floor.

#4988/#4989 add a new exact warning:

~~~text
pairwise orthogonal + strong convergence => zero limit

and, for independent product coordinates,

~~~text
<I_i f, I_j g>
  = mean(f) * mean(g),
i != j.
~~~

Hence a centered sequence moved through fresh independent coordinates can only have strong limit zero.

**Exact claim boundary:** #4989 is generic. It does not yet prove that the concrete #4984 Wilson top-orthogonal image is centered relative to the interacting marginal constant-one vector. Establishing that Wilson-specific centering relation is now inseparable from the one-slab-top versus OS-vacuum compatibility problem.

The active continuation is therefore:

~~~text
H1-C1 / H1-D:
  prove the Wilson-specific marginal centering / finite OS vacuum compatibility

THEN:
  if centered, use #4988/#4989 to rule out the independent-coordinate
  carrier as a nonzero strong-limit presentation

H1-C2:
  construct a genuinely scale-coherent finite-to-continuum excitation carrier

H1-C3:
  prove initial and evolved strong convergence there and transport q0^k

H2:
  replace the fixed discrete q0 by spacing-scaled dynamics

H3:
  OS semigroup / Hamiltonian reconstruction on the correct excitation sector

H4:
  spectral / Wightman mass gap.
~~~

Do not reopen the already closed leakage, Schur, renewal, twelve-color, physical-centering or uniform finite-volume gap layers unless a genuine inconsistency is found.

## 1. Closed finite-volume foundation

### 1.1 #4935--#4971 — leakage through intrinsic constant-line relative Poincaré

Closed chain:

- real square-root leakage;
- ordered RMS Schur envelope;
- terminal recurrence;
- geometric renewal and tail control;
- two-boundary propagation;
- actual two-sided leakage;
- strict full-sweep loss contraction;
- intrinsic constant-line fixed space;
- strong convergence to the constant projection;
- all-L² tagged relative Poincaré.

Endpoint:

~~~text
(1 - 2 Q) * ||f - B f||^2
  <= sum_e ||f - P_e f||^2,
0 < 1 - 2 Q.
~~~

Status: CLOSED dependency.

### 1.2 #4976--#4978 — complete-order robustness

#4976 removes dependence on the canonical list by proving the strict loss contraction for any complete duplicate-free tagged-link order.

#4977 constructs the genuine grouped right-six plus left-six order.

#4978 proves fixed-space identification, constant-projection absorption and complete-order strong convergence.

Status: CLOSED.

### 1.3 #4979--#4980 — endpoint swap and twelve-spatial frame

#4979 transports whole-color displacement control across endpoint swap.

#4980 proves

~~~text
kappa_12(s,beta)
  = (1 - sqrt(twoBoundaryOrderedLossRatio(s,beta)))^2 / 576

kappa_12(s,beta) * ||f - B f||^2 <= E_12(f),

0 < kappa_12(s,beta).
~~~

No lattice-link, volume or rank factor occurs.

Status: G1 CLOSED.

### 1.4 #4981 — physical top-orthogonal centering and finite gap

For z = R(Ux), #4981 proves

~~~text
B z = 0

||z - Bz||^2 = ||x||^2
~~~

and the receiver yields

~~~text
3 * kappa_12(s,beta) / 4
  <= physical top-eigenspace transfer gap.
~~~

Status: G2/G3 CLOSED.

### 1.5 #4982--#4983 — uniform gap and power decay

#4982 proves

~~~text
1/2304 <= kappa_12(s,beta)
1/3072 <= physical transfer gap.
~~~

#4983 sets q0 = 3071/3072 and proves

~~~text
||R_n|| <= q0
||R_n^k|| <= q0^k
||R_n^k x|| <= q0^k ||x||.
~~~

Status: G4 + uniform discrete dynamics CLOSED.

## 2. H1-A / H1-B — simultaneous carrier and conditional descent

### H1-A #4984 — simultaneous independent-product realization CLOSED

For each scale n:

~~~text
physical top-orthogonal sector
  -> shared-boundary Haar L2
  -> interacting boundary marginal L2
  -> coordinate n of the infinite product L2.
~~~

Every arrow is an exact isometry. The finite q0^k estimate survives on each exact image range.

Important: #4984 proves a common ambient presentation, not cross-scale coherence.

### H1-B #4985 — strong-limit preservation CLOSED

For any compatible data:

~~~text
I_n x_n -> x
I_n R_n^k x_n -> y

=> ||y|| <= q0^k ||x||.
~~~

The packaged one-step conclusion is

~~~text
||T|| <= 3071/3072
1/3072 <= 1 - ||T||
||T|| < 1.
~~~

#4985 remains a valid abstract descent theorem.

## 3. H1-C carrier audit — #4988/#4989

### H1-C0a #4988 — pairwise-orthogonal strong-limit obstruction CLOSED

The new generic theorem realHilbert_tendsto_zero_of_pairwise_inner_eq_zero states:

~~~text
v_n -> x strongly
and
inner(v_m, v_n) = 0 for m != n

=> x = 0.
~~~

No completeness or model-specific structure is required.

### H1-C0b #4989 — independent-coordinate L² geometry CLOSED

For probability measures mu_i, the coordinate pullbacks I_i satisfy

~~~text
<I_i f, I_j g>
  = (integral f d mu_i) * (integral g d mu_j)
  when i != j.
~~~

Therefore:

~~~text
f_i centered
=> I_i f_i pairwise orthogonal

I_n f_n -> x strongly
=> x = 0.
~~~

This is the exact kinematic obstruction for centered fresh-coordinate sequences in an independent product.

### H1-C0c — Wilson-specific applicability OPEN

The remaining question is whether the concrete #4984 scale-n physical top-orthogonal image is centered in its interacting marginal coordinate.

Target theorem shape:

~~~text
inner(1,
  HaarToMarginal(
    OneSidedExcitationBoundary(x))) = 0.
~~~

This is not merely a measure-theory lemma. It depends on how the physical one-slab top mode relates to the finite OS/boundary vacuum. Therefore it belongs at the H1-C/H1-D interface.

Two outcomes are possible:

1. **Centering holds.** Then #4988/#4989 rule out a nonzero strong limit obtained by simply moving the excitation through coordinates n = 0,1,2,... of the independent product.
2. **Centering does not yet hold.** Then the top-sector / OS-vacuum mismatch must be resolved before the limit can be claimed to live in the physical vacuum-orthogonal sector.

Either way, the independent product must not be treated as an already-established continuum identification.

## 4. Revised H1-C construction route

### H1-C1. Prove the finite Wilson centering / sector bridge — immediate

Required:

- identify the finite OS boundary vacuum image;
- compare it with the one-slab top companion mode used by #4984;
- prove the exact vacuum coefficient of the transported physical excitation;
- keep the full top eigenspace distinct from any one-dimensional vacuum line unless a theorem proves equality.

Completion criterion: a theorem deciding whether the #4984 finite image is centered relative to the marginal constant-one vector.

### H1-C2. Choose a scale-coherent limit carrier

The continuum carrier must compare different scales through actual model coherence rather than independent coordinate separation.

Relevant existing interfaces:

1. **PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier**
   - gap-free;
   - finite completed Wilson OS Hilbert -> continuum physical Hilbert isometries;
   - finite vacuum -> continuum vacuum;
   - does not itself provide approximation convergence.

2. **PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer**
   - stores finite approximation and evolved convergence into one OS physical Hilbert space;
   - already feeds generic continuum Hamiltonian gap machinery;
   - care is required to avoid circularly assuming the very gap certificate that the #4982 estimate is meant to supply.

3. **Same-root factorial OS direct-limit / regular vacuum-orthogonal carrier**
   - explicit scale-coherent/direct-limit construction;
   - dense centered positive-time-smoothed cylinder cores;
   - finite Wilson correlation convergence already available;
   - promising for a non-circular model-facing bridge if the #4982 top-orthogonal estimate can be expressed on its finite representatives.

Do not try to repair the independent product merely by applying a fixed linear isometry afterward: an isometry preserves the pairwise orthogonality established in #4989.

### H1-C3. Reconnect the q0 estimate

Once a scale-coherent carrier E and finite approximants x_n are available, prove:

~~~text
J_n x_n -> J x

J_n R_n x_n -> J(Tx)
~~~

with the actual physical finite dynamics.

Then reuse the #4983 bound and the generic limit-preservation argument to obtain

~~~text
||T|| <= 3071/3072
~~~

on the physically correct limiting excitation sector.

Completion criterion: nonzero theorem-generated model-facing limit data, not an abstract structure populated by assumptions.

## 5. H1-D — one-slab top sector versus OS vacuum sector

Keep distinct:

- one-slab normalized-transfer top eigenspace;
- full top-eigenspace orthogonal sector;
- finite periodic OS vacuum line;
- canonical boundary vacuum;
- interacting marginal constant-one vector;
- continuum physical vacuum line.

Existing mode-wise boundary closure, eigenlift, positive-half synthesis and completed-boundary-transfer machinery can be used as local bridges.

Possible routes:

- prove a global finite top/vacuum identification;
- prove only the centering relation needed by H1-C;
- bypass a global finite equality and identify the continuum vacuum-orthogonal sector directly through a scale-coherent OS construction.

Status: OPEN, immediate parallel boundary.

## 6. H2 — spacing-scaled continuum dynamics

### H2-A. Fixed q0 is not a physical continuum-time rate

With a_n -> 0 and fixed t > 0,

~~~text
q0 ^ floor(t / a_n) -> 0.
~~~

Thus fixed q0 would produce instantaneous positive-time collapse, incompatible with a nontrivial C0 semigroup.

Required target form:

~~~text
q_n = exp(-m_n a_n + o(a_n))
~~~

or an equivalent:

- rescaled one-step defect;
- Dirichlet lower bound;
- centered generator rate;
- floor-time exponential transfer statement.

Relevant existing modules include:

- PhysicalYangMillsFloorExponentialTransferTrajectory.lean
- PhysicalYangMillsDerivedDiscreteTransferRate.lean
- PhysicalYangMillsGaugeInvariantOSLiteralBoundaryPoincareDirectGap.lean
- PhysicalYangMillsGaugeInvariantOSPhysicalExcitationDirichletScalingRate.lean
- PhysicalYangMillsWilsonIntrinsicRateToPhysicalMass.lean.

Status: OPEN after H1 carrier compatibility.

## 7. H3 — OS reconstruction

After H1/H2 produce actual model data, connect to:

- continuum physical Hilbert space;
- normalized vacuum;
- strongly continuous contraction semigroup;
- symmetry/self-adjointness;
- closed Hamiltonian;
- correct vacuum-orthogonal excitation sector.

Much of the generic functional-analytic infrastructure already exists.

Status: downstream.

## 8. H4 — spectral / Wightman mass gap

Final intended route:

~~~text
finite-volume uniform coercivity
  -> scale-coherent and spacing-scaled continuum dynamics
  -> OS Hamiltonian lower bound on vacuum orthogonal sector
  -> positive spectral gap
  -> Wightman / energy-momentum mass gap.
~~~

A scale-uniform finite-volume transfer gap is not itself the final theorem.

Status: downstream.

## 9. Exact distinctions to preserve

### Beta zero versus positive beta

~~~text
gap(beta = 0) = 1
~~~

is a separate exact endpoint theorem. The positive-beta 1/3072 floor need not be sharp at beta = 0.

### Relative frame versus uniform coefficient

#4980 gives the pointwise kappa_12(s,beta). #4982 proves 1/2304 <= kappa_12 only on the smaller common uniform-gap cutoff.

### Finite gap versus discrete contraction

~~~text
gap_n >= 1/3072
<=> convenient top-orthogonal norm bound
||R_n|| <= 3071/3072.
~~~

-log(3071/3072) is a discrete step rate, not automatically a physical mass.

### Simultaneous common carrier versus scale-coherent limit carrier

#4984's infinite product contains all finite scales isometrically but separates them by independent coordinates.

#4988/#4989 show why simultaneous containment is not the same as nontrivial cross-scale strong convergence.

## 10. Validation / Lean engineering

### Latest theorem evidence — #4989

~~~text
exact PR head:
  bee4f20f8007078ddbd6b061f64834513be674e9

PR Lean Fast Check:
  36817103467
  completed / success

exact-head receipt:
  success

artifact:
  11141653528
  sha256:9e9102467a6fe69ac43ccae7fba34b8203370966e9c3d4ff667027d1247c97a1
~~~

### Lean lesson from #4989

The real L² inner product expands scalar factors in Mathlib's chosen orientation. At the failing line Lean had reduced the goal to

~~~text
G (omega j) * F (omega i) = F (omega i) * G (omega j).
~~~

The correct repair was to make real multiplication commutativity explicit with mul_comm. No independence or integration argument had to be redesigned.

Continuing workflow:

- start from fresh theorem-carrier HEAD;
- inspect the complete changed module and relevant imports;
- use pinned Lean/mathlib APIs;
- separate mathematical obstruction from elaboration/import hygiene;
- preserve source/target orientation;
- once an unchanged exact head is GREEN, do not repeat strict validation without a new reason;
- do not run theorem validation for README/ROADMAP-only changes.

## 11. Milestone ledger — #4976 through #4989

| PR | Classification | Contribution |
| --- | --- | --- |
| #4976 | Theorem | arbitrary complete duplicate-free tagged-link loss contraction |
| #4977 | Theorem | complete grouped right-six + left-six order |
| #4978 | Theorem | complete-order constant-line convergence |
| #4979 | Theorem | whole left six-color displacement by endpoint swap |
| #4980 | Theorem | volume-free genuine two-sided twelve-spatial relative frame |
| #4981 | Theorem | physical top-orthogonal centering and finite-volume gap |
| #4982 | Theorem | uniform 1/2304 coefficient and 1/3072 gap floor |
| #4983 | Theorem | uniform q0^k decay, q0 = 3071/3072 |
| #4984 | Theorem | all finite top-orthogonal sectors embedded in one independent interacting product L² |
| #4985 | Theorem | compatible strong limits preserve q0^k and the one-step gap floor |
| #4988 | Theorem | pairwise-orthogonal strong-limit obstruction |
| #4989 | Theorem | centered independent-coordinate L² pullbacks are orthogonal; centered fresh-coordinate strong limits vanish |

## 12. Restart sequence

Freshly re-observe:

~~~text
formal/real-hilbert-uniform-coercive-strong-limit
~~~

The theorem-bearing checkpoint documented here is:

~~~text
c46e2fad7d5a5a749e63650b7772c4d4973dc12f
~~~

Read in this order:

1. InfiniteProductProbabilityCoordinateL2Orthogonality.lean (#4989);
2. RealHilbertPairwiseOrthogonalStrongLimit.lean (#4988);
3. PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopOrthogonalScaleCommonBoundaryStrongLimit.lean (#4985);
4. PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopOrthogonalScaleCommonBoundaryDecay.lean (#4984);
5. PhysicalYangMillsWilsonInteractingBoundaryScaleCommonVacuumCarrier.lean;
6. PeriodicHypercubicEvenOSBoundaryOneSidedExcitationTransfer.lean;
7. PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2PhysicalVacuumSector.lean;
8. PhysicalYangMillsWilsonMassFreeAmbientTwoStepRecovery.lean;
9. PhysicalYangMillsGaugeInvariantOSApproximatingGapTransfer.lean;
10. same-root factorial OS direct-limit regular vacuum-orthogonal modules;
11. only then return to #4983/#4982 if a finite estimate dependency must be inspected.

Current restart target:

~~~text
CURRENT CLOSED:
  G1--G4
  uniform q0^k finite dynamics
  #4984 simultaneous independent-product carrier
  #4985 abstract compatible strong-limit preservation
  #4988 pairwise-orthogonal strong-limit obstruction
  #4989 centered independent-coordinate orthogonality

NEXT:
  Wilson-specific centering / one-slab-top vs OS-vacuum bridge

THEN:
  scale-coherent nonzero continuum excitation carrier
  + initial/evolved convergence
  + q0 transport

THEN H2:
  spacing-scaled rate and nontrivial continuum-time dynamics

LATER:
  H3 OS Hamiltonian
  H4 spectral/Wightman mass gap.
~~~

Do not reopen #4980--#4985, #4988 or #4989 unless a concrete inconsistency is found.
