# MGAP4D ROADMAP

## Authority checkpoint — 2026-10-02 JST

| Item | Value |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique authoritative theorem-carrier | formal/real-hilbert-uniform-coercive-strong-limit |
| Latest theorem-bearing snapshot | 382f73aa90ab24d7b02285012bf6e5513ad62a41 |
| Latest theorem merge | PR #5018 — canonical-sign OS vacuum pair independently endpoint-gauge fixed |
| #5018 validated PR head | 99d2e1c208654ee29f58ca1bc948b4baa9595cdd |
| #5018 validation | PR Lean Fast Check 36991129671: completed / success; exact-head receipt success |
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

README / ROADMAP-only merges are docs-only. They may move a branch pointer but do not replace the theorem-bearing snapshot above.

## 0. Current frontier in one page

The finite-volume gap problem is not the active bottleneck anymore.

The theorem carrier already proves

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= finite-volume physical transfer gap

q0 = 3071/3072

||R_n^m x|| <= q0^m ||x||.
~~~

The uniform q0^m estimate is available on the full completed physical pair non-top sector.

The current H1-D problem is now a two-seam compatibility problem for the canonical-sign finite OS vacuum pair.

### CLOSED through #5018

~~~text
finite-volume q0^m
  -> full physical pair non-top q0^m                         #5006

explicit SU(N) two-mode centered boundary vector             #5008
  -> pair carrier + top-top orthogonality residuals          #5009
  -> top eigenspace is one-dimensional                       #5012
  -> pair top-top sector is one selected line                #5013/#5016
  -> uncentered plaquette pair is physical                   #5015
  -> only finite OS vacuum alignment remains                 #5015
  -> alignment reduced to carrier + one-vector transfer      #5016
  -> canonical-sign OS vacuum = concrete boundary vacuum     #5017
  -> vacuum pair is independently endpoint-gauge fixed       #5018
~~~

### NEXT

~~~text
H1-D4:
  independent endpoint gauge-fixed pair
    -> completed physical pair carrier

H1-D5:
  normalized physical pair transfer
    = completed OS boundary transfer
  on the single canonical-sign OS vacuum pair

H1-D6:
  combine #5016 + H1-D4 + H1-D5
    -> vacuum pair lies on selected pair-top line
    -> explicit centered SU(N) two-mode q0^m decay
       with no arbitrary compatibility package
~~~

### THEN

~~~text
H1-C3:
  projective initial/evolved coherence
  + q0 transport to the nonzero projective continuum excitation

H2:
  spacing-scaled rate / generator / Dirichlet statement

H3:
  OS semigroup + Hamiltonian on the correct vacuum-orthogonal sector

H4:
  spectral / Wightman mass gap
~~~

Do not reopen the closed leakage, Schur, renewal, twelve-spatial, finite-gap, top-simplicity or uncentered-pair-physicality layers unless a concrete inconsistency is found.

## 1. Closed finite-volume foundation

### 1.1 #4935--#4971 — leakage through intrinsic constant-line Poincare

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
- all-L2 tagged relative Poincare.

Endpoint:

~~~text
(1 - 2 Q) * ||f - B f||^2
  <= sum_e ||f - P_e f||^2,

0 < 1 - 2 Q.
~~~

Status: CLOSED dependency.

### 1.2 #4976--#4980 — complete-order and genuine twelve-spatial frame

#4976 removes dependence on one canonical link order.

#4977 constructs the complete right-six plus left-six grouped order.

#4978 proves fixed-space identification, constant-projection absorption and complete-order strong convergence.

#4979 transports whole-color displacement across endpoint swap.

#4980 proves

~~~text
kappa_12(s,beta)
  = (1 - sqrt(twoBoundaryOrderedLossRatio(s,beta)))^2 / 576

kappa_12(s,beta) * ||f - B f||^2 <= E_12(f),

0 < kappa_12(s,beta).
~~~

Status: CLOSED.

### 1.3 #4981--#4983 — physical centering, explicit gap floor and q0

#4981 proves the physical top-orthogonal centering identity required by the finite receiver.

#4982 proves

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= physical top-eigenspace transfer gap.
~~~

#4983 sets

~~~text
q0 = 3071/3072
~~~

and proves uniform discrete power decay.

Status: CLOSED.

## 2. H1-A/H1-B carrier audit

### 2.1 #4984 — simultaneous independent-product carrier CLOSED

Every finite top-orthogonal sector has an exact isometric realization in one interacting independent-product boundary L2 carrier.

This is useful for simultaneous finite-scale comparison.

It is not a scale-coherent continuum identification.

### 2.2 #4985 — conditional strong-limit preservation CLOSED

If initial and evolved finite vectors converge strongly through compatible embeddings, the q0^m estimate survives the limit.

This remains a valid abstract descent theorem.

### 2.3 #4988/#4989 — independent-coordinate obstruction CLOSED

#4988 proves:

~~~text
pairwise orthogonal + strong convergence => zero limit.
~~~

#4989 proves for distinct product coordinates:

~~~text
<I_i f, I_j g> = mean(f) * mean(g).
~~~

Hence centered fresh-coordinate images are pairwise orthogonal and cannot have a nonzero strong limit.

### 2.4 #4992 — exact Wilson applicability obstruction CLOSED

#4992 isolates the exact top-boundary-vacuum compatibility under which the #4984 Wilson images are centered in the interacting marginal carrier.

The theorem does not assume the compatibility; it proves its exact consequence.

Status: CLOSED obstruction theorem, compatibility itself moved into H1-D.

## 3. H1-C scale-coherent projective carrier

### 3.1 #4993 — projective finite OS scale coherence CLOSED

The finite OS Hilbert spaces are embedded into one projective-limit L2 carrier through actual finite boundary marginals.

Exact finite-marginal transition coherence implies exact equality of continuum images across scales.

Therefore a coherent nonzero finite sequence has a nonzero strong limit automatically.

### 3.2 #4994/#4995 — SU(2) primary-plaquette projective strong limits CLOSED

The projective construction is specialized to primary-plaquette finite OS states.

Vacuum-centering is shown to commute with projective embedding under the finite vacuum-unit compatibility.

### 3.3 #4997 — nonzero centered witness CLOSED

A concrete nonzero centered projective excitation witness is generated.

### 3.4 #4998 — SU(N) centered nonzero projective strong-limit theorem CLOSED

For the generic SU(N) primary-plaquette Haar-mode cylinder data, actual finite OS vacuum-orthogonal states admit a nonzero projective strong limit.

Important claim boundary:

- this is a true scale-coherent strong-limit theorem;
- it depends on the projective cylinder/readout package and vacuum-unit compatibility;
- it does not yet identify the finite q0 transfer with the projective continuum Euclidean-time evolution.

### 3.5 #4999--#5003 — concrete SU(N) two-mode realization lane

The abstract SU(N) projective mode family is reduced toward explicit Wilson data:

- #4999: nonconstant Wilson-energy witness;
- #5000: two explicit orthonormal Haar modes;
- #5001: only the first two modes are needed;
- #5002: continuous boundary representatives;
- #5003: pointwise coherent readout reduction.

Status: kinematic/model-facing mode construction substantially closed; dynamic q0 compatibility remains tied to H1-D.

## 4. Full physical pair q0 route

### 4.1 #5004/#5005 — first one-sided bridge

#5004 transports q0 decay to the represented one-sided boundary sector.

#5005 bridges the concrete SU(N) two-mode finite OS state to that lane through an explicit compatibility package.

This route remains valid but is no longer the preferred endpoint.

### 4.2 #5006 — full physical pair non-top q0 CLOSED

The uniform decay theorem is lifted to the full completed physical pair non-top sector.

Target estimate:

~~~text
||S_2^m x|| <= q0^m ||x||
~~~

for every x in the completed physical pair non-top block.

This removes the need to force concrete data into one selected one-sided factorization.

### 4.3 #5007 — compatibility from range + raw kernel CLOSED

The earlier arbitrary compatibility package is theorem-generated from:

1. centered boundary range membership;
2. a literal raw one-slab matrix coefficient identity.

### 4.4 #5008 — explicit centered finite OS boundary formula CLOSED

The concrete centered boundary vector is exposed as

~~~text
finiteVacuumCentered
  (J Omega_OS)
  (explicit primary-plaquette two-mode boundary Haar vector).
~~~

This makes the top/vacuum issue explicit instead of hiding it.

### 4.5 #5009 — full-pair residual formulation CLOSED

To obtain q0^m for the explicit centered pair vector it is enough to prove:

~~~text
x_centered ∈ PhysicalPairCarrier

x_centered ∈ TopTop^perp.
~~~

Status: CLOSED bridge.

## 5. H1-D top-sector rigidity

### 5.1 #5010 — nonnegative top-mode strict positivity CLOSED

Every nonzero nonnegative full-top vector is strictly positive almost everywhere.

### 5.2 #5011 — sign rigidity CLOSED

Every unit full-top vector has one fixed sign almost everywhere.

The proof uses:

- physical absolute-value domination;
- equality at the operator norm;
- strict positivity of nonzero nonnegative top modes.

### 5.3 #5012 — finite-volume top eigenspace simplicity CLOSED

Exact theorem:

~~~text
TopEigenspace
  = span(canonical nonnegative top mode)
  = span(chosen normalized top eigenvector).
~~~

Consequences:

- top eigenspace is one-dimensional;
- no external simplicity hypothesis remains;
- full top-orthogonal sector equals the older chosen-top excitation sector.

This closes the earlier Perron-Frobenius-style uniqueness gap.

### 5.4 #5013 — pair top-top orthogonality scalarized CLOSED

The one-slice simplicity theorem is lifted to the pair sector.

Completed top-top orthogonality becomes

~~~text
x ∈ TopTop^perp
  <=> <Omega_top tensor Omega_top, x> = 0.
~~~

Status: CLOSED.

## 6. H1-D concrete SU(N) residual reduction

### 6.1 #5014 — residuals reduced to vacuum alignment CLOSED

For the explicit centered two-mode vector, the remaining pair-side problem is reduced to:

1. uncentered primary-plaquette pair physicality;
2. finite OS vacuum-pair alignment with the selected top-pair line.

### 6.2 #5015 — uncentered pair physicality CLOSED

The uncentered primary-plaquette boundary mode is proved in pair coordinates to be

~~~text
physical primary-slice plaquette mode
  tensor
physical constant-one mode.
~~~

Therefore it lies in the completed physical pair carrier.

After this PR the only structural residual is finite OS vacuum alignment.

### 6.3 #5016 — vacuum alignment reduced to two concrete seams CLOSED

#5016 upgrades the pair top-top block to the exact line identity

~~~text
TopTopClosure = span(Omega_top tensor Omega_top).
~~~

It also proves the finite OS vacuum pair is fixed by the completed OS boundary transfer.

Therefore old vacuum alignment follows from:

~~~text
A. OS vacuum pair ∈ PhysicalPairCarrier

B. NormalizedPhysicalPairTransfer vacuumPair
     =
   PairCoordinateCompletedOSBoundaryTransfer vacuumPair.
~~~

Only one-vector transfer compatibility is required. No global operator equality is needed.

The resulting theorem already reconnects these hypotheses to the q0^m estimate.

## 7. Canonical-sign finite OS vacuum — #5017/#5018

### 7.1 #5017 — concrete boundary-vacuum identification CLOSED

The coherent positive-half square root has a scale-wise sign freedom on the unit observable.

The existing vacuumNormalized construction removes this sign freedom while preserving the reflected quadratic observable.

For Q.vacuumNormalized:

~~~text
J_n Omega_OS
  = periodicHypercubicEvenBoundaryVacuumL2.
~~~

The concrete Wilson boundary vacuum is also fixed by every full finite-lattice boundary gauge pullback.

Thus the finite OS vacuum is no longer an abstract boundary vector in the canonical-sign lane.

### 7.2 #5018 — independent endpoint gauge fixedness CLOSED

The reflection-fixed boundary is decomposed exactly into primary and antipodal spatial slices.

For arbitrary one-slice gauge transformations gamma_L and gamma_R, #5018 constructs one full-lattice extension and proves exact coordinate intertwining:

~~~text
boundary gauge action
  <-> independent pair action
      (gamma_L on primary,
       gamma_R on antipodal).
~~~

Consequently the canonical-sign explicit OS vacuum pair is fixed by arbitrary independent endpoint gauge transformations.

Status: CLOSED.

## 8. Immediate next work

### H1-D4 — identify the independent gauge-fixed pair sector with the physical pair carrier

Current exact input:

~~~text
vacuumPair is fixed by every
(gamma_L, gamma_R).
~~~

Current physical pair carrier:

~~~text
PhysicalPairCarrier
  =
closure(span {
  f tensor g |
  f one-slice Gauss-law physical,
  g one-slice Gauss-law physical
}).
~~~

Required theorem:

~~~text
IndependentEndpointGaugeFixedPairSector
  =
PhysicalPairCarrier
~~~

or at minimum

~~~text
canonicalSignVacuumPair ∈ PhysicalPairCarrier.
~~~

This should be treated as a Hilbert/tensor/fixed-subspace theorem, not as new Wilson dynamics.

Suggested proof route:

1. use the one-slice Gauss-law star projection;
2. tensor the two one-slice physical projections;
3. identify the range with the closure of decomposable physical tensors;
4. prove the common fixed space of independent endpoint gauge pullbacks is that range;
5. apply #5018 to the canonical-sign vacuum pair.

Completion criterion: theorem-generate
PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairPhysicalCarrier
for Q.vacuumNormalized.

### H1-D5 — close the one-vector transfer seam

Required theorem at each scale n:

~~~text
NormalizedPhysicalPairTransfer
  (canonicalSignVacuumPair)
=
PairCoordinateCompletedOSBoundaryTransfer
  (canonicalSignVacuumPair).
~~~

#5016 already proves

~~~text
PairCoordinateCompletedOSBoundaryTransfer
  (canonicalSignVacuumPair)
=
canonicalSignVacuumPair.
~~~

Therefore H1-D5 immediately yields normalized physical pair fixedness.

Possible proof inputs already present in the repository:

- exact completed boundary transfer on represented OS states;
- realizable one-step Wilson synthesis / raw kernel formulas;
- pair-coordinate completed-boundary-transfer wrappers;
- full top-sector simplicity from #5012;
- exact finite Wilson kernel positivity.

Do not replace this one-vector target by an unnecessarily global all-input operator equality.

### H1-D6 — close vacuum alignment and explicit centered q0^m

After H1-D4 and H1-D5:

~~~text
vacuumPair ∈ PhysicalPairCarrier
vacuumPair fixed by normalized pair transfer
  -> vacuumPair ∈ TopTopClosure
  -> vacuumPair ∈ span(pairTop)
~~~

using #5016.

Then #5015 supplies the uncentered carrier statement and #5009 supplies the centered full-pair q0 theorem.

Completion criterion:

~~~text
||S_{2,n}^m y_{k,n}||
  <= q0^m ||y_{k,n}||
~~~

for the explicit centered SU(N) two-mode finite OS vectors, with only the already theorem-generated canonical-sign data.

## 9. H1-C3 — projective dynamics after H1-D

The projective carrier already supports nonzero centered strong limits.

The next task is to transport the finite dynamics, not to build another carrier.

Required:

1. choose the explicit two-mode finite OS centered sequence;
2. prove its projective transition coherence;
3. prove the finite evolved sequence has compatible projective transitions or strong convergence;
4. identify the limiting projective operator on the centered continuum mode;
5. pass the q0^m estimate to that operator.

The #4984 independent product is not the target carrier for this step.

Completion criterion:

~~~text
J_n y_n -> y != 0

J_n S_{2,n}^m y_n -> T^m y

||T^m y|| <= q0^m ||y||.
~~~

This is still discrete-time continuum-carrier control, not yet a physical-time mass gap.

## 10. H2 — spacing-scaled continuum dynamics

### H2-A — fixed q0 is not a continuum-time mass rate

If a_n -> 0 and t > 0 is fixed,

~~~text
q0 ^ floor(t / a_n) -> 0.
~~~

Therefore the fixed finite-step factor would collapse every positive physical time instantly.

Required target form:

~~~text
q_n = exp(-m_n a_n + o(a_n))
~~~

or an equivalent lower bound for a rescaled defect / Dirichlet form / generator.

Relevant existing modules include:

- PhysicalYangMillsFloorExponentialTransferTrajectory.lean
- PhysicalYangMillsDerivedDiscreteTransferRate.lean
- PhysicalYangMillsGaugeInvariantOSLiteralBoundaryPoincareDirectGap.lean
- PhysicalYangMillsGaugeInvariantOSPhysicalExcitationDirichletScalingRate.lean
- PhysicalYangMillsWilsonIntrinsicRateToPhysicalMass.lean

Status: OPEN after H1-D and projective dynamic coherence.

## 11. H3 — OS reconstruction

After H1/H2 provide actual model data:

- continuum physical Hilbert space;
- normalized vacuum;
- strongly continuous contraction semigroup;
- symmetry / self-adjointness;
- closed Hamiltonian;
- correct vacuum-orthogonal excitation sector.

The generic functional-analytic infrastructure is largely present.

Status: downstream.

## 12. H4 — spectral / Wightman mass gap

Final intended route:

~~~text
finite-volume uniform coercivity
  -> scale-coherent projective excitation dynamics
  -> spacing-scaled continuum semigroup
  -> OS Hamiltonian lower bound on vacuum orthogonal sector
  -> positive spectral gap
  -> Wightman / energy-momentum mass gap.
~~~

A scale-uniform finite-volume transfer gap is not by itself the final theorem.

## 13. Exact distinctions to preserve

### Finite OS vacuum versus one-slab top mode

#5012 proves the one-slab top eigenspace is one-dimensional.

It does not by itself identify the finite periodic OS vacuum pair with the selected one-slab pair-top vector.

That identification still passes through H1-D4/H1-D5.

### Gauge fixedness versus physical pair carrier membership

#5018 proves arbitrary independent endpoint gauge fixedness.

The repository has not yet proved that this fixed space equals the closure of decomposable one-slice Gauss-law physical tensors.

Do not silently identify them before H1-D4 is formalized.

### Completed OS boundary transfer versus normalized physical pair transfer

#5016 proves the completed OS boundary transfer fixes the finite OS vacuum pair.

It does not yet prove the normalized physical pair transfer is the same operator on that vector.

That is H1-D5.

### Projective nonzero strong limit versus evolved q0 limit

#4998 gives a nonzero centered projective strong limit under the projective cylinder/readout data.

It does not yet prove that the finite q0 transfer powers converge to the same projective continuum dynamics.

That is H1-C3.

### Fixed q0 versus physical mass

~~~text
-log(3071/3072)
~~~

is a discrete one-step rate.

It is not automatically the physical continuum mass.

## 14. Validation / Lean engineering

Latest theorem evidence:

~~~text
PR #5018 exact head:
  99d2e1c208654ee29f58ca1bc948b4baa9595cdd

PR Lean Fast Check:
  36991129671
  completed / success

exact-head receipt:
  success

merged theorem-bearing snapshot:
  382f73aa90ab24d7b02285012bf6e5513ad62a41
~~~

Recent Lean lessons from #5005--#5018:

- anonymous local instances can collide after import composition; use explicit module-specific names;
- section variables absent from a declaration body may disappear from the declaration signature;
- theorem-header metavariables must be resolved before proof-body information can help;
- do not rely on dot notation through local notation for submodule methods;
- make subtype-to-ambient Lp norm/coercion boundaries explicit;
- congrArg on a typed scalar map is often more robust than simp-heavy scalar cancellation;
- pointwise Lp addition/subtraction should be crossed through named coeFn theorems rather than forced by change;
- preserve the pinned mathlib API;
- inspect the full changed file, not only the first reported compiler line;
- once the exact head is GREEN, do not rerun strict Lean without a new code change;
- docs-only README / ROADMAP updates are not theorem-bearing changes.

## 15. Milestone ledger — #4992 through #5018

| PR | Classification | Contribution |
| --- | --- | --- |
| #4992 | Theorem | top-boundary-vacuum centering obstruction |
| #4993 | Theorem | projective finite OS scale coherence |
| #4994 | Theorem | SU(2) primary-plaquette projective strong limit |
| #4995 | Theorem | projective finite vacuum-centering |
| #4997 | Theorem | nonzero centered projective excitation witness |
| #4998 | Theorem | generic SU(N) centered nonzero projective strong limit |
| #4999 | Theorem | explicit nonconstant SU(N) Wilson-energy witness |
| #5000 | Theorem | explicit SU(N) Wilson Haar two-mode orthonormal family |
| #5001 | Theorem | reduce to two concrete Wilson modes |
| #5002 | Theorem | continuous SU(N) two-mode boundary representatives |
| #5003 | Theorem | pointwise coherent readout reduction |
| #5004 | Theorem | one-sided boundary q0 decay |
| #5005 | Theorem | concrete SU(N) two-mode finite OS q0 bridge |
| #5006 | Theorem | full physical pair non-top q0^m |
| #5007 | Theorem | compatibility generated from range + raw kernel |
| #5008 | Theorem | explicit centered finite OS boundary formula |
| #5009 | Theorem | full-pair centered q0 bridge |
| #5010 | Theorem | nonnegative top modes strictly positive |
| #5011 | Theorem | top-mode sign rigidity |
| #5012 | Theorem | finite-volume top eigenspace simplicity |
| #5013 | Theorem | pair top-top scalar criterion |
| #5014 | Theorem | residuals reduced to vacuum alignment |
| #5015 | Theorem | uncentered primary-plaquette pair physical |
| #5016 | Theorem | vacuum alignment reduced to carrier + one-vector transfer seam |
| #5017 | Theorem | canonical-sign OS vacuum = concrete gauge-fixed boundary vacuum |
| #5018 | Theorem | canonical-sign OS vacuum pair independently endpoint-gauge fixed |

PR #4996 was closed without merge and is not part of theorem authority.

## 16. Restart sequence

Freshly re-observe:

~~~text
formal/real-hilbert-uniform-coercive-strong-limit
~~~

The theorem-bearing checkpoint documented here is:

~~~text
382f73aa90ab24d7b02285012bf6e5513ad62a41
~~~

Read in this order for the current frontier:

1. PhysicalYangMillsWilsonVacuumNormalizedPairIndependentGaugeFixed.lean — #5018;
2. PhysicalYangMillsWilsonVacuumNormalizedBoundaryGaugeFixed.lean — #5017;
3. PhysicalYangMillsWilsonSUNTwoModeFiniteOSVacuumPairFixedSeam.lean — #5016;
4. PhysicalYangMillsWilsonSUNTwoModeFiniteOSUncenteredPairPhysical.lean — #5015;
5. PhysicalYangMillsWilsonSUNTwoModeFiniteOSVacuumPairAlignmentBridge.lean — #5014;
6. PhysicalYangMillsWilsonSUNTwoModeFiniteOSPairTopTopScalarCriterion.lean — #5013;
7. PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceSimplicity.lean — #5012;
8. PhysicalYangMillsWilsonSUNTwoModeFiniteOSFullPairNonTopQ0Bridge.lean — #5009;
9. PeriodicHypercubicEvenSpecialUnitaryPhysicalPairUniformNonTopDecay.lean — #5006;
10. PhysicalYangMillsWilsonSUNPrimaryPlaquetteProjectiveCenteredNonzeroStrongLimit.lean — #4998;
11. PhysicalYangMillsWilsonProjectiveFiniteOSScaleCoherence.lean — #4993.

Current restart target:

~~~text
CURRENT CLOSED:
  finite-volume uniform q0^m
  full pair non-top q0^m
  scale-coherent projective nonzero centered strong-limit theorem
  top eigenspace simplicity
  pair top-top one-dimensionality
  uncentered two-mode pair physicality
  completed OS vacuum transfer fixedness
  canonical-sign OS vacuum boundary identification
  independent endpoint gauge fixedness

NEXT H1-D4:
  independent-gauge-fixed pair sector
    -> physical pair carrier

NEXT H1-D5:
  one-vector normalized-pair / completed-OS transfer compatibility

THEN H1-D6:
  vacuum alignment
    -> explicit centered SU(N) two-mode q0^m

THEN H1-C3:
  evolved projective coherence
    -> q0 transport to nonzero projective continuum excitation

THEN H2:
  spacing-scaled continuum-time rate

LATER:
  H3 OS Hamiltonian
  H4 spectral/Wightman mass gap.
~~~

Do not reopen #5006, #5010--#5018 unless a concrete inconsistency is found.
