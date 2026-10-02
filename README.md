# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

## Current theorem status — through merged PR #5018

The finite-volume positive-beta transfer-gap route is closed with the explicit uniform constants

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= physical top-eigenspace transfer gap

q0 = 3071/3072

||R_n^m x|| <= q0^m ||x||.
~~~

Since #5006, the q0 estimate is available on the full completed physical pair non-top sector, not only on a selected one-sided excitation lane.

The main advance from #5010 through #5018 is structural. The repository now proves that the finite-volume normalized physical one-slab top eigenspace is one-dimensional, collapses the completed pair top-top block to one selected pair-top line, reduces the concrete SU(N) centered two-mode q0 problem to finite OS vacuum alignment, and then reduces that alignment to an explicit one-vector transfer seam.

For the canonical-sign coherent Wilson pullback, the finite OS vacuum is now identified with the concrete finite Wilson boundary-vacuum vector and, after transport to ordered primary/antipodal pair coordinates, is proved fixed by arbitrary independent endpoint gauge transformations.

The immediate remaining H1-D work is therefore sharply localized:

1. identify the independently endpoint-gauge-fixed pair sector with the completed physical pair carrier, at least for the canonical-sign OS vacuum pair;
2. prove the one-vector compatibility between the normalized physical pair transfer used by the q0 theorem and the completed OS boundary transfer on that vacuum pair.

Once those two statements are theorem-generated, the already-proved #5016 bridge yields finite OS vacuum/top alignment and the #5015/#5009 chain yields q0^m decay for the explicit centered SU(N) two-mode finite OS states without an arbitrary compatibility structure.

A complete continuum four-dimensional Yang--Mills existence and Wightman mass-gap theorem is not yet claimed.

## Authority checkpoint — 2026-10-02 JST

| Item | Authoritative value |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Latest theorem-bearing snapshot | 382f73aa90ab24d7b02285012bf6e5513ad62a41 — merged PR #5018 |
| #5018 validated exact PR head | 99d2e1c208654ee29f58ca1bc948b4baa9595cdd |
| #5018 validation | PR Lean Fast Check run 36991129671: completed / success; exact-head completion receipt: success |
| Lean | v4.30.0-rc2 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |

[Authoritative theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) · [Detailed roadmap](ROADMAP.md)

The default branch main is not theorem authority. It is a documentation mirror. README / ROADMAP-only commits may advance a branch pointer without changing the latest theorem-bearing snapshot.

Authority order is fixed:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

## Current claim boundary

The theorem carrier proves a strong finite-volume result and several exact continuum-carrier interfaces, but it does not yet prove the final continuum mass gap.

What is already closed:

- beta = 0 physical transfer gap equals 1;
- positive-beta high-temperature finite-volume coercivity;
- volume/rank/scale-uniform transfer-gap floor 1/3072;
- uniform discrete power decay q0^m with q0 = 3071/3072;
- full physical pair non-top q0 decay;
- one-dimensionality of the finite-volume physical top eigenspace;
- one-dimensionality of the completed pair top-top block;
- a scale-coherent projective L2 carrier supporting nonzero centered finite-OS strong limits under the projective cylinder/readout data;
- explicit SU(N) Wilson two-mode boundary representatives;
- theorem reduction of the centered two-mode q0 problem to a finite OS vacuum seam;
- canonical-sign identification of the finite OS boundary vacuum with the concrete Wilson boundary-vacuum L2 vector;
- independent primary/antipodal endpoint gauge fixedness of that canonical-sign vacuum pair.

What remains open:

- independently gauge-fixed pair L2 sector versus completed physical pair carrier;
- normalized physical pair transfer versus completed OS boundary transfer on the canonical-sign vacuum vector;
- model-facing transport of the finite q0 dynamics into the projective continuum excitation limit;
- spacing-scaled continuum-time dynamics;
- final OS Hamiltonian spectral lower bound and Wightman energy-momentum mass-gap theorem.

## Closed finite-volume gap route

### 1. Complete tagged-link and twelve-spatial frame — #4935--#4983

The leakage, Schur, recurrence, renewal, two-boundary, complete-order and twelve-spatial layers are closed.

The endpoint is

~~~text
kappa_12(s,beta) * ||f - B f||^2 <= E_12(f),

0 < kappa_12(s,beta),

1/2304 <= kappa_12(s,beta),

1/3072 <= physical top-eigenspace transfer gap.
~~~

#4983 then defines

~~~text
q0 = 3071/3072
~~~

and proves the uniform discrete contraction

~~~text
||R_n|| <= q0 < 1
||R_n^m|| <= q0^m
||R_n^m x|| <= q0^m ||x||.
~~~

No lattice-volume, link-count or gauge-rank loss appears in this bound.

### 2. Independent-product carrier audit — #4984--#4992

#4984 embeds all finite top-orthogonal sectors isometrically into one interacting independent-product boundary L2 carrier.

#4985 proves that explicitly compatible strong limits preserve q0^m.

#4988 proves the model-free obstruction

~~~text
pairwise orthogonal + strong convergence => zero limit.
~~~

#4989 proves that distinct independent-product coordinate pullbacks have inner product equal to the product of their means, hence centered fresh-coordinate vectors are pairwise orthogonal.

#4992 isolates the exact top-boundary-vacuum compatibility needed to apply this obstruction to the Wilson one-sided excitation images.

Conclusion: the independent product remains useful as a simultaneous finite-scale carrier, but it must not be mistaken for a nontrivial scale-coherent continuum identification.

## Scale-coherent projective carrier — #4993--#4998

#4993 constructs the projective finite-OS scale-coherence interface. Under exact finite-marginal transition compatibility, different finite-scale OS representatives have literally the same image in one projective-limit L2 space.

Therefore an exactly coherent nonzero finite sequence has an automatic nonzero strong limit.

#4994/#4995 specialize this geometry to SU(2) primary-plaquette finite OS states and vacuum-centering.

#4997 constructs a nonzero centered projective excitation witness.

#4998 generalizes the centered nonzero projective strong-limit theorem to SU(N). Its theorem is deliberately conditional on the existing projective primary-plaquette Haar-mode cylinder/readout package and finite vacuum-unit compatibility; it does not by itself identify the finite transfer used in q0 with continuum Euclidean-time evolution.

This projective lane is the current preferred scale-coherent alternative to the independent-product presentation.

## Explicit SU(N) two-mode lane — #4999--#5009

### #4999--#5003: explicit modes and readout

The model-facing primary-plaquette family is reduced to two concrete Wilson Haar modes:

- #4999: explicit nonconstant SU(N) Wilson-energy witness;
- #5000: explicit SU(N) two-mode Haar orthonormal family;
- #5001: only two modes are required for the nonzero excitation argument;
- #5002: continuous boundary representatives;
- #5003: realization reduced to pointwise coherent readout.

### #5004--#5008: q0 bridge and explicit centered boundary formula

#5004 transports q0 decay to the one-sided boundary sector.

#5005 first bridges concrete SU(N) two-mode finite OS states to q0 through a compatibility package.

#5007 removes that arbitrary package: compatibility is theorem-generated from exact range membership plus the literal raw one-slab matrix coefficient identity.

#5008 rewrites the actual centered finite OS boundary image explicitly as

~~~text
finiteVacuumCentered
  (boundary image of finite OS vacuum)
  (explicit primary-plaquette two-mode boundary Haar vector).
~~~

This exposed the genuine top/vacuum issue rather than hiding it inside a compatibility structure.

### #5006 and #5009: full physical pair non-top route

#5006 proves uniform q0^m decay on the full completed physical pair non-top sector.

#5009 routes the explicit centered two-mode pair vector through that stronger result. It shows that only two pair-side residuals are needed:

~~~text
centered pair vector ∈ PhysicalPairCarrier

centered pair vector ∈ TopTop^perp.
~~~

No one-sided factorization or pairWeakAtFor assumption is needed in this full-pair lane.

## Top-sector rigidity and simplicity — #5010--#5013

This is one of the main new closed layers.

### #5010: strict positivity rigidity

Every nonzero nonnegative vector in the full normalized physical top eigenspace is strictly positive almost everywhere.

### #5011: sign rigidity

For every unit top mode f, the physical absolute value |f| is again a top mode. The vectors |f| + f and |f| - f cannot both be nonzero, so every unit top mode has one fixed sign almost everywhere.

### #5012: top eigenspace simplicity

The full normalized physical top eigenspace is exactly one-dimensional:

~~~text
TopEigenspace
  = span(canonical nonnegative top mode)
  = span(chosen normalized top eigenvector).
~~~

Consequently the old chosen-vacuum excitation submodule is exactly the orthogonal complement of the full top eigenspace.

This removes the earlier need to avoid or assume top-sector simplicity.

### #5013: pair top-top scalar criterion

Top-eigenspace simplicity is lifted to the pair sector. Completed top-top orthogonality is equivalent to one scalar matrix coefficient against the selected pair-top mode.

The large submodule condition is therefore reduced to

~~~text
<Omega_top tensor Omega_top, x> = 0.
~~~

## H1-D residual reduction — #5014--#5018

### #5014: reduce full-pair residuals to vacuum alignment

The centered pair residuals are reduced to two concrete statements:

1. the uncentered primary-plaquette pair is physical;
2. the finite OS vacuum pair lies on the selected top-pair line.

### #5015: uncentered primary-plaquette physicality CLOSED

The uncentered primary-plaquette mode is proved to factor in pair coordinates as

~~~text
physical one-slice plaquette mode tensor physical constant-one mode.
~~~

Therefore it belongs to the completed physical pair carrier.

After #5015, vacuum alignment is the only remaining structural input needed by the centered q0^m theorem.

### #5016: vacuum alignment becomes a one-vector transfer seam

#5016 proves the completed pair top-top block itself is exactly the one-dimensional selected pair-top line.

It also proves that the finite OS vacuum pair is automatically fixed by the completed OS boundary transfer.

Thus the old vacuum-alignment statement follows from only:

~~~text
(A) OS vacuum pair ∈ PhysicalPairCarrier

(B) normalized physical pair transfer agrees,
    on that vacuum vector,
    with the pair-coordinate completed OS boundary transfer.
~~~

Because the completed OS boundary transfer already fixes the vacuum, no global all-input intertwining is required.

### #5017: canonical-sign OS vacuum = concrete Wilson boundary vacuum

The coherent positive-half square root has only a scale-wise sign freedom on the unit observable. The existing vacuumNormalized construction removes it without changing the reflected quadratic observable.

For Q.vacuumNormalized, #5017 proves

~~~text
finite OS vacuum boundary image
  = periodicHypercubicEvenBoundaryVacuumL2.
~~~

The concrete boundary vacuum is also proved fixed by every full finite-lattice boundary gauge pullback.

### #5018: independent endpoint gauge fixedness CLOSED

The reflection-fixed boundary is written exactly as primary slice plus antipodal slice.

Two arbitrary one-slice gauge transformations are extended independently to the full finite lattice, and the boundary/pair coordinate equivalence is proved to intertwine that full action with the independent product action on the two endpoint slices.

Therefore the canonical-sign explicit OS vacuum pair is fixed by arbitrary independent primary and antipodal gauge transformations.

This is the current theorem-bearing endpoint.

## Immediate frontier after #5018

### H1-D4. Independent gauge-fixed pair sector -> physical pair carrier

The physical pair carrier is defined as the Hilbert closure of decomposable tensors of one-slice Gauss-law physical vectors.

The next functional-analytic target is to prove that the independently endpoint-gauge-fixed pair sector is exactly this completed physical pair carrier, or at minimum that the canonical-sign OS vacuum pair belongs to it.

#5018 supplies the full gauge-fixedness input. What remains is the Hilbert closure/fixed-subspace identification.

### H1-D5. One-vector physical-pair/completed-OS transfer compatibility

For the canonical-sign OS vacuum pair, prove

~~~text
NormalizedPhysicalPairTransfer vacuumPair
  =
PairCoordinateCompletedOSBoundaryTransfer vacuumPair.
~~~

Only this single vector is needed.

#5016 already proves the right-hand side equals vacuumPair, so this theorem will give normalized physical pair fixedness.

### H1-D6. Close vacuum alignment and concrete q0^m decay

Once H1-D4 and H1-D5 are proved, #5016 gives

~~~text
OS vacuum pair ∈ selected pair-top line.
~~~

Then #5015 + #5009 immediately give

~~~text
||S_{2,n}^m y_{k,n}|| <= q0^m ||y_{k,n}||
~~~

for the explicit centered SU(N) two-mode finite OS boundary vectors, without an arbitrary compatibility structure.

## Projective continuum continuation

The projective carrier already supports nonzero centered strong limits under the cylinder/readout data.

After H1-D is closed, the next projective task is dynamical rather than kinematic:

1. choose the explicit two-mode finite OS sequence;
2. prove projective initial-state coherence;
3. prove projective coherence/convergence after one or m finite transfer steps;
4. transport the q0^m bound to the projective continuum excitation operator.

This must be kept distinct from the independent-product carrier, whose centered fresh-coordinate strong limits vanish.

## H2 continuum-scaling obstruction

The fixed discrete factor

~~~text
q0 = 3071/3072 < 1
~~~

cannot itself be interpreted as a fixed physical-time continuum factor when lattice spacing a_n -> 0.

For fixed t > 0,

~~~text
q0 ^ floor(t / a_n) -> 0.
~~~

That gives instantaneous collapse rather than a nontrivial strongly continuous semigroup.

H2 therefore requires a spacing-scaled statement such as

~~~text
q_n = exp(-m_n a_n + o(a_n))
~~~

or an equivalent rescaled defect, Dirichlet-form or generator lower bound.

The repository already contains floor-time, derived-rate, physical-excitation Dirichlet-scaling and intrinsic-rate-to-physical-mass infrastructure. These become active after the H1-D transfer seam is closed.

## Downstream H3 / H4

The intended final route remains

~~~text
finite-volume uniform coercivity
  -> explicit scale-coherent projective excitation dynamics
  -> spacing-scaled continuum semigroup
  -> OS physical Hilbert reconstruction
  -> self-adjoint Hamiltonian on the vacuum-orthogonal sector
  -> positive spectral gap
  -> Wightman / energy-momentum mass gap.
~~~

The generic OS/Hamiltonian machinery is substantial; the current bottleneck is the model-facing finite transfer / OS vacuum / projective scaling compatibility.

## Lean / CI workflow

Latest theorem validation:

~~~text
PR #5018 exact head:
  99d2e1c208654ee29f58ca1bc948b4baa9595cdd

PR Lean Fast Check:
  run 36991129671
  completed / success

exact-head completion receipt:
  success

theorem-bearing merge:
  382f73aa90ab24d7b02285012bf6e5513ad62a41
~~~

Recent Lean engineering lessons:

- inspect the complete changed module, not only the first reported line;
- preserve the pinned mathlib API rather than coding against current master;
- use explicit module-specific local instance names to avoid anonymous-instance declaration collisions;
- do not rely on dot notation through local notation when the namespace receiver is ambiguous;
- make subtype-to-Lp norm/coercion boundaries explicit;
- prefer congrArg plus typed scalar-map calculations to fragile simp-heavy rewrites;
- theorem headers must resolve dependent implicit arguments before the proof body can help inference;
- once an unchanged exact head is GREEN, do not rerun strict Lean validation merely for reassurance;
- README / ROADMAP-only changes are docs-only and do not change the theorem-bearing baseline.

## Milestone map — recent theorem progression

| PR | Contribution |
| --- | --- |
| #4992 | exact Wilson top-boundary-vacuum centering obstruction |
| #4993 | projective finite OS scale coherence |
| #4994 | SU(2) primary-plaquette projective strong limits |
| #4995 | finite vacuum-centering commutes with projective embedding |
| #4997 | nonzero centered projective excitation witness |
| #4998 | generic SU(N) centered nonzero projective strong-limit theorem |
| #4999 | explicit nonconstant SU(N) Wilson-energy witness |
| #5000 | explicit SU(N) Wilson Haar two-mode orthonormal family |
| #5001 | reduce excitation route to two concrete modes |
| #5002 | continuous SU(N) two-mode boundary representatives |
| #5003 | pointwise coherent readout reduction |
| #5004 | uniform q0 decay on the one-sided boundary sector |
| #5005 | concrete SU(N) two-mode OS state to q0 bridge |
| #5006 | full physical pair non-top uniform q0^m decay |
| #5007 | generate q0 compatibility from range + raw kernel |
| #5008 | explicit centered finite OS boundary formula |
| #5009 | full-pair non-top q0 bridge for centered data |
| #5010 | nonnegative top modes are a.e. strictly positive |
| #5011 | sign rigidity of physical top modes |
| #5012 | finite-volume physical top eigenspace simplicity |
| #5013 | pair top-top orthogonality reduced to one scalar coefficient |
| #5014 | SU(N) full-pair residuals reduced to vacuum alignment |
| #5015 | uncentered SU(N) primary-plaquette pair is physical |
| #5016 | vacuum alignment reduced to carrier + one-vector transfer seam |
| #5017 | canonical-sign OS vacuum identified with concrete gauge-fixed boundary vacuum |
| #5018 | canonical-sign OS vacuum pair independently endpoint-gauge fixed |

For the exact continuation sequence, see [ROADMAP.md](ROADMAP.md).

## Primary current modules

- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSUNTwoModeFiniteOSFullPairNonTopQ0Bridge.lean
- MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceSimplicity.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSUNTwoModeFiniteOSPairTopTopScalarCriterion.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSUNTwoModeFiniteOSVacuumPairAlignmentBridge.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSUNTwoModeFiniteOSUncenteredPairPhysical.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSUNTwoModeFiniteOSVacuumPairFixedSeam.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedBoundaryGaugeFixed.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedPairIndependentGaugeFixed.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSUNPrimaryPlaquetteProjectiveCenteredNonzeroStrongLimit.lean
- MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonProjectiveFiniteOSScaleCoherence.lean
