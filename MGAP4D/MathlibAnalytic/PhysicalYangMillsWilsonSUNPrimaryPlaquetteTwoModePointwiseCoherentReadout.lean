import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonEnergySUNTwoModeContinuousBoundaryRepresentative
import Mathlib.Tactic

/-!
# Pointwise coherent readout for the concrete SU(N) Wilson two-mode family

The previous arbitrary-rank layers have removed the SU(2)-specific mode
construction:

* #4999 proves that the Wilson energy is nonconstant for every N >= 2;
* #5000 constructs the concrete normalized-Haar orthonormal Fin 2 Wilson pair;
* #5001 proves that a coherent projective realization of those two modes gives
  a nonzero vacuum-orthogonal strong limit;
* #5002 constructs continuous conjugation-invariant representatives and
  explicit primary-plaquette boundary observables.

This file reduces the remaining model-facing input to exactly two statements:

1. the actual finite OS boundary moment of each selected positive-time
   observable agrees a.e. with the explicit #5002 boundary observable;
2. the canonical primary-plaquette projective images of each of the two modes
   are coherent under finite-marginal transition.

The source cylinder of mode k is no longer arbitrary: it is fixed at
R.marginalIndex k.val, and its source vector is the concrete primary-plaquette
image of specialUnitaryWilsonHaarTwoMode hN2 k at that marginal.

Everything after those two statements is theorem-generated, including the
#5001 nonzero vacuum-orthogonal projective strong limit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Topology
open scoped InnerProductSpace

noncomputable section

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- Generic arbitrary-rank factorization of the finite OS/projective isometry
through the canonical boundary-Haar isometry. -/
theorem finiteOSMarginalLinearIsometry_eq_boundaryHaarProjectiveL2Isometry_sun
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    R.finiteOSMarginalLinearIsometry hInvariant n phi =
      R.boundaryHaarProjectiveL2Isometry n
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n phi) :=
  rfl

/-- If one finite OS state has the explicit arbitrary-rank Wilson two-mode
boundary-Haar vector as its OS boundary moment, then its selected projective
marginal image is exactly the canonical primary-plaquette image of that Haar
mode. -/
theorem finiteOSMarginalLinearIsometry_physicalState_eq_primarySpatialPlaquetteWilsonTwoMode_of_boundaryMoment
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (hN2 : 2 ≤ N)
    (n : ℕ)
    (k : Fin 2)
    (O : D.positiveTimeSubalgebra.toSubmodule)
    (hBoundary :
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (Pn.physicalState
            (Pn.positiveTimeSubmoduleCarrierLinearMap O)) =
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
          (halfExtent n) hN2 k) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    R.finiteOSMarginalLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap O)) =
      R.primarySpatialPlaquetteHaarProjectiveL2Isometry n
        (specialUnitaryWilsonHaarTwoMode hN2 k) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hBoundary' :
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (Pn.physicalState
            (Pn.positiveTimeSubmoduleCarrierLinearMap O)) =
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
          (halfExtent n) hN2 k := by
    simpa [Pn] using hBoundary
  change
    R.finiteOSMarginalLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap O)) =
      R.primarySpatialPlaquetteHaarProjectiveL2Isometry n
        (specialUnitaryWilsonHaarTwoMode hN2 k)
  rw [R.finiteOSMarginalLinearIsometry_eq_boundaryHaarProjectiveL2Isometry_sun,
    hBoundary']
  rfl

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

/-- Pointwise model-facing readout data for the concrete arbitrary-rank Wilson
two-mode family.

No L2 boundary equality and no arbitrary cylinder vector are primitive fields.
The former is generated by Lp.ext from the explicit #5002 representative; the
latter is fixed canonically by the theorem-generated Haar pair. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N) (hN2 : 2 ≤ N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  observable : Fin 2 → D.positiveTimeSubalgebra.toSubmodule
  marginalSupportEventually : ∀ k : Fin 2,
    ∀ᶠ n in atTop, R.marginalIndex k.val ⊆ R.marginalIndex n
  boundaryMoment_coeFn_eq_primaryPlaquetteWilsonTwoModeBoundaryObservable :
    ∀ k : Fin 2, ∀ n : ℕ,
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (Pn.physicalState
            (Pn.positiveTimeSubmoduleCarrierLinearMap (observable k))) =ᵐ[
        periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N]
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryObservable
          (halfExtent n) hN2 k
  primaryPlaquetteWilsonTwoMode_transition :
    ∀ (k : Fin 2) (n : ℕ)
      (h : R.marginalIndex k.val ⊆ R.marginalIndex n),
      R.primarySpatialPlaquetteHaarProjectiveL2Isometry n
          (specialUnitaryWilsonHaarTwoMode hN2 k) =
        EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) h
          (R.primarySpatialPlaquetteHaarProjectiveL2Isometry k.val
            (specialUnitaryWilsonHaarTwoMode hN2 k))

namespace PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- The pointwise boundary-moment identity theorem-generates equality to the
actual boundary-Haar L2 mode. -/
theorem boundaryMoment_eq_primaryPlaquetteWilsonTwoModeBoundaryHaarL2
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
      S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (k : Fin 2)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k))) =
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
        (halfExtent n) hN2 k := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k))) =
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
        (halfExtent n) hN2 k
  apply Lp.ext
  exact
    (C.boundaryMoment_coeFn_eq_primaryPlaquetteWilsonTwoModeBoundaryObservable
      k n).trans
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2_coeFn
        (halfExtent n) hN2 k).symm

/-- The pointwise coherent-readout package canonically generates the #5001
two-mode cylinder datum.  In particular, finite-image compatibility follows
from the boundary-moment theorem and the canonical density/projective
isometries; it is not a primitive field. -/
noncomputable def toTwoModeCylinderData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
      S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant where
  observable := C.observable
  cylinderIndex := fun k => R.marginalIndex k.val
  cylinderVector := fun k =>
    R.primarySpatialPlaquetteHaarProjectiveL2Isometry k.val
      (specialUnitaryWilsonHaarTwoMode hN2 k)
  supportEventually := C.marginalSupportEventually
  finiteImage_eq_transition := by
    intro k n h
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    calc
      R.finiteOSMarginalLinearIsometry hInvariant n
          (Pn.physicalState
            (Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k))) =
        R.primarySpatialPlaquetteHaarProjectiveL2Isometry n
          (specialUnitaryWilsonHaarTwoMode hN2 k) := by
            exact
              R.finiteOSMarginalLinearIsometry_physicalState_eq_primarySpatialPlaquetteWilsonTwoMode_of_boundaryMoment
                hInvariant hN2 n k (C.observable k)
                (C.boundaryMoment_eq_primaryPlaquetteWilsonTwoModeBoundaryHaarL2
                  k n)
      _ =
        EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) h
          (R.primarySpatialPlaquetteHaarProjectiveL2Isometry k.val
            (specialUnitaryWilsonHaarTwoMode hN2 k)) :=
        C.primaryPlaquetteWilsonTwoMode_transition k n h
  primaryPlaquetteWilsonTwoMode_eq_transition := by
    intro k n h
    exact C.primaryPlaquetteWilsonTwoMode_transition k n h

/-- Terminal arbitrary-rank consequence: the two pointwise readout/coherence
obligations already imply existence of a nonzero projective strong limit of
actual finite Wilson OS vacuum-orthogonal states. -/
theorem exists_nonzero_vacuumOrthogonal_projectiveStrongLimit
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
      S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant) :
    ∃ k : Fin 2, ∃ y : Lp ℝ 2 L.continuumMeasure,
      y ≠ 0 ∧
      Tendsto
        (fun n =>
          R.projectiveFiniteOSEmbed L hInvariant n
            ((C.toTwoModeCylinderData L).finiteOSCenteredPhysicalState k n))
        atTop (𝓝 y) := by
  exact (C.toTwoModeCylinderData L).exists_nonzero_vacuumOrthogonal_projectiveStrongLimit U

end PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData

end

end MathlibAnalytic
end MGAP4D
