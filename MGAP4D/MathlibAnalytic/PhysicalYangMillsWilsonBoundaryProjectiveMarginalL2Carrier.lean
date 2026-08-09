import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentSeparationCompletion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonProjectiveMarginalL2MassFreeCarrier
import MGAP4D.MathlibAnalytic.RealLinearIsometryRangeIdentification
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- The genuinely model-facing finite-coordinate datum needed to place the
actual compact-Wilson boundary Hilbert realization inside one projective finite
marginal.

The map goes from a projective marginal configuration to the actual shared
Wilson boundary configuration and is required to push the selected marginal
law exactly to boundary Haar measure.  Mathlib then supplies the `L²` pullback
isometry automatically.

No identification of the full projective marginal `L²` space with the Wilson
OS Hilbert space is assumed. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveMarginalReadout
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (F : EuclideanYangMillsProjectiveCylinderFamily) where
  marginalIndex : ℕ → Finset EuclideanFourSpace
  boundaryReadout :
    (n : ℕ) →
      (∀ x : marginalIndex n, F.fieldValue x) →
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
          (halfExtent n) N
  boundaryReadout_measurePreserving :
    ∀ n,
      MeasurePreserving
        (boundaryReadout n)
        (F.finiteMarginal (marginalIndex n))
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveMarginalReadout

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

/-- Pull a shared-boundary Haar `L²` vector back to the selected finite
projective marginal.  Exact measure preservation makes this a canonical
Mathlib linear isometry. -/
noncomputable def boundaryL2Pullback
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveMarginalReadout
      Q F)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →ₗᵢ[ℝ]
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  Lp.compMeasurePreservingₗᵢ ℝ
    (R.boundaryReadout n)
    (R.boundaryReadout_measurePreserving n)

@[simp] theorem boundaryL2Pullback_norm
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveMarginalReadout
      Q F)
    (n : ℕ)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    ‖R.boundaryL2Pullback n v‖ = ‖v‖ :=
  (R.boundaryL2Pullback n).norm_map v

/-- Compose the already-proved actual Wilson OS-to-boundary isometry with the
measure-preserving boundary-to-projective pullback.  This is the desired actual
compact-Wilson finite OS embedding into one projective marginal `L²` carrier. -/
noncomputable def finiteOSMarginalLinearIsometry
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveMarginalReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n →ₗᵢ[ℝ]
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  (R.boundaryL2Pullback n).comp
    (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n)

@[simp] theorem finiteOSMarginalLinearIsometry_norm
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveMarginalReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    ‖R.finiteOSMarginalLinearIsometry hInvariant n phi‖ = ‖phi‖ :=
  (R.finiteOSMarginalLinearIsometry hInvariant n).norm_map phi

/-- The correct selected finite marginal carrier is the exact range of the
actual finite Wilson OS isometry, rather than the whole raw marginal `L²`
space. -/
noncomputable def selectedMarginalSubspace
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveMarginalReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    Submodule ℝ (Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n))) :=
  LinearMap.range (R.finiteOSMarginalLinearIsometry hInvariant n).toLinearMap

/-- The measure-preserving boundary readout theorem-generates a genuine
proof-relevant two-sided identification of the actual completed finite Wilson
OS Hilbert space with its selected projective marginal subspace. -/
noncomputable def finiteIdentification
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveMarginalReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    RealHilbertLinearIsometricIdentification
      (PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n)
      (R.selectedMarginalSubspace hInvariant n) :=
  realHilbertLinearIsometricIdentificationRange
    (R.finiteOSMarginalLinearIsometry hInvariant n)

@[simp] theorem finiteIdentification_forward_coe
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveMarginalReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    (((R.finiteIdentification hInvariant n).forward phi :
        R.selectedMarginalSubspace hInvariant n) :
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n))) =
        R.finiteOSMarginalLinearIsometry hInvariant n phi := by
  exact
    realHilbertLinearIsometricIdentificationRange_forward_coe
      (R.finiteOSMarginalLinearIsometry hInvariant n) phi

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveMarginalReadout

/-- After the finite compact-Wilson/projective identification has been generated
from a measure-preserving boundary readout, the remaining common-carrier data
are purely continuum-facing: choose the continuum OS subspace, prove that every
finite projective image lands there, and identify that subspace with the
physical Hilbert space. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveContinuumInput
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
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveMarginalReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (P : D.OSPreHilbertData) where
  continuumOSSubspace : Submodule ℝ (Lp ℝ 2 L.continuumMeasure)
  finiteImage_mem_continuumOS :
    ∀ n
      (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n),
      L.finiteMarginalL2Pullback (R.marginalIndex n)
          (R.finiteOSMarginalLinearIsometry hInvariant n phi) ∈
        continuumOSSubspace
  physicalIdentification :
    RealHilbertLinearIsometricIdentification
      continuumOSSubspace P.PhysicalHilbert

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveContinuumInput

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
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveMarginalReadout
      Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {P : D.OSPreHilbertData}

/-- Fill the complete #1581 proof-relevant projective carrier identification.
The finite identification is no longer model input: it is generated from the
actual Wilson boundary isometry and the measure-preserving boundary readout. -/
noncomputable def toProjectiveMarginalL2Identification
    (C : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveContinuumInput
      (hInvariant := hInvariant) R L P) :
    PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := Q.toWeakStarBridge) (hInvariant := hInvariant) F L P where
  marginalIndex := R.marginalIndex
  marginalSubspace := R.selectedMarginalSubspace hInvariant
  finiteIdentification := R.finiteIdentification hInvariant
  continuumOSSubspace := C.continuumOSSubspace
  finiteImage_mem_continuumOS := by
    intro n phi
    simpa [R.finiteIdentification_forward_coe hInvariant n phi] using
      C.finiteImage_mem_continuumOS n phi
  physicalIdentification := C.physicalIdentification

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryProjectiveContinuumInput

end

end MathlibAnalytic
end MGAP4D
