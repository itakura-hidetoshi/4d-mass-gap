import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentSeparationCompletion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalL2Isometry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonProjectiveMarginalL2MassFreeCarrier
import MGAP4D.MathlibAnalytic.RealLinearIsometryRangeIdentification
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Correct interacting finite-coordinate compatibility between a projective
finite marginal and the actual compact-Wilson boundary marginal.

At nonzero coupling the Wilson boundary marginal is generally not boundary
Haar.  The latter is only a reference measure for the OS boundary-moment
realization.  Therefore the projective marginal is required to recover the
**interacting boundary marginal** under a measurable boundary readout.

The already-proved reciprocal-vacuum density isometry then transports boundary
Haar `L²` into this interacting marginal before the projective pullback is
applied. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
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
  boundaryReadout_measurable :
    ∀ n, Measurable (boundaryReadout n)
  map_finiteMarginal_eq_boundaryMarginal :
    ∀ n,
      Measure.map (boundaryReadout n)
          (F.finiteMarginal (marginalIndex n)) =
        periodicHypercubicEvenBoundaryMarginalMeasure
          (halfExtent n) N hN (beta n) (hbeta n)

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

/-- The explicit measurable readout plus exact marginal-law identity generates
the `MeasurePreserving` object consumed by Mathlib's `L²` pullback. -/
noncomputable def boundaryReadoutMeasurePreserving
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n : ℕ) :
    MeasurePreserving
      (R.boundaryReadout n)
      (F.finiteMarginal (R.marginalIndex n))
      (periodicHypercubicEvenBoundaryMarginalMeasure
        (halfExtent n) N hN (beta n) (hbeta n)) where
  measurable := R.boundaryReadout_measurable n
  map_eq := R.map_finiteMarginal_eq_boundaryMarginal n

/-- Pull the actual interacting Wilson boundary marginal `L²` into the selected
projective finite marginal. -/
noncomputable def boundaryMarginalL2Pullback
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n : ℕ) :
    PeriodicHypercubicEvenBoundaryMarginalL2
        (halfExtent n) N hN (beta n) (hbeta n) →ₗᵢ[ℝ]
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  Lp.compMeasurePreservingₗᵢ ℝ
    (R.boundaryReadout n)
    (R.boundaryReadoutMeasurePreserving n)

/-- Density-corrected actual compact-Wilson finite OS embedding into one
projective finite marginal.

The three factors are all theorem-generated isometries:

`H_n^OS → L²(boundary Haar) → L²(boundary Gibbs marginal) → L²(projective marginal)`.

The middle map is reciprocal multiplication by the strictly positive Wilson OS
boundary-vacuum moment. -/
noncomputable def finiteOSMarginalLinearIsometry
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n →ₗᵢ[ℝ]
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  (R.boundaryMarginalL2Pullback n).comp
    ((periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
      (halfExtent n) N hN (beta n) (hbeta n)).comp
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n))

@[simp] theorem finiteOSMarginalLinearIsometry_norm
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    ‖R.finiteOSMarginalLinearIsometry hInvariant n phi‖ = ‖phi‖ :=
  (R.finiteOSMarginalLinearIsometry hInvariant n).norm_map phi

/-- The selected projective finite carrier is exactly the image of the
interacting density-corrected Wilson OS isometry. -/
noncomputable def selectedMarginalSubspace
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    Submodule ℝ (Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n))) :=
  LinearMap.range (R.finiteOSMarginalLinearIsometry hInvariant n).toLinearMap

/-- Genuine two-sided proof-relevant identification with the exact selected
projective marginal subspace. -/
noncomputable def finiteIdentification
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
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
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
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

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

/-- Once the finite interacting boundary marginal is recovered by the
projective family, only the continuum-facing range data remain before #1581's
mass-free carrier is generated. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveContinuumInput
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
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
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

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveContinuumInput

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
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {P : D.OSPreHilbertData}

/-- Fill the complete #1581 carrier identification through the actual
interacting Wilson boundary marginal rather than the beta-zero/Haar shortcut. -/
noncomputable def toProjectiveMarginalL2Identification
    (C : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveContinuumInput
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

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveContinuumInput

end

end MathlibAnalytic
end MGAP4D
