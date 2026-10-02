import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5BoundaryVacuumMomentCriterion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentUnfixedPathKernel
import Mathlib.Tactic

/-!
# Unfixed positive-half path-kernel form of the vacuum-normalized H1-D5 seam

The preceding H1-D5 reduction identifies the finite OS vacuum in ordered
spatial-slice-pair coordinates with the literal Wilson boundary vacuum moment.

The boundary-moment path-kernel theorem already expands every boundary moment
as the reciprocal square-root partition normalization times a complete unfixed
positive-half path-kernel moment.  Specializing its insertion to the constant
observable therefore removes the remaining abstract boundary Gram feature from
H1-D5.

No new compatibility, transfer, spectral, or positivity assumption is added.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5UnfixedPathTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5UnfixedPathCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5UnfixedPathSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5UnfixedPathMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5UnfixedPathBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5UnfixedPathSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5UnfixedPathPairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- Complete unfixed positive-half path-kernel vacuum moment in ordered
spatial-slice-pair coordinates. -/
def periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
    (H N : ℕ)
    (beta : ℝ)
    (q :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ℝ :=
  periodicHypercubicEvenBoundaryUnfixedPathKernelMoment
    H N beta (fun _ => (1 : ℝ))
    ((periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm q)

/-- The finite Wilson boundary vacuum moment is exactly the reciprocal
square-root partition normalization times the complete unfixed positive-half
path-kernel moment with constant insertion. -/
theorem
    periodicHypercubicEvenBoundaryVacuumMoment_eq_invSqrtPartition_mul_unfixedPathKernelMoment
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryVacuumMoment
        H N hN beta hbeta b =
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ *
        periodicHypercubicEvenBoundaryUnfixedPathKernelMoment
          H N beta (fun _ => (1 : ℝ)) b := by
  have h :=
    periodicHypercubicEvenBoundaryObservableMoment_eq_invSqrtPartition_mul_unfixedPathKernelMoment
      H N hN beta hbeta (fun _ => (1 : ℝ)) b
  simpa [
    periodicHypercubicEvenBoundaryObservableMoment,
    periodicHypercubicEvenBoundaryObservableGramFeature,
    periodicHypercubicEvenBoundaryVacuumMoment
  ] using h

/-- Pair-coordinate version of the literal finite Wilson vacuum path-kernel
formula. -/
theorem
    periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate_eq_invSqrtPartition_mul_unfixedPathKernelMomentPairCoordinate
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (q :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate
        H N hN beta hbeta q =
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ *
        periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
          H N beta q := by
  exact
    periodicHypercubicEvenBoundaryVacuumMoment_eq_invSqrtPartition_mul_unfixedPathKernelMoment
      H N hN beta hbeta
      ((periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm q)

section VacuumNormalizedH1D5UnfixedPath

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- H1-D5 is exactly the finite Wilson one-slab pair-kernel identity with the
source written as the partition-normalized complete unfixed positive-half
path-kernel vacuum moment. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_unfixedPathKernelMomentWilsonIntegral :
    PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C ↔
      ∀ n : ℕ,
        ∀ x y :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N,
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              (halfExtent n) N hN (beta n) (hbeta n)‖ ^ 2)⁻¹ *
              ∫ q, ∫ p,
                inner ℝ
                  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
                    (halfExtent n) N (beta n) (p, q))
                  (((Real.sqrt
                      (periodicHypercubicSpecialUnitaryWilsonSystem
                        (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
                          (beta n) (hbeta n)).base.partitionFunction)⁻¹ *
                      periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
                        (halfExtent n) N (beta n) p) *
                    (((x :
                        Lp ℝ 2
                          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                            (halfExtent n) N)) q.1) *
                      ((y :
                        Lp ℝ 2
                          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                            (halfExtent n) N)) q.2)))
                ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
                  (halfExtent n) N)
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
                (halfExtent n) N) =
            ∫ q,
              inner ℝ
                ((Real.sqrt
                    (periodicHypercubicSpecialUnitaryWilsonSystem
                      (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
                        (beta n) (hbeta n)).base.partitionFunction)⁻¹ *
                  periodicHypercubicEvenBoundaryVacuumUnfixedPathKernelMomentPairCoordinate
                    (halfExtent n) N (beta n) q)
                (((x :
                    Lp ℝ 2
                      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                        (halfExtent n) N)) q.1) *
                  ((y :
                    Lp ℝ 2
                      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                        (halfExtent n) N)) q.2))
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
                (halfExtent n) N) := by
  rw [
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_iff_boundaryVacuumMomentWilsonIntegral
      Q hInvariant C]
  constructor
  · intro h n x y
    simpa only [
      periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate_eq_invSqrtPartition_mul_unfixedPathKernelMomentPairCoordinate
    ] using h n x y
  · intro h n x y
    simpa only [
      periodicHypercubicEvenBoundaryVacuumMomentPairCoordinate_eq_invSqrtPartition_mul_unfixedPathKernelMomentPairCoordinate
    ] using h n x y

end VacuumNormalizedH1D5UnfixedPath

end

end MathlibAnalytic
end MGAP4D
