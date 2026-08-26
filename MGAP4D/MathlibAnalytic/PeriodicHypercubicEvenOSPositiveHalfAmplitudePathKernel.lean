import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSPositiveHalfCompleteActionPathIdentification
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCoordinateTransferBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryPositiveHalfPathAmplitude
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The actual unnormalized OS positive-half amplitude on shared-boundary /
positive-open-half coordinates is exactly the complete unfixed `H+1`-slab
path kernel extracted from the same positive closure.

This is the pointwise bridge from the reflection-positive OS factorization to
the transfer-path carrier.  No integration, temporal gauge fixing, or
one-slice transfer-power identification is used here. -/
theorem periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude_eq_unfixedPathKernel
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
        H N hN beta hbeta b x =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
          H N
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x (fun _ => 1)))
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
          H N
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x (fun _ => 1))) := by
  let A :=
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
      b x (fun _ => 1)
  have hcross :
      periodicHypercubicEvenSpatialCrossingWilsonAction H N
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b (fun _ => 1) (fun _ => 1)) =
        periodicHypercubicEvenSpatialCrossingWilsonAction H N A := by
    exact
      periodicHypercubicEvenSpatialCrossingWilsonAction_boundaryFiberedAssemble_independent
        H N b (fun _ => 1) (fun _ => 1) x (fun _ => 1)
  unfold periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
  unfold periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
  unfold periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
  rw [periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight_sqrt_eq_halfAction]
  unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
  change
    Real.exp
        (-(beta / 2) *
          periodicHypercubicEvenSpatialCrossingWilsonAction H N
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
              b (fun _ => 1) (fun _ => 1))) *
      (Real.exp (-beta * periodicHypercubicEvenPositiveWilsonAction H N A) *
        Real.exp
          (-beta * periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A)) = _
  rw [hcross]
  rw [← Real.exp_add, ← Real.exp_add]
  have hexponent :
      -(beta / 2) * periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
          (-beta * periodicHypercubicEvenPositiveWilsonAction H N A +
            -beta * periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A) =
        -beta *
          ((1 / 2 : ℝ) * periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
            periodicHypercubicEvenPositiveWilsonAction H N A +
            periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A) := by
    ring
  rw [hexponent]
  exact
    periodicHypercubicEvenCompletePositiveHalfBoltzmannWeight_eq_unfixedPathKernel
      H N beta A

/-- The pointwise OS/path-kernel identity survives integration against the
actual positive-closure Haar law with an arbitrary scalar insertion.

The insertion is deliberately retained.  Thus this theorem does not collapse a
general OS observable to a plain transfer-power matrix coefficient; it only
moves the genuine OS half-amplitude onto the unfixed path-kernel carrier. -/
theorem periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude_closureIntegral_eq_unfixedPathKernel
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ) :
    (∫ z,
      periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
          H N hN beta hbeta z.1 z.2 * F z
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)) =
      ∫ z,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
            H N beta
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
              H N
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                z.1 z.2 (fun _ => 1)))
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
              H N
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
                z.1 z.2 (fun _ => 1))) * F z
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N) := by
  apply integral_congr_ae
  filter_upwards with z
  rw [periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude_eq_unfixedPathKernel
    H N hN beta hbeta z.1 z.2]

end

end MathlibAnalytic
end MGAP4D
