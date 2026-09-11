import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryObservableGram
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfTransferPathIteration
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The unnormalized positive-half OS amplitude on the actual shared-boundary /
positive-open-half coordinates.

The completed positive Wilson amplitude already contains the strict positive
bulk and the positive-side temporal plaquettes adjacent to the two fixed
planes.  The missing fixed-plane spatial contribution enters with exactly a
square root, because reflection positivity splits the boundary-only spatial
Boltzmann weight equally between the two reflected halves.

This is the correctly typed object to compare with the complete `H+1`-slab
positive-half path kernel.  It is a function of the whole positive closure,
not a one-slab operator on a single spatial slice. -/
noncomputable def periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  Real.sqrt
      (periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
        H N beta b) *
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude
      H N beta b x

/-- Exact finite-volume normalization of the canonical OS Gram feature.

The canonical boundary feature is `Z^{-1/2}` times the unnormalized physical
positive-half amplitude.  This is the normalization that has to be retained
when the OS boundary Gram/moment is compared with the positive-half path
integral; no identification with a one-slab kernel is made here. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_invSqrtPartition_mul_osAmplitude
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x =
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ *
        periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
          H N hN beta hbeta b x := by
  have hboundary :
      0 ≤ periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
        H N beta b := by
    unfold periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
    unfold periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight
    exact Real.exp_nonneg _
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
  unfold periodicHypercubicEvenBoundaryGramCoefficient
  unfold periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
  rw [Real.sqrt_div hboundary]
  rw [div_eq_mul_inv]
  ring

/-- The observable-weighted OS Gram feature has the same exact normalization.
This form is convenient before taking the open-half Bochner moment. -/
theorem periodicHypercubicEvenBoundaryObservableGramFeature_eq_invSqrtPartition_mul_osAmplitude
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta f b x =
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ *
        (periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
          H N hN beta hbeta b x * f x) := by
  unfold periodicHypercubicEvenBoundaryObservableGramFeature
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_invSqrtPartition_mul_osAmplitude]
  ring

/-- Consequently the scalar boundary moment is exactly the same `Z^{-1/2}`
normalization times the unnormalized positive-half OS amplitude with the bulk
observable inserted.

For a general positive-half observable this is a path integral *with an
insertion*.  Only after specializing to the bare/vacuum half-cylinder does the
existing #2062 endpoint theorem turn it into a plain `T^(H+1)` matrix
coefficient. -/
theorem periodicHypercubicEvenBoundaryObservableGramMoment_eq_invSqrtPartition_mul_osAmplitudeMoment
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (∫ x,
      periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta f b x
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) =
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ *
        ∫ x,
          periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
            H N hN beta hbeta b x * f x
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  calc
    (∫ x,
      periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta f b x
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) =
      ∫ x,
        (Real.sqrt
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ *
          (periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
            H N hN beta hbeta b x * f x)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards with x
      exact
        periodicHypercubicEvenBoundaryObservableGramFeature_eq_invSqrtPartition_mul_osAmplitude
          H N hN beta hbeta f b x
    _ =
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ *
        ∫ x,
          periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
            H N hN beta hbeta b x * f x
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
      rw [integral_const_mul]

end

end MathlibAnalytic
end MGAP4D
