import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryObservableGram
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOpenHalfHaarOrientationCorrectionCore

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

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

/-- Haar invariance removes the orientation correction from the density argument
and transfers it to the reflected observable. -/
theorem periodicHypercubicEvenBoundaryObservable_corrected_innerIntegral_eq_original
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
        (f x * f y)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) =
    ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal *
        (f x * f (periodicHypercubicEvenOpenHalfOrientationCorrection H y))
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let e := periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv H Gauge
  let mu := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let k : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge → ℝ :=
    fun y =>
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal * (f x * f (e y))
  have hmp : MeasurePreserving e mu mu := by
    simpa [e, mu, periodicHypercubicEvenOpenHalfHaarMeasure] using
      (periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv_measurePreserving
        H Gauge)
  change (∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
        (f x * f y) ∂mu) =
    ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal *
        (f x * f (periodicHypercubicEvenOpenHalfOrientationCorrection H y)) ∂mu
  calc
    (∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
        (f x * f y) ∂mu) = ∫ y, k (e y) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp [k, e, periodicHypercubicEvenOpenHalfOrientationCorrection_involutive]
    _ = ∫ y, k y ∂mu := hmp.integral_comp' k
    _ = ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal *
        (f x * f (periodicHypercubicEvenOpenHalfOrientationCorrection H y)) ∂mu := by
      rfl

/-- The corrected boundary Gram integral equals the reflected observable integral
in the original negative-half coordinates. -/
theorem periodicHypercubicEvenBoundaryObservable_corrected_boundaryIntegral_eq_original
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ) :
    (∫ b, ∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
        (f x * f y)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)) =
    ∫ b, ∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal *
        (f x * f (periodicHypercubicEvenOpenHalfOrientationCorrection H y))
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  apply integral_congr_ae
  filter_upwards [] with b
  apply integral_congr_ae
  filter_upwards [] with x
  exact periodicHypercubicEvenBoundaryObservable_corrected_innerIntegral_eq_original
    H N hN beta hbeta f b x

/-- The actual reflected Wilson observable kernel in the original boundary
coordinates has a nonnegative boundary-fibered Gibbs integral. -/
theorem periodicHypercubicEvenBoundaryObservable_original_boundaryIntegral_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hf : ∀ b, Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta f b)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N)) :
    0 ≤ ∫ b, ∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal *
        (f x * f (periodicHypercubicEvenOpenHalfOrientationCorrection H y))
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  rw [← periodicHypercubicEvenBoundaryObservable_corrected_boundaryIntegral_eq_original
    H N hN beta hbeta f]
  exact periodicHypercubicEvenBoundaryObservable_corrected_boundaryIntegral_nonneg
    H N hN beta hbeta f hf

end

end MathlibAnalytic
end MGAP4D
