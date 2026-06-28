import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryObservableGram
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOpenHalfHaarOrientationCorrectionCore

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A measure-preserving involutive measurable embedding transfers itself from a
density argument to an observable argument inside an integral. -/
theorem integral_measurePreserving_involutive_transport
    {X : Type} [MeasurableSpace X]
    (mu : Measure X)
    (c : X → X)
    (hmp : MeasurePreserving c mu mu)
    (hme : MeasurableEmbedding c)
    (hc : Function.Involutive c)
    (density observable : X → ℝ) :
    (∫ x, density (c x) * observable x ∂mu) =
      ∫ x, density x * observable (c x) ∂mu := by
  have hIntegrand :
      (fun x => density (c x) * observable x) =
        (fun x => density (c x) * observable (c (c x))) := by
    funext x
    exact congrArg (fun z => density (c x) * observable z) (hc x).symm
  calc
    (∫ x, density (c x) * observable x ∂mu) =
        ∫ x, density (c x) * observable (c (c x)) ∂mu := by
      exact congrArg (fun q : X → ℝ => ∫ x, q x ∂mu) hIntegrand
    _ = ∫ x, density x * observable (c x) ∂mu :=
      hmp.integral_comp hme (fun x => density x * observable (c x))

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
  let mu := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let c : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge →
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge :=
    periodicHypercubicEvenOpenHalfOrientationCorrection H
  let density :
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge → ℝ :=
    fun y =>
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal
  let observable :
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge → ℝ :=
    fun y => f x * f y
  have hmp : MeasurePreserving c mu mu := by
    simpa [c, mu, periodicHypercubicEvenOpenHalfHaarMeasure] using
      (periodicHypercubicEvenOpenHalfOrientationCorrection_measurePreserving
        H Gauge)
  have hme : MeasurableEmbedding c := by
    simpa [c] using
      (periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv
        H Gauge).measurableEmbedding
  have hc : Function.Involutive c := by
    intro y
    exact periodicHypercubicEvenOpenHalfOrientationCorrection_involutive H y
  change (∫ y, density (c y) * observable y ∂mu) =
    ∫ y, density y * observable (c y) ∂mu
  exact integral_measurePreserving_involutive_transport
    mu c hmp hme hc density observable

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
