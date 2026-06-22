import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryObservableIntegralTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryBoundaryFiberedGibbsFactorization
import Mathlib.MeasureTheory.Integral.Prod

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

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

/-- A positive-half observable evaluated before and after physical Euclidean-time
reflection on a full even-periodic configuration. -/
def periodicHypercubicEvenFullReflectedObservable
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge → ℝ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) : ℝ :=
  f ((periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A) *
    f ((periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction
      (periodicHypercubicEvenConfigurationReflection H A))

/-- Boundary-coordinate expression of the reflected positive-half observable. -/
def periodicHypercubicEvenBoundaryReflectedObservable
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge → ℝ)
    (z : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Gauge ×
      ((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge ×
        (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge)) : ℝ :=
  f z.2.1 * f (periodicHypercubicEvenOpenHalfOrientationCorrection H z.2.2)

/-- Density-weighted boundary-coordinate reflected observable. -/
noncomputable def periodicHypercubicEvenBoundaryWeightedReflectedObservable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (z : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      ((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ))) : ℝ :=
  (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
      H N hN beta hbeta z).toReal *
    periodicHypercubicEvenBoundaryReflectedObservable H f z

/-- Integrability and measurability receipts needed only for transporting the
physical Gibbs integral to the boundary-fibered reference measure. -/
structure PeriodicHypercubicEvenWilsonGibbsReflectionTransportData
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ) : Prop where
  coordinateAestronglyMeasurable :
    AEStronglyMeasurable
      (periodicHypercubicEvenBoundaryReflectedObservable H f)
      (((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        ((periodicHypercubicEvenOpenHalfHaarMeasure H N).prod
          (periodicHypercubicEvenOpenHalfHaarMeasure H N))).withDensity
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta))
  kernelIntegrable :
    Integrable
      (periodicHypercubicEvenBoundaryWeightedReflectedObservable
        H N hN beta hbeta f)
      ((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        ((periodicHypercubicEvenOpenHalfHaarMeasure H N).prod
          (periodicHypercubicEvenOpenHalfHaarMeasure H N)))
  fiberKernelIntegrable :
    ∀ b, Integrable
      (fun z => periodicHypercubicEvenBoundaryWeightedReflectedObservable
        H N hN beta hbeta f (b, z))
      ((periodicHypercubicEvenOpenHalfHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N))

/-- The positive restriction of a reflected full configuration is the
orientation-corrected negative restriction of the original configuration. -/
theorem periodicHypercubicEvenPositiveRestriction_configurationReflection
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenOpenHalfOrientationCorrection H
        ((periodicHypercubicEvenEdgeOrbitPartition H).negativeRestriction A) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let b := P.boundaryRestriction A
  let x := P.positiveRestriction A
  let y := P.negativeRestriction A
  have hA : A = P.boundaryFiberedAssemble b x y := by
    exact (P.boundaryFiberedCoordinates Gauge).symm_apply_apply A |>.symm
  calc
    P.positiveRestriction (periodicHypercubicEvenConfigurationReflection H A) =
        P.positiveRestriction
          (periodicHypercubicEvenConfigurationReflection H
            (P.boundaryFiberedAssemble b x y)) := by rw [hA]
    _ = periodicHypercubicEvenOpenHalfOrientationCorrection H y := by
      rw [periodicHypercubicEvenConfigurationReflection_boundaryFiberedAssemble]
      exact P.positiveRestriction_boundaryFiberedAssemble _ _ _
    _ = periodicHypercubicEvenOpenHalfOrientationCorrection H
        (P.negativeRestriction A) := rfl

/-- The full reflected observable is exactly its canonical boundary-coordinate
expression. -/
theorem periodicHypercubicEvenFullReflectedObservable_eq_boundaryCoordinates
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge → ℝ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenFullReflectedObservable H f A =
      periodicHypercubicEvenBoundaryReflectedObservable H f
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedCoordinates Gauge A) := by
  unfold periodicHypercubicEvenFullReflectedObservable
  unfold periodicHypercubicEvenBoundaryReflectedObservable
  rw [periodicHypercubicEvenPositiveRestriction_configurationReflection]
  rfl

/-- Exact transport of the physical finite-volume Wilson Gibbs reflected
observable to the original boundary/open-half/open-half coordinates. -/
theorem periodicHypercubicEvenWilsonGibbs_reflectedObservable_integral_eq_boundaryIntegral
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (T : PeriodicHypercubicEvenWilsonGibbsReflectionTransportData
      H N hN beta hbeta f) :
    (∫ A, periodicHypercubicEvenFullReflectedObservable H f A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) =
      ∫ b, ∫ x, ∫ y,
        periodicHypercubicEvenBoundaryWeightedReflectedObservable
          H N hN beta hbeta f (b, (x, y))
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let referenceMeasure := boundaryMeasure.prod (halfMeasure.prod halfMeasure)
  let density := periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
    H N hN beta hbeta
  let coordinateObservable := periodicHypercubicEvenBoundaryReflectedObservable H f
  let weightedObservable := periodicHypercubicEvenBoundaryWeightedReflectedObservable
    H N hN beta hbeta f
  letI : SFinite boundaryMeasure := by
    dsimp [boundaryMeasure, periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  letI : SFinite halfMeasure := by
    dsimp [halfMeasure, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hMap :
      Measure.map (P.boundaryFiberedCoordinates Gauge) C.gibbsMeasure =
        referenceMeasure.withDensity density := by
    simpa [P, C, referenceMeasure, boundaryMeasure, halfMeasure, density,
      periodicHypercubicEvenBoundaryHaarMeasure,
      periodicHypercubicEvenOpenHalfHaarMeasure] using
      (periodicHypercubicEvenSpecialUnitary_map_boundaryFiberedCoordinates_gibbsMeasure
        H N hN beta hbeta)
  have hCoordinateMapMeasurable :
      AEStronglyMeasurable coordinateObservable
        (Measure.map (P.boundaryFiberedCoordinates Gauge) C.gibbsMeasure) := by
    rw [hMap]
    simpa [coordinateObservable, referenceMeasure, boundaryMeasure, halfMeasure,
      density] using T.coordinateAestronglyMeasurable
  have hDensityMeasurable : Measurable density := by
    simpa [density] using
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
        H N hN beta hbeta)
  have hDensityLtTop : ∀ᵐ z ∂referenceMeasure, density z < ∞ :=
    Filter.Eventually.of_forall fun z => by
      simp [density,
        periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity,
        ContinuousCompactOrientedGaugeWilsonSystem.boundaryFiberedGibbsDensity]
  have hKernelIntegrable : Integrable weightedObservable referenceMeasure := by
    simpa [weightedObservable, referenceMeasure, boundaryMeasure, halfMeasure] using
      T.kernelIntegrable
  have hFiberKernelIntegrable : ∀ b, Integrable
      (fun z => weightedObservable (b, z)) (halfMeasure.prod halfMeasure) := by
    intro b
    simpa [weightedObservable, halfMeasure] using T.fiberKernelIntegrable b
  calc
    (∫ A, periodicHypercubicEvenFullReflectedObservable H f A ∂C.gibbsMeasure) =
        ∫ A, coordinateObservable (P.boundaryFiberedCoordinates Gauge A)
          ∂C.gibbsMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun A => by
        simpa [coordinateObservable] using
          periodicHypercubicEvenFullReflectedObservable_eq_boundaryCoordinates
            H f A
    _ = ∫ z, coordinateObservable z
          ∂Measure.map (P.boundaryFiberedCoordinates Gauge) C.gibbsMeasure := by
      symm
      exact MeasureTheory.integral_map
        (P.boundaryFiberedCoordinates_measurable Gauge).aemeasurable
        hCoordinateMapMeasurable
    _ = ∫ z, coordinateObservable z ∂referenceMeasure.withDensity density := by
      rw [hMap]
    _ = ∫ z, (density z).toReal • coordinateObservable z ∂referenceMeasure := by
      exact integral_withDensity_eq_integral_toReal_smul₀
        hDensityMeasurable.aemeasurable hDensityLtTop coordinateObservable
    _ = ∫ z, weightedObservable z ∂referenceMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change (density z).toReal * coordinateObservable z = weightedObservable z
        rfl
    _ = ∫ b, ∫ z, weightedObservable (b, z)
          ∂halfMeasure.prod halfMeasure ∂boundaryMeasure := by
      exact MeasureTheory.integral_prod _ hKernelIntegrable
    _ = ∫ b, ∫ x, ∫ y, weightedObservable (b, (x, y))
          ∂halfMeasure ∂halfMeasure ∂boundaryMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun b =>
        MeasureTheory.integral_prod _ (hFiberKernelIntegrable b)
    _ = ∫ b, ∫ x, ∫ y,
          periodicHypercubicEvenBoundaryWeightedReflectedObservable
            H N hN beta hbeta f (b, (x, y))
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
          ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
      rfl

/-- Finite-volume Osterwalder--Schrader reflection positivity for the actual
`SU(N)` Wilson Gibbs law on the even periodic four-dimensional lattice. -/
theorem periodicHypercubicEvenWilsonGibbs_reflectionPositive
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (T : PeriodicHypercubicEvenWilsonGibbsReflectionTransportData
      H N hN beta hbeta f)
    (hf : ∀ b, Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta f b)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N)) :
    0 ≤ ∫ A, periodicHypercubicEvenFullReflectedObservable H f A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  rw [periodicHypercubicEvenWilsonGibbs_reflectedObservable_integral_eq_boundaryIntegral
    H N hN beta hbeta f T]
  simpa [periodicHypercubicEvenBoundaryWeightedReflectedObservable,
    periodicHypercubicEvenBoundaryReflectedObservable] using
    periodicHypercubicEvenBoundaryObservable_original_boundaryIntegral_nonneg
      H N hN beta hbeta f hf

end

end MathlibAnalytic
end MGAP4D
