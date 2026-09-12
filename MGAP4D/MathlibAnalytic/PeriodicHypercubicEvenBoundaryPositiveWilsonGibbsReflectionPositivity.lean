import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveBoundedContinuousGram
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasureInstances
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Boundary-positive reflection positivity for the actual finite Wilson Gibbs law

The preceding Gram theorem proves nonnegativity in canonical
`boundary × positive-open-half × negative-open-half` coordinates for bounded
continuous observables that may depend on the reflection-fixed boundary.

This file transports that result back to the actual finite-volume Wilson Gibbs
measure.  The transport is exact and reuses the already constructed
boundary-fibered pushforward of the Wilson Gibbs law.  Thus a bounded continuous
observable

`F : BoundaryConfiguration × OpenHalfConfiguration → ℝ`

satisfies

`∫ F(A₊) F((θA)₊) dμ_W(A) ≥ 0`,

where the boundary coordinate is included in `A₊` and is fixed by reflection.
No new reflection-positivity premise is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance boundaryPositiveWilsonNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryPositiveWilsonTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryPositiveWilsonCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryPositiveWilsonSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryPositiveWilsonMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryPositiveWilsonBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A boundary-positive observable evaluated on a full configuration and its
physical Euclidean-time reflection. -/
def periodicHypercubicEvenBoundaryPositiveFullReflectedObservable
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (f :
      (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Gauge ×
        (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge → ℝ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) : ℝ :=
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  f (P.boundaryRestriction A, P.positiveRestriction A) *
    f (P.boundaryRestriction (periodicHypercubicEvenConfigurationReflection H A),
      P.positiveRestriction (periodicHypercubicEvenConfigurationReflection H A))

/-- Canonical boundary-coordinate form of the boundary-positive reflected
observable. -/
def periodicHypercubicEvenBoundaryPositiveReflectedObservable
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (f :
      (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Gauge ×
        (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge → ℝ)
    (z : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Gauge ×
      ((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge ×
        (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge)) : ℝ :=
  f (z.1, z.2.1) *
    f (z.1, periodicHypercubicEvenOpenHalfOrientationCorrection H z.2.2)

/-- The actual full reflected observable equals the canonical boundary-coordinate
expression.  The reflection-fixed boundary is preserved exactly, while the two
open halves are exchanged with the required time-link orientation correction. -/
theorem periodicHypercubicEvenBoundaryPositiveFullReflectedObservable_eq_boundaryCoordinates
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (f :
      (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Gauge ×
        (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge → ℝ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H f A =
      periodicHypercubicEvenBoundaryPositiveReflectedObservable H f
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedCoordinates Gauge A) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let b := P.boundaryRestriction A
  let x := P.positiveRestriction A
  let y := P.negativeRestriction A
  have hA : A = P.boundaryFiberedAssemble b x y := by
    exact (P.boundaryFiberedCoordinates Gauge).symm_apply_apply A |>.symm
  rw [hA]
  simp [periodicHypercubicEvenBoundaryPositiveFullReflectedObservable,
    periodicHypercubicEvenBoundaryPositiveReflectedObservable,
    FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedCoordinates,
    P, periodicHypercubicEvenConfigurationReflection_boundaryFiberedAssemble]

/-- Density-weighted boundary-positive reflected observable. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveWeightedReflectedObservable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) ℝ)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N)) : ℝ :=
  (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
      H N hN beta hbeta z).toReal *
    periodicHypercubicEvenBoundaryPositiveReflectedObservable H f z

/-- Transport receipts for the boundary-positive observable. -/
structure PeriodicHypercubicEvenBoundaryPositiveWilsonGibbsReflectionTransportData
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) ℝ) : Prop where
  coordinateAestronglyMeasurable :
    AEStronglyMeasurable
      (periodicHypercubicEvenBoundaryPositiveReflectedObservable H f)
      (((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        ((periodicHypercubicEvenOpenHalfHaarMeasure H N).prod
          (periodicHypercubicEvenOpenHalfHaarMeasure H N))).withDensity
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta))
  kernelIntegrable :
    Integrable
      (periodicHypercubicEvenBoundaryPositiveWeightedReflectedObservable
        H N hN beta hbeta f)
      ((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        ((periodicHypercubicEvenOpenHalfHaarMeasure H N).prod
          (periodicHypercubicEvenOpenHalfHaarMeasure H N)))
  fiberKernelIntegrable :
    ∀ b, Integrable
      (fun z => periodicHypercubicEvenBoundaryPositiveWeightedReflectedObservable
        H N hN beta hbeta f (b, z))
      ((periodicHypercubicEvenOpenHalfHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N))

/-- Boundary-coordinate reflected observables generated by bounded continuous
boundary-positive functions are measurable. -/
theorem periodicHypercubicEvenBoundaryPositiveReflectedObservable_measurable
    (H N : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) ℝ) :
    Measurable (periodicHypercubicEvenBoundaryPositiveReflectedObservable H f) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  have hf : Measurable (fun z => f z) := f.continuous.measurable
  have hc : Measurable
      (periodicHypercubicEvenOpenHalfOrientationCorrection
        (H := H) (Gauge := Gauge)) :=
    (periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv
      H Gauge).measurable
  have hleft : Measurable
      (fun z : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) =>
        (z.1, z.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hright : Measurable
      (fun z : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) =>
        (z.1, periodicHypercubicEvenOpenHalfOrientationCorrection H z.2.2)) :=
    measurable_fst.prodMk (hc.comp (measurable_snd.comp measurable_snd))
  unfold periodicHypercubicEvenBoundaryPositiveReflectedObservable
  exact (hf.comp hleft).mul (hf.comp hright)

/-- Sup-norm control for the boundary-positive reflected observable. -/
theorem periodicHypercubicEvenBoundaryPositiveReflectedObservable_norm_le
    (H N : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) ℝ)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N)) :
    ‖periodicHypercubicEvenBoundaryPositiveReflectedObservable H f z‖ ≤ ‖f‖ * ‖f‖ := by
  have hx : |f (z.1, z.2.1)| ≤ ‖f‖ := by
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (z.1, z.2.1)
  have hy :
      |f (z.1, periodicHypercubicEvenOpenHalfOrientationCorrection H z.2.2)| ≤ ‖f‖ := by
    simpa [Real.norm_eq_abs] using
      f.norm_coe_le_norm
        (z.1, periodicHypercubicEvenOpenHalfOrientationCorrection H z.2.2)
  unfold periodicHypercubicEvenBoundaryPositiveReflectedObservable
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (norm_nonneg f)

/-- The density-weighted boundary-positive reflected observable is measurable. -/
theorem periodicHypercubicEvenBoundaryPositiveWeightedReflectedObservable_measurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) ℝ) :
    Measurable
      (periodicHypercubicEvenBoundaryPositiveWeightedReflectedObservable
        H N hN beta hbeta f) := by
  have hd :=
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
      H N hN beta hbeta
  have hf :=
    periodicHypercubicEvenBoundaryPositiveReflectedObservable_measurable H N f
  unfold periodicHypercubicEvenBoundaryPositiveWeightedReflectedObservable
  exact (ENNReal.measurable_toReal.comp hd).mul hf

/-- Bounded continuity supplies all transport measurability and integrability
receipts automatically. -/
noncomputable def
    periodicHypercubicEvenBoundaryPositiveWilsonGibbsReflectionTransportData_of_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) ℝ) :
    PeriodicHypercubicEvenBoundaryPositiveWilsonGibbsReflectionTransportData
      H N hN beta hbeta f := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let density := periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
    H N hN beta hbeta
  let coordinateObservable :=
    periodicHypercubicEvenBoundaryPositiveReflectedObservable H f
  let weightedObservable :=
    periodicHypercubicEvenBoundaryPositiveWeightedReflectedObservable
      H N hN beta hbeta f
  let bound := C.base.partitionFunction⁻¹ * (‖f‖ * ‖f‖)
  letI : IsFiniteMeasure boundaryMeasure := by
    dsimp [boundaryMeasure, periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  letI : IsFiniteMeasure halfMeasure := by
    dsimp [halfMeasure, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hCoordinateMeasurable : Measurable coordinateObservable := by
    simpa [coordinateObservable] using
      periodicHypercubicEvenBoundaryPositiveReflectedObservable_measurable H N f
  have hWeightedMeasurable : Measurable weightedObservable := by
    simpa [weightedObservable] using
      periodicHypercubicEvenBoundaryPositiveWeightedReflectedObservable_measurable
        H N hN beta hbeta f
  have hZ : 0 < C.base.partitionFunction :=
    compact_oriented_partitionFunction_pos C.base
      (continuous_compact_oriented_boltzmannIntegrable C)
  have hWeightedNorm : ∀ z, ‖weightedObservable z‖ ≤ bound := by
    intro z
    have hd : (density z).toReal ≤ C.base.partitionFunction⁻¹ := by
      simpa [density, C] using
        periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_le_inv_partitionFunction
          H N hN beta hbeta z
    have hfz : ‖coordinateObservable z‖ ≤ ‖f‖ * ‖f‖ := by
      simpa [coordinateObservable] using
        periodicHypercubicEvenBoundaryPositiveReflectedObservable_norm_le H N f z
    change ‖(density z).toReal * coordinateObservable z‖ ≤ bound
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul hd hfz (norm_nonneg _) (inv_nonneg.mpr hZ.le)
  refine
    { coordinateAestronglyMeasurable := hCoordinateMeasurable.aestronglyMeasurable
      kernelIntegrable := ?_
      fiberKernelIntegrable := ?_ }
  · exact Integrable.of_bound hWeightedMeasurable.aestronglyMeasurable bound
      (Filter.Eventually.of_forall hWeightedNorm)
  · intro b
    have hb : Measurable
        (fun _ : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N => b) :=
      measurable_const
    have hEmbedding : Measurable
        (fun z : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N => (b, z)) :=
      hb.prodMk measurable_id
    have hFiberMeasurable : Measurable (fun z => weightedObservable (b, z)) :=
      hWeightedMeasurable.comp hEmbedding
    exact Integrable.of_bound hFiberMeasurable.aestronglyMeasurable bound
      (Filter.Eventually.of_forall fun z => hWeightedNorm (b, z))

/-- Exact transport of the boundary-positive full reflected observable from the
actual finite Wilson Gibbs measure to canonical boundary/open-half coordinates. -/
theorem periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectedObservable_integral_eq_boundaryIntegral
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) ℝ)
    (T : PeriodicHypercubicEvenBoundaryPositiveWilsonGibbsReflectionTransportData
      H N hN beta hbeta f) :
    (∫ A, periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H f A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) =
      ∫ b, ∫ x, ∫ y,
        periodicHypercubicEvenBoundaryPositiveWeightedReflectedObservable
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
  let coordinateObservable :=
    periodicHypercubicEvenBoundaryPositiveReflectedObservable H f
  let weightedObservable :=
    periodicHypercubicEvenBoundaryPositiveWeightedReflectedObservable
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
    (∫ A, periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H f A
        ∂C.gibbsMeasure) =
        ∫ A, coordinateObservable (P.boundaryFiberedCoordinates Gauge A)
          ∂C.gibbsMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun A => by
        simpa [coordinateObservable] using
          periodicHypercubicEvenBoundaryPositiveFullReflectedObservable_eq_boundaryCoordinates
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
          periodicHypercubicEvenBoundaryPositiveWeightedReflectedObservable
            H N hN beta hbeta f (b, (x, y))
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
          ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
      rfl

/-- Finite-volume OS reflection positivity for bounded continuous observables
that may depend on the reflection-fixed boundary and the positive open half. -/
theorem periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectionPositive_boundedContinuous
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) ℝ) :
    0 ≤ ∫ A,
      periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H f A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  have htransport :=
    periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectedObservable_integral_eq_boundaryIntegral
      H N hN beta hbeta f
      (periodicHypercubicEvenBoundaryPositiveWilsonGibbsReflectionTransportData_of_boundedContinuous
        H N hN beta hbeta f)
  rw [htransport]
  simpa [periodicHypercubicEvenBoundaryPositiveWeightedReflectedObservable,
    periodicHypercubicEvenBoundaryPositiveReflectedObservable] using
    periodicHypercubicEvenBoundaryPositiveObservable_boundaryIntegral_nonneg
      H N hN beta hbeta f

end

end MathlibAnalytic
end MGAP4D
