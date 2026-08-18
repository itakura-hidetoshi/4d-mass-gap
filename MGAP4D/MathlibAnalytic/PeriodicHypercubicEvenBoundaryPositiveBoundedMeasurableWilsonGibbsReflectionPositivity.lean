import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveWilsonGibbsReflectionPositivity

/-!
# Boundary-positive Wilson reflection positivity for bounded measurable observables

The actual finite Wilson Gram argument does not require continuity of the
boundary-positive observable.  Continuity was previously used only to obtain
measurability and uniform integrability automatically.

This file lowers that interface to the receipts needed by the proof itself:

* measurability of `f`, and
* one uniform norm bound `‖f z‖ ≤ M` with `0 ≤ M`.

No reflection-positivity premise is added.  The proof still uses the actual
boundary-fibered Wilson Gibbs density and the existing scalar Gram-square
identity.  This is the finite theorem needed by measurable boundary-vacuum path
readouts before any separate continuity statement is available.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance boundaryPositiveMeasurableWilsonNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryPositiveMeasurableWilsonTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryPositiveMeasurableWilsonCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryPositiveMeasurableWilsonSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryPositiveMeasurableWilsonMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryPositiveMeasurableWilsonBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A measurable boundary-positive observable gives a measurable reflected
quadratic observable in canonical boundary/open-half coordinates. -/
theorem periodicHypercubicEvenBoundaryPositiveReflectedObservable_measurable_of_measurable
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N → ℝ)
    (hf : Measurable f) :
    Measurable (periodicHypercubicEvenBoundaryPositiveReflectedObservable H f) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
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

/-- A uniform bound on a boundary-positive observable gives the corresponding
quadratic bound after reflection. -/
theorem periodicHypercubicEvenBoundaryPositiveReflectedObservable_norm_le_of_bound
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N → ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z, ‖f z‖ ≤ M)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N)) :
    ‖periodicHypercubicEvenBoundaryPositiveReflectedObservable H f z‖ ≤ M * M := by
  have hx : ‖f (z.1, z.2.1)‖ ≤ M := hbound _
  have hy :
      ‖f (z.1, periodicHypercubicEvenOpenHalfOrientationCorrection H z.2.2)‖ ≤ M :=
    hbound _
  unfold periodicHypercubicEvenBoundaryPositiveReflectedObservable
  rw [norm_mul]
  exact mul_le_mul hx hy (norm_nonneg _) hM

/-- For each fixed shared boundary, a measurable uniformly bounded
boundary-positive observable has an integrable Wilson Gram feature. -/
theorem periodicHypercubicEvenBoundaryPositiveObservableGramFeature_integrable_of_measurable_of_bound
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N → ℝ)
    (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z, ‖f z‖ ≤ M)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta (fun x => f (b, x)) b)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let gramBound :=
    Real.sqrt
        (((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹) *
      M
  letI : IsFiniteMeasure halfMeasure := by
    dsimp [halfMeasure, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hpair : Measurable
      (fun x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (b, x)) :=
    measurable_const.prodMk measurable_id
  have hslice : Measurable
      (fun x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        f (b, x)) :=
    hf.comp hpair
  have hgramMeasurable : Measurable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta (fun x => f (b, x)) b) := by
    unfold periodicHypercubicEvenBoundaryObservableGramFeature
    exact
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_measurable
        H N hN beta hbeta b).mul hslice
  have hgramNorm : ∀ x,
      ‖periodicHypercubicEvenBoundaryObservableGramFeature
          H N hN beta hbeta (fun x => f (b, x)) b x‖ ≤ gramBound := by
    intro x
    have hg0 := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
      H N hN beta hbeta b x
    have hg :=
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
        H N hN beta hbeta b x
    have hfx : ‖f (b, x)‖ ≤ M := hbound _
    unfold periodicHypercubicEvenBoundaryObservableGramFeature
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hg0]
    exact mul_le_mul hg hfx (norm_nonneg _) (Real.sqrt_nonneg _)
  exact Integrable.of_bound hgramMeasurable.aestronglyMeasurable gramBound
    (Filter.Eventually.of_forall hgramNorm)

/-- For a fixed boundary, the actual Wilson quadratic form of a measurable
uniformly bounded boundary-positive observable is nonnegative. -/
theorem periodicHypercubicEvenBoundaryPositiveObservable_original_iteratedIntegral_nonneg_of_measurable_of_bound
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N → ℝ)
    (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z, ‖f z‖ ≤ M)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    0 ≤ ∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal *
        (f (b, x) *
          f (b, periodicHypercubicEvenOpenHalfOrientationCorrection H y))
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  let fb : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N → ℝ :=
    fun x => f (b, x)
  have hfb : Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta fb b)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
    simpa [fb] using
      periodicHypercubicEvenBoundaryPositiveObservableGramFeature_integrable_of_measurable_of_bound
        H N hN beta hbeta f hf M hM hbound b
  have hcorrected :=
    periodicHypercubicEvenBoundaryObservable_corrected_iteratedIntegral_nonneg
      H N hN beta hbeta fb b hfb
  have htransport :
      (∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
          (fb x * fb y)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) =
      ∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta (b, (x, y))).toReal *
          (fb x * fb (periodicHypercubicEvenOpenHalfOrientationCorrection H y))
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact periodicHypercubicEvenBoundaryObservable_corrected_innerIntegral_eq_original
      H N hN beta hbeta fb b x
  rw [← htransport]
  simpa [fb] using hcorrected

/-- Boundary integration preserves the measurable bounded finite Wilson Gram
positivity. -/
theorem periodicHypercubicEvenBoundaryPositiveObservable_boundaryIntegral_nonneg_of_measurable_of_bound
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N → ℝ)
    (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z, ‖f z‖ ≤ M) :
    0 ≤ ∫ b, ∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal *
        (f (b, x) *
          f (b, periodicHypercubicEvenOpenHalfOrientationCorrection H y))
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  exact integral_nonneg fun b =>
    periodicHypercubicEvenBoundaryPositiveObservable_original_iteratedIntegral_nonneg_of_measurable_of_bound
      H N hN beta hbeta f hf M hM hbound b

/-- Exact transport of a measurable uniformly bounded boundary-positive
reflected observable from the actual Wilson Gibbs measure to canonical
boundary/open-half coordinates. -/
theorem periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectedObservable_integral_eq_boundaryIntegral_of_measurable_of_bound
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N → ℝ)
    (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z, ‖f z‖ ≤ M) :
    (∫ A, periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H f A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) =
      ∫ b, ∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta (b, (x, y))).toReal *
          (f (b, x) *
            f (b, periodicHypercubicEvenOpenHalfOrientationCorrection H y))
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
  let weightedObservable := fun z => (density z).toReal * coordinateObservable z
  let weightedBound := C.base.partitionFunction⁻¹ * (M * M)
  letI : SFinite boundaryMeasure := by
    dsimp [boundaryMeasure, periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  letI : SFinite halfMeasure := by
    dsimp [halfMeasure, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hCoordinateMeasurable : Measurable coordinateObservable := by
    simpa [coordinateObservable] using
      periodicHypercubicEvenBoundaryPositiveReflectedObservable_measurable_of_measurable
        H N f hf
  have hDensityMeasurable : Measurable density := by
    simpa [density] using
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
        H N hN beta hbeta)
  have hWeightedMeasurable : Measurable weightedObservable := by
    exact (ENNReal.measurable_toReal.comp hDensityMeasurable).mul hCoordinateMeasurable
  have hZ : 0 < C.base.partitionFunction :=
    compact_oriented_partitionFunction_pos C.base
      (continuous_compact_oriented_boltzmannIntegrable C)
  have hWeightedNorm : ∀ z, ‖weightedObservable z‖ ≤ weightedBound := by
    intro z
    have hd : (density z).toReal ≤ C.base.partitionFunction⁻¹ := by
      simpa [density, C] using
        periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_le_inv_partitionFunction
          H N hN beta hbeta z
    have hq : ‖coordinateObservable z‖ ≤ M * M := by
      simpa [coordinateObservable] using
        periodicHypercubicEvenBoundaryPositiveReflectedObservable_norm_le_of_bound
          H N f M hM hbound z
    change ‖(density z).toReal * coordinateObservable z‖ ≤ weightedBound
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul hd hq (norm_nonneg _) (inv_nonneg.mpr hZ.le)
  have hKernelIntegrable : Integrable weightedObservable referenceMeasure := by
    letI : IsFiniteMeasure referenceMeasure := by
      dsimp [referenceMeasure]
      infer_instance
    exact Integrable.of_bound hWeightedMeasurable.aestronglyMeasurable weightedBound
      (Filter.Eventually.of_forall hWeightedNorm)
  have hFiberKernelIntegrable : ∀ b, Integrable
      (fun z => weightedObservable (b, z)) (halfMeasure.prod halfMeasure) := by
    intro b
    letI : IsFiniteMeasure (halfMeasure.prod halfMeasure) := by infer_instance
    have hb : Measurable
        (fun _ : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N => b) :=
      measurable_const
    have hEmbedding : Measurable
        (fun z : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N => (b, z)) :=
      hb.prodMk measurable_id
    have hm : Measurable (fun z => weightedObservable (b, z)) :=
      hWeightedMeasurable.comp hEmbedding
    exact Integrable.of_bound hm.aestronglyMeasurable weightedBound
      (Filter.Eventually.of_forall fun z => hWeightedNorm (b, z))
  have hMap :
      Measure.map (P.boundaryFiberedCoordinates Gauge) C.gibbsMeasure =
        referenceMeasure.withDensity density := by
    simpa [P, C, referenceMeasure, boundaryMeasure, halfMeasure, density,
      periodicHypercubicEvenBoundaryHaarMeasure,
      periodicHypercubicEvenOpenHalfHaarMeasure] using
      (periodicHypercubicEvenSpecialUnitary_map_boundaryFiberedCoordinates_gibbsMeasure
        H N hN beta hbeta)
  have hDensityLtTop : ∀ᵐ z ∂referenceMeasure, density z < ∞ :=
    Filter.Eventually.of_forall fun z => by
      simp [density,
        periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity,
        ContinuousCompactOrientedGaugeWilsonSystem.boundaryFiberedGibbsDensity]
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
        hCoordinateMeasurable.aestronglyMeasurable
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
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta (b, (x, y))).toReal *
          (f (b, x) *
            f (b, periodicHypercubicEvenOpenHalfOrientationCorrection H y))
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
      rfl

/-- Finite-volume Osterwalder--Schrader reflection positivity for every
measurable uniformly bounded observable on the reflection-fixed boundary plus
positive open half, under the actual `SU(N)` Wilson Gibbs law. -/
theorem periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectionPositive_boundedMeasurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N → ℝ)
    (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z, ‖f z‖ ≤ M) :
    0 ≤ ∫ A,
      periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H f A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  rw [periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectedObservable_integral_eq_boundaryIntegral_of_measurable_of_bound
    H N hN beta hbeta f hf M hM hbound]
  exact
    periodicHypercubicEvenBoundaryPositiveObservable_boundaryIntegral_nonneg_of_measurable_of_bound
      H N hN beta hbeta f hf M hM hbound

end

end MathlibAnalytic
end MGAP4D
