import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualCanonicalPositiveHalfSubalgebra
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenGibbsReflection
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBilinearForm

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance actualCanonicalReflectionSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualCanonicalReflectionSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance actualCanonicalReflectionSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance actualCanonicalReflectionSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance actualCanonicalReflectionSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance actualCanonicalReflectionSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- The physical approximating measure is automatically invariant under the
configuration reflection carried by a canonical fiber-reflection realization.

This is the reflection analogue of the existing temporal-action pushforward
argument: transport the physical reflected pushforward through the common
interpolation, use interpolation/reflection covariance, and discharge the
finite-volume step by the actual even-periodic Wilson Gibbs reflection theorem. -/
theorem approximatingMeasure_reflection_map_eq_self
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ) :
    Measure.map R.configurationReflection
        (S.approximatingMeasure n : Measure S.Configuration) =
      (S.approximatingMeasure n : Measure S.Configuration) := by
  let μ :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (halfExtent n))
      N hN (beta n) (hbeta n)).gibbsMeasure
  rw [R.approximatingMeasure_toMeasure_eq n]
  change
    Measure.map R.configurationReflection
        (Measure.map (R.interpolate n) μ) =
      Measure.map (R.interpolate n) μ
  have hreflect : Measurable
      (periodicHypercubicEvenConfigurationReflection
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) (halfExtent n)) :=
    (periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_measurePreserving
      (halfExtent n) N hN (beta n) (hbeta n)).measurable
  calc
    Measure.map R.configurationReflection
        (Measure.map (R.interpolate n) μ) =
      Measure.map (R.configurationReflection ∘ R.interpolate n) μ :=
        Measure.map_map R.configurationReflection.continuous.measurable
          (R.interpolate_measurable n)
    _ = Measure.map
        (R.interpolate n ∘
          periodicHypercubicEvenConfigurationReflection
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) (halfExtent n)) μ := by
      congr 1
      funext A
      exact R.interpolate_reflection n A
    _ = Measure.map (R.interpolate n)
        (Measure.map
          (periodicHypercubicEvenConfigurationReflection
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) (halfExtent n)) μ) :=
      (Measure.map_map (R.interpolate_measurable n) hreflect).symm
    _ = Measure.map (R.interpolate n) μ := by
      dsimp [μ]
      rw [periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_map_eq_self]
      rfl

/-- Reflection invariance of the actual finite-volume physical weak-star state
is generated from the physical measure invariance above. -/
theorem approximatingWeakStarReflectionInvariant
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ) :
    R.reflectionData.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n) := by
  intro O
  rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply]
  rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply]
  rw [physicalYangMillsApproximatingGaugeInvariantExpectation_apply]
  rw [physicalYangMillsApproximatingGaugeInvariantExpectation_apply]
  change
    (∫ X,
      ((O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ)
        (R.configurationReflection X)
      ∂(S.approximatingMeasure n : Measure S.Configuration)) =
      ∫ X,
        ((O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) X
        ∂(S.approximatingMeasure n : Measure S.Configuration)
  calc
    (∫ X,
      ((O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ)
        (R.configurationReflection X)
      ∂(S.approximatingMeasure n : Measure S.Configuration)) =
      ∫ X,
        ((O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) X
        ∂Measure.map R.configurationReflection
          (S.approximatingMeasure n : Measure S.Configuration) := by
      symm
      exact MeasureTheory.integral_map
        R.configurationReflection.continuous.measurable.aemeasurable
        ((O : BoundedContinuousFunction S.Configuration ℝ).continuous.aestronglyMeasurable)
    _ = ∫ X,
        ((O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) X
        ∂(S.approximatingMeasure n : Measure S.Configuration) := by
      rw [R.approximatingMeasure_reflection_map_eq_self n]

/-- The continuum physical weak-star state is reflection invariant without a
separate hypothesis: invariance of every actual finite Wilson approximant
passes through the already-proved weak-star convergence theorem. -/
theorem continuumWeakStarReflectionInvariant
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta) :
    R.reflectionData.WeakStarReflectionInvariant
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S) := by
  exact
    physical_yang_mills_gaugeInvariantWeakStarReflectionInvariance_passes_to_limit
      S R.reflectionData
      (fun n => R.approximatingWeakStarReflectionInvariant n)

/-- The scale-indexed reflection-invariance family used by the actual Wilson OS
pre-Hilbert construction is therefore canonical data, not an external input. -/
noncomputable def approximatingReflectionInvariantFamily
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta) :
    ∀ n,
      R.reflectionData.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n) :=
  fun n => R.approximatingWeakStarReflectionInvariant n

/-- The canonical half-fiber/reflection realization now generates the separated
actual Wilson boundary representation with no independent reflection-invariance
argument. -/
noncomputable def toSeparatedBoundaryMomentLinearIsometryAutomatic
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).Separated →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  R.toSeparatedBoundaryMomentLinearIsometry
    R.approximatingReflectionInvariantFamily n

@[simp] theorem toSeparatedBoundaryMomentLinearIsometryAutomatic_mk
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).Carrier) :
    R.toSeparatedBoundaryMomentLinearIsometryAutomatic n
        (SeparationQuotient.mk F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S R.reflectionData halfExtent N hN beta hbeta
          R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
          R.approximatingReflectionInvariantFamily n F := by
  exact
    R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback
      |>.toSeparatedBoundaryMomentLinearIsometry_mk
        R.approximatingReflectionInvariantFamily n F

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end

end MathlibAnalytic
end MGAP4D
