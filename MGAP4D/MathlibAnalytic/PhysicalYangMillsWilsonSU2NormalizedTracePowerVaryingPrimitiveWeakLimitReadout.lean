import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSUniformWeakLimitFromLocality
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveWeakLimitReadout

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

noncomputable section

private theorem normalizedTracePowerVaryingPrimitiveWeakLimitTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerVaryingPrimitiveWeakLimitNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerVaryingPrimitiveWeakLimitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerVaryingPrimitiveWeakLimitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerVaryingPrimitiveWeakLimitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerVaryingPrimitiveWeakLimitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerVaryingPrimitiveWeakLimitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerVaryingPrimitiveWeakLimitSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- At one matching lattice scale, a scale-dependent physical positive-time
observable with the exact normalized-trace positive-half readout has the exact
reflected-product quadratic pullback.

No equality between observables at distinct scales is required. -/
theorem normalizedTracePower_varying_quadraticObservable_pullback_of_primitivePositiveHalfReadout
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (interpolate : ∀ n, (PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) → S.Configuration)
    (configurationReflection : Homeomorph S.Configuration S.Configuration)
    (reflection_gauge_commute : ∀ g A, configurationReflection (S.action g A) =
      S.action g (configurationReflection A))
    (reflection_realization : ∀ O, D.reflection O =
      physicalGaugeInvariantObservablePrecompAlgEquiv S
        configurationReflection reflection_gauge_commute O)
    (interpolate_reflection : ∀ n A, configurationReflection (interpolate n A) =
      interpolate n (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))
    (j : ℕ) (F : ℕ → D.positiveTimeSubalgebra)
    (positive_readout : ∀ n A,
      (((F n : D.positiveTimeSubalgebra) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) (interpolate n A) =
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j
        ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A))
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge (halfExtent n) → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    D.quadraticBoundedContinuousFunction (F n) (interpolate n A) =
      normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A *
        normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j
          (periodicHypercubicEvenConfigurationReflection (halfExtent n) A) := by
  have hreflected :
      ((D.reflection
          ((F n : D.positiveTimeSubalgebra) :
            physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ)
          (interpolate n A) =
        periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) j
          ((periodicHypercubicEvenEdgeOrbitPartition
            (halfExtent n)).positiveRestriction
              (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)) := by
    rw [reflection_realization]
    change
      (((F n : D.positiveTimeSubalgebra) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ)
          (configurationReflection (interpolate n A)) = _
    rw [interpolate_reflection n A]
    exact positive_readout n
      (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)
  calc
    D.quadraticBoundedContinuousFunction (F n) (interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
            (halfExtent n) (beta n) (hbeta n) j) A := by
      unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction
      unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable
      unfold periodicHypercubicEvenFullReflectedObservable
      change
        ((D.reflection
            ((F n : D.positiveTimeSubalgebra) :
              physicalYangMillsGaugeInvariantObservableSubalgebra S) :
            physicalYangMillsGaugeInvariantObservableSubalgebra S) :
            BoundedContinuousFunction S.Configuration ℝ) (interpolate n A) *
          (((F n : D.positiveTimeSubalgebra) :
              physicalYangMillsGaugeInvariantObservableSubalgebra S) :
            BoundedContinuousFunction S.Configuration ℝ) (interpolate n A) = _
      rw [hreflected, positive_readout n A]
      ring
    _ = normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A *
        normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j
          (periodicHypercubicEvenConfigurationReflection (halfExtent n) A) := rfl

/-- Scale-dependent primitive normalized-trace readouts give nonnegative
matching-scale physical quadratic expectations directly from the actual finite
Wilson Gibbs theorem. -/
theorem normalizedTracePower_varying_approximating_quadratic_nonneg_of_primitivePositiveHalfReadout
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (interpolate : ∀ n, (PeriodicHypercubicEvenEdge (halfExtent n) → Matrix.specialUnitaryGroup (Fin 2) ℂ) → S.Configuration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (approximatingMeasure_toMeasure_eq : ∀ n, (S.approximatingMeasure n : Measure S.Configuration) =
      Measure.map (interpolate n) (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n)) 2
        normalizedTracePowerVaryingPrimitiveWeakLimitTwoRankPositive (beta n) (hbeta n)).gibbsMeasure)
    (configurationReflection : Homeomorph S.Configuration S.Configuration)
    (reflection_gauge_commute : ∀ g A, configurationReflection (S.action g A) = S.action g (configurationReflection A))
    (reflection_realization : ∀ O, D.reflection O = physicalGaugeInvariantObservablePrecompAlgEquiv S
      configurationReflection reflection_gauge_commute O)
    (interpolate_reflection : ∀ n A, configurationReflection (interpolate n A) =
      interpolate n (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))
    (j : ℕ) (F : ℕ → D.positiveTimeSubalgebra)
    (positive_readout : ∀ n A, (((F n : D.positiveTimeSubalgebra) :
      physicalYangMillsGaugeInvariantObservableSubalgebra S) : BoundedContinuousFunction S.Configuration ℝ)
      (interpolate n A) = periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j
        ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A))
    (n : ℕ) : 0 ≤ ∫ A, D.quadraticBoundedContinuousFunction (F n) A
      ∂(S.approximatingMeasure n : Measure S.Configuration) := by
  simpa using
    (physical_yang_mills_evenPeriodicWilsonOS_varying_approximating_nonneg_of_negativeHalfIndependent
      S.toPhysicalFourDimensionalYangMillsWeakLimit
      halfExtent 2 normalizedTracePowerVaryingPrimitiveWeakLimitTwoRankPositive
      beta hbeta
      (fun m => D.quadraticBoundedContinuousFunction (F m))
      interpolate interpolate_measurable approximatingMeasure_toMeasure_eq
      (fun m => normalizedTracePowerTietzeFullTarget halfExtent beta hbeta m j)
      (fun m => normalizedTracePowerTietzeFullTarget_negativeHalfIndependent
        halfExtent beta hbeta m j)
      (fun m A =>
        normalizedTracePower_varying_quadraticObservable_pullback_of_primitivePositiveHalfReadout
          S D halfExtent beta hbeta interpolate configurationReflection
          reflection_gauge_commute reflection_realization interpolate_reflection
          j F positive_readout m A)
      n)

/-- If the scale-dependent physical normalized-trace quadratic observables
converge uniformly to one bounded-continuous continuum observable, their exact
finite Wilson OS positivity passes to that continuum observable.

This removes the cross-scale identity requirement on the positive-time
observables themselves: only their quadratic bounded-continuous observables
must converge in sup norm. -/
theorem normalizedTracePower_varying_continuum_quadratic_nonneg_of_primitivePositiveHalfReadout_of_uniform
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (interpolate : ∀ n, (PeriodicHypercubicEvenEdge (halfExtent n) → Matrix.specialUnitaryGroup (Fin 2) ℂ) → S.Configuration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (approximatingMeasure_toMeasure_eq : ∀ n, (S.approximatingMeasure n : Measure S.Configuration) =
      Measure.map (interpolate n) (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n)) 2
        normalizedTracePowerVaryingPrimitiveWeakLimitTwoRankPositive (beta n) (hbeta n)).gibbsMeasure)
    (configurationReflection : Homeomorph S.Configuration S.Configuration)
    (reflection_gauge_commute : ∀ g A, configurationReflection (S.action g A) = S.action g (configurationReflection A))
    (reflection_realization : ∀ O, D.reflection O = physicalGaugeInvariantObservablePrecompAlgEquiv S
      configurationReflection reflection_gauge_commute O)
    (interpolate_reflection : ∀ n A, configurationReflection (interpolate n A) =
      interpolate n (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))
    (j : ℕ) (F : ℕ → D.positiveTimeSubalgebra)
    (positive_readout : ∀ n A, (((F n : D.positiveTimeSubalgebra) :
      physicalYangMillsGaugeInvariantObservableSubalgebra S) : BoundedContinuousFunction S.Configuration ℝ)
      (interpolate n A) = periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j
        ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A))
    (Olim : BoundedContinuousFunction S.Configuration ℝ)
    (huniform : Tendsto (fun n => ‖D.quadraticBoundedContinuousFunction (F n) - Olim‖) atTop (nhds 0)) :
    0 ≤ ∫ A, Olim A ∂(S.continuumMeasure : Measure S.Configuration) := by
  simpa using
    (physical_yang_mills_evenPeriodicWilsonOS_varying_continuum_nonneg_of_negativeHalfIndependent_of_uniform
      S.toPhysicalFourDimensionalYangMillsWeakLimit
      halfExtent 2 normalizedTracePowerVaryingPrimitiveWeakLimitTwoRankPositive
      beta hbeta
      (fun m => D.quadraticBoundedContinuousFunction (F m)) Olim huniform
      interpolate interpolate_measurable approximatingMeasure_toMeasure_eq
      (fun m => normalizedTracePowerTietzeFullTarget halfExtent beta hbeta m j)
      (fun m => normalizedTracePowerTietzeFullTarget_negativeHalfIndependent
        halfExtent beta hbeta m j)
      (fun m A =>
        normalizedTracePower_varying_quadraticObservable_pullback_of_primitivePositiveHalfReadout
          S D halfExtent beta hbeta interpolate configurationReflection
          reflection_gauge_commute reflection_realization interpolate_reflection
          j F positive_readout m A))

end

end MathlibAnalytic
end MGAP4D
