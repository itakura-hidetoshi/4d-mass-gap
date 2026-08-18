import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitFromLocality
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerBoundaryPositiveOS
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSConfigurationTimeTranslation

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

private theorem normalizedTracePowerPrimitiveWeakLimitReadoutTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerPrimitiveWeakLimitReadoutNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerPrimitiveWeakLimitReadoutTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerPrimitiveWeakLimitReadoutCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerPrimitiveWeakLimitReadoutSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerPrimitiveWeakLimitReadoutMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerPrimitiveWeakLimitReadoutBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerPrimitiveWeakLimitReadoutSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- A primitive scale-coherent positive-half normalized-trace readout gives the
exact physical quadratic pullback needed by the locality-to-weak-limit bridge.

Unlike the coherent positive-time pullback package, this theorem assumes no
finite bridge for arbitrary positive-time observables.  It uses only one fixed
physical positive-time observable, the actual interpolation family, realization
of physical OS reflection by configuration reflection, and the literal
positive-half readout of that same observable at every lattice scale. -/
theorem normalizedTracePower_quadraticObservable_pullback_of_primitivePositiveHalfReadout
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
    (j : ℕ) (F : D.positiveTimeSubalgebra)
    (positive_readout : ∀ n A,
      ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) (interpolate n A) =
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j
        ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A))
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge (halfExtent n) → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    D.quadraticBoundedContinuousFunction F (interpolate n A) =
      normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A *
        normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j
          (periodicHypercubicEvenConfigurationReflection (halfExtent n) A) := by
  have hreflected :
      ((D.reflection
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
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
      ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ)
          (configurationReflection (interpolate n A)) = _
    rw [interpolate_reflection n A]
    exact positive_readout n
      (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)
  calc
    D.quadraticBoundedContinuousFunction F (interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
            (halfExtent n) (beta n) (hbeta n) j) A := by
      unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction
      unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable
      unfold periodicHypercubicEvenFullReflectedObservable
      change
        ((D.reflection
            (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
            physicalYangMillsGaugeInvariantObservableSubalgebra S) :
            BoundedContinuousFunction S.Configuration ℝ) (interpolate n A) *
          ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
            BoundedContinuousFunction S.Configuration ℝ) (interpolate n A) = _
      rw [hreflected, positive_readout n A]
      ring
    _ = normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A *
        normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j
          (periodicHypercubicEvenConfigurationReflection (halfExtent n) A) := rfl

/-- Primitive normalized-trace readout data yields nonnegativity of every
physical approximating quadratic expectation by the actual finite Wilson Gibbs
theorem.  No coherent all-observable pullback, finite positivity premise,
density premise, or range premise is used. -/
theorem normalizedTracePower_approximating_quadratic_nonneg_of_primitivePositiveHalfReadout
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (interpolate : ∀ n, (PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) → S.Configuration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (approximatingMeasure_toMeasure_eq : ∀ n,
      (S.approximatingMeasure n : Measure S.Configuration) = Measure.map (interpolate n)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n)) 2
          normalizedTracePowerPrimitiveWeakLimitReadoutTwoRankPositive
          (beta n) (hbeta n)).gibbsMeasure)
    (configurationReflection : Homeomorph S.Configuration S.Configuration)
    (reflection_gauge_commute : ∀ g A, configurationReflection (S.action g A) =
      S.action g (configurationReflection A))
    (reflection_realization : ∀ O, D.reflection O =
      physicalGaugeInvariantObservablePrecompAlgEquiv S
        configurationReflection reflection_gauge_commute O)
    (interpolate_reflection : ∀ n A, configurationReflection (interpolate n A) =
      interpolate n (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))
    (j : ℕ) (F : D.positiveTimeSubalgebra)
    (positive_readout : ∀ n A,
      ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) (interpolate n A) =
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j
        ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A))
    (n : ℕ) :
    0 ≤ ∫ A, D.quadraticBoundedContinuousFunction F A
      ∂(S.approximatingMeasure n : Measure S.Configuration) := by
  simpa using
    (physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_approximating_nonneg_of_negativeHalfIndependent
      S.toPhysicalFourDimensionalYangMillsWeakLimit
      halfExtent 2 normalizedTracePowerPrimitiveWeakLimitReadoutTwoRankPositive
      beta hbeta
      (D.quadraticBoundedContinuousFunction F)
      interpolate interpolate_measurable approximatingMeasure_toMeasure_eq
      (fun m => normalizedTracePowerTietzeFullTarget halfExtent beta hbeta m j)
      (fun m => normalizedTracePowerTietzeFullTarget_negativeHalfIndependent
        halfExtent beta hbeta m j)
      (fun m A =>
        normalizedTracePower_quadraticObservable_pullback_of_primitivePositiveHalfReadout
          S D halfExtent beta hbeta interpolate configurationReflection
          reflection_gauge_commute reflection_realization interpolate_reflection
          j F positive_readout m A)
      n)

/-- The same primitive exact readout therefore passes normalized-trace-power OS
quadratic nonnegativity to the continuum weak limit.  This is the concrete
same-root route from the fixed physical observable to #1777 locality and #1778
weak-limit transport without assuming the stronger coherent positive-time
pullback package. -/
theorem normalizedTracePower_continuum_quadratic_nonneg_of_primitivePositiveHalfReadout
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (interpolate : ∀ n, (PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) → S.Configuration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (approximatingMeasure_toMeasure_eq : ∀ n,
      (S.approximatingMeasure n : Measure S.Configuration) = Measure.map (interpolate n)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n)) 2
          normalizedTracePowerPrimitiveWeakLimitReadoutTwoRankPositive
          (beta n) (hbeta n)).gibbsMeasure)
    (configurationReflection : Homeomorph S.Configuration S.Configuration)
    (reflection_gauge_commute : ∀ g A, configurationReflection (S.action g A) =
      S.action g (configurationReflection A))
    (reflection_realization : ∀ O, D.reflection O =
      physicalGaugeInvariantObservablePrecompAlgEquiv S
        configurationReflection reflection_gauge_commute O)
    (interpolate_reflection : ∀ n A, configurationReflection (interpolate n A) =
      interpolate n (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))
    (j : ℕ) (F : D.positiveTimeSubalgebra)
    (positive_readout : ∀ n A,
      ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) (interpolate n A) =
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j
        ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A)) :
    0 ≤ ∫ A, D.quadraticBoundedContinuousFunction F A
      ∂(S.continuumMeasure : Measure S.Configuration) := by
  simpa using
    (physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_continuum_nonneg_of_negativeHalfIndependent
      S.toPhysicalFourDimensionalYangMillsWeakLimit
      halfExtent 2 normalizedTracePowerPrimitiveWeakLimitReadoutTwoRankPositive
      beta hbeta
      (D.quadraticBoundedContinuousFunction F)
      interpolate interpolate_measurable approximatingMeasure_toMeasure_eq
      (fun n => normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j)
      (fun n => normalizedTracePowerTietzeFullTarget_negativeHalfIndependent
        halfExtent beta hbeta n j)
      (fun n A =>
        normalizedTracePower_quadraticObservable_pullback_of_primitivePositiveHalfReadout
          S D halfExtent beta hbeta interpolate configurationReflection
          reflection_gauge_commute reflection_realization interpolate_reflection
          j F positive_readout n A))

end

end MathlibAnalytic
end MGAP4D
