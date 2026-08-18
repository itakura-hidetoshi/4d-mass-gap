import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitFromLocality
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerBoundaryPositiveOS
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerReflectionCylinderReadout

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

private theorem normalizedTracePowerWeakLimitCoherentReadoutTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerWeakLimitCoherentReadoutNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerWeakLimitCoherentReadoutTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerWeakLimitCoherentReadoutCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerWeakLimitCoherentReadoutSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerWeakLimitCoherentReadoutMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerWeakLimitCoherentReadoutBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerWeakLimitCoherentReadoutSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- A single physical positive-time observable which reads the same normalized
trace power at every finite Wilson scale has the exact quadratic pullback
required by the locality-to-weak-limit bridge.

Reflection compatibility supplies the reflected linear readout, the existing
linear-cylinder theorem supplies the quadratic identity, and the Tietze full
target is definitionally the positive-half target composed with positive
restriction.  No positivity premise is assumed here. -/
theorem normalizedTracePower_quadraticObservable_pullback_of_scaleCoherentPositiveHalfReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerWeakLimitCoherentReadoutTwoRankPositive
        beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (j : ℕ)
    (F : D.positiveTimeSubalgebra)
    (hReadout : ∀ n, NormalizedTracePowerPositiveHalfReadout Q n j F)
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    D.quadraticBoundedContinuousFunction F (Q.interpolate n A) =
      normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A *
        normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j
          (periodicHypercubicEvenConfigurationReflection (halfExtent n) A) := by
  have hquadratic :=
    (Q.normalizedTracePower_quadraticCylinder_of_linearHalfReadout
      n j F ((hReadout n).toLinearHalfReadout Q C n j F)).1 A
  calc
    D.quadraticBoundedContinuousFunction F (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
            (halfExtent n) (beta n) (hbeta n) j) A := hquadratic
    _ = normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j A *
        normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j
          (periodicHypercubicEvenConfigurationReflection (halfExtent n) A) := rfl

/-- Scale-coherent normalized-trace-power readout therefore gives nonnegativity
of every actual finite Wilson approximating quadratic expectation through the
#1777 locality theorem and the generic #1778 bridge. -/
theorem normalizedTracePower_approximating_quadratic_nonneg_of_scaleCoherentPositiveHalfReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerWeakLimitCoherentReadoutTwoRankPositive
        beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (j : ℕ)
    (F : D.positiveTimeSubalgebra)
    (hReadout : ∀ n, NormalizedTracePowerPositiveHalfReadout Q n j F)
    (n : ℕ) :
    0 ≤ ∫ A, D.quadraticBoundedContinuousFunction F A
      ∂(S.approximatingMeasure n : Measure S.Configuration) := by
  simpa using
    (physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_approximating_nonneg_of_negativeHalfIndependent
      S.toPhysicalFourDimensionalYangMillsWeakLimit
      halfExtent 2 normalizedTracePowerWeakLimitCoherentReadoutTwoRankPositive
      beta hbeta
      (D.quadraticBoundedContinuousFunction F)
      Q.interpolate Q.interpolate_measurable Q.approximatingMeasure_toMeasure_eq
      (fun m => normalizedTracePowerTietzeFullTarget halfExtent beta hbeta m j)
      (fun m => normalizedTracePowerTietzeFullTarget_negativeHalfIndependent
        halfExtent beta hbeta m j)
      (fun m A =>
        Q.normalizedTracePower_quadraticObservable_pullback_of_scaleCoherentPositiveHalfReadout
          C j F hReadout m A)
      n)

/-- The same fixed physical normalized-trace-power quadratic observable passes
to the continuum weak limit.  This is the concrete normalized-trace-power
instance of the locality-to-continuum OS nonnegativity route: no separate
finite reflection-positivity, density, range, or continuum positivity premise
is introduced. -/
theorem normalizedTracePower_continuum_quadratic_nonneg_of_scaleCoherentPositiveHalfReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerWeakLimitCoherentReadoutTwoRankPositive
        beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (j : ℕ)
    (F : D.positiveTimeSubalgebra)
    (hReadout : ∀ n, NormalizedTracePowerPositiveHalfReadout Q n j F) :
    0 ≤ ∫ A, D.quadraticBoundedContinuousFunction F A
      ∂(S.continuumMeasure : Measure S.Configuration) := by
  simpa using
    (physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_continuum_nonneg_of_negativeHalfIndependent
      S.toPhysicalFourDimensionalYangMillsWeakLimit
      halfExtent 2 normalizedTracePowerWeakLimitCoherentReadoutTwoRankPositive
      beta hbeta
      (D.quadraticBoundedContinuousFunction F)
      Q.interpolate Q.interpolate_measurable Q.approximatingMeasure_toMeasure_eq
      (fun n => normalizedTracePowerTietzeFullTarget halfExtent beta hbeta n j)
      (fun n => normalizedTracePowerTietzeFullTarget_negativeHalfIndependent
        halfExtent beta hbeta n j)
      (fun n A =>
        Q.normalizedTracePower_quadraticObservable_pullback_of_scaleCoherentPositiveHalfReadout
          C j F hReadout n A))

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
