import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerVaryingPrimitiveWeakLimitReadout
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerCylinderCoordinateRealization

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

noncomputable section

private theorem primitiveNormalizedTraceCylinderWeakLimitTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance primitiveNormalizedTraceCylinderWeakLimitNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance primitiveNormalizedTraceCylinderWeakLimitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance primitiveNormalizedTraceCylinderWeakLimitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance primitiveNormalizedTraceCylinderWeakLimitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance primitiveNormalizedTraceCylinderWeakLimitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance primitiveNormalizedTraceCylinderWeakLimitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance primitiveNormalizedTraceCylinderWeakLimitSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Primitive SU(2) finite-to-physical weak-limit geometry.

This packages only the actual interpolation, its pushforward identification with
the finite Wilson Gibbs laws, and realization of physical OS reflection by a
configuration reflection compatible with interpolation.  It contains no
positive-time pullback, reflection-positivity, density, range, Hamiltonian, or
spectral premise. -/
structure PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n) where
  interpolate : ∀ n, (PeriodicHypercubicEvenEdge (halfExtent n) →
    Matrix.specialUnitaryGroup (Fin 2) ℂ) → S.Configuration
  interpolate_measurable : ∀ n, Measurable (interpolate n)
  approximatingMeasure_toMeasure_eq : ∀ n,
    (S.approximatingMeasure n : Measure S.Configuration) = Measure.map (interpolate n)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n)) 2
        primitiveNormalizedTraceCylinderWeakLimitTwoRankPositive
        (beta n) (hbeta n)).gibbsMeasure
  configurationReflection : Homeomorph S.Configuration S.Configuration
  reflection_gauge_commute : ∀ g A, configurationReflection (S.action g A) =
    S.action g (configurationReflection A)
  reflection_realization : ∀ O, D.reflection O =
    physicalGaugeInvariantObservablePrecompAlgEquiv S
      configurationReflection reflection_gauge_commute O
  interpolate_reflection : ∀ n A, configurationReflection (interpolate n A) =
    interpolate n (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)

private abbrev primitiveNormalizedTraceCylinderTarget
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n j : ℕ) :=
  periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
    (halfExtent n) (beta n) (hbeta n) j

/-- A target-specific continuum cylinder-coordinate realization at one scale,
independent of the stronger coherent all-observable pullback package.

The coordinate itself may transform covariantly.  Only the normalized-trace
cylinders required by the physical excitation route are required to be gauge
invariant after precomposition and to belong to the already-defined physical
positive-time algebra. -/
structure PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderCoordinateRealization
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (G : PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry S D halfExtent beta hbeta)
    (n : ℕ) where
  coordinate : S.Configuration →
    PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration (halfExtent n) 2
  coordinate_continuous : Continuous coordinate
  interpolate_coordinate : ∀ A, coordinate (G.interpolate n A) =
    (periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A
  tracePower_gaugeInvariant : ∀ j g A,
    primitiveNormalizedTraceCylinderTarget halfExtent beta hbeta n j
        (coordinate (S.action g A)) =
      primitiveNormalizedTraceCylinderTarget halfExtent beta hbeta n j (coordinate A)
  tracePower_positiveTime : ∀ j,
    (⟨positiveHalfCylinderCoordinatePullback coordinate coordinate_continuous
          (primitiveNormalizedTraceCylinderTarget halfExtent beta hbeta n j),
        tracePower_gaugeInvariant j⟩ :
      physicalYangMillsGaugeInvariantObservableSubalgebra S) ∈ D.positiveTimeSubalgebra

namespace PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderCoordinateRealization

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {G : PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry S D halfExtent beta hbeta}
    {n : ℕ}

/-- The canonical gauge-invariant normalized-trace cylinder generated by the
primitive physical coordinate readback. -/
noncomputable def gaugeInvariantTracePowerObservable
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderCoordinateRealization G n)
    (j : ℕ) : physicalYangMillsGaugeInvariantObservableSubalgebra S :=
  ⟨positiveHalfCylinderCoordinatePullback R.coordinate R.coordinate_continuous
      (primitiveNormalizedTraceCylinderTarget halfExtent beta hbeta n j),
    R.tracePower_gaugeInvariant j⟩

@[simp] theorem gaugeInvariantTracePowerObservable_apply
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderCoordinateRealization G n)
    (j : ℕ) (A : S.Configuration) :
    ((R.gaugeInvariantTracePowerObservable j :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) A =
      primitiveNormalizedTraceCylinderTarget halfExtent beta hbeta n j (R.coordinate A) :=
  rfl

/-- Package the target-specific cylinder as a physical positive-time observable. -/
noncomputable def positiveTimeTracePowerObservable
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderCoordinateRealization G n)
    (j : ℕ) : D.positiveTimeSubalgebra :=
  ⟨R.gaugeInvariantTracePowerObservable j, R.tracePower_positiveTime j⟩

/-- Exact same-root normalized-trace readout on the actual finite interpolation. -/
theorem positiveTimeTracePowerObservable_interpolate
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderCoordinateRealization G n)
    (j : ℕ)
    (A : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (((R.positiveTimeTracePowerObservable j : D.positiveTimeSubalgebra) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) (G.interpolate n A) =
      primitiveNormalizedTraceCylinderTarget halfExtent beta hbeta n j
        ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A) := by
  change primitiveNormalizedTraceCylinderTarget halfExtent beta hbeta n j
      (R.coordinate (G.interpolate n A)) = _
  rw [R.interpolate_coordinate A]

end PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderCoordinateRealization

/-- Primitive target-specific cylinder coordinates at every scale reduce
continuum normalized-trace OS positivity to one analytic cross-scale condition:
uniform convergence of the theorem-generated physical quadratic observables.

The stronger `PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback`
is absent from both the hypotheses and the conclusion. -/
theorem normalizedTracePower_varying_continuum_quadratic_nonneg_of_primitiveCylinderCoordinateRealization_of_uniform
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (G : PhysicalYangMillsWilsonSU2PrimitiveWeakLimitGeometry S D halfExtent beta hbeta)
    (j : ℕ)
    (R : ∀ n, PhysicalYangMillsWilsonSU2NormalizedTracePowerPrimitiveCylinderCoordinateRealization G n)
    (Olim : BoundedContinuousFunction S.Configuration ℝ)
    (huniform : Tendsto (fun n => ‖D.quadraticBoundedContinuousFunction
      ((R n).positiveTimeTracePowerObservable j) - Olim‖) atTop (nhds 0)) :
    0 ≤ ∫ A, Olim A ∂(S.continuumMeasure : Measure S.Configuration) := by
  apply normalizedTracePower_varying_continuum_quadratic_nonneg_of_primitivePositiveHalfReadout_of_uniform
    S D halfExtent beta hbeta G.interpolate G.interpolate_measurable
    G.approximatingMeasure_toMeasure_eq G.configurationReflection
    G.reflection_gauge_commute G.reflection_realization G.interpolate_reflection
    j (fun n => (R n).positiveTimeTracePowerObservable j)
  · intro n A
    exact (R n).positiveTimeTracePowerObservable_interpolate j A
  · exact huniform

end

end MathlibAnalytic
end MGAP4D
