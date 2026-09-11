import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerLinearCylinderReadout
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSConfigurationTimeTranslation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerReflectionCylinderReadoutTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerReflectionCylinderReadoutNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerReflectionCylinderReadoutTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerReflectionCylinderReadoutCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerReflectionCylinderReadoutSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerReflectionCylinderReadoutMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerReflectionCylinderReadoutBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerReflectionCylinderReadoutSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Kinematic compatibility between the common finite-Wilson interpolation and
the physical OS reflection.

This contains no positivity, density, range, Hamiltonian, or spectral input.
It says only that the abstract OS reflection is the actual configuration
precomposition and that interpolation commutes with the finite even-periodic
reflection. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta) where
  configurationReflection : Homeomorph S.Configuration S.Configuration
  reflection_gauge_commute : ∀ g A,
    configurationReflection (S.action g A) =
      S.action g (configurationReflection A)
  reflection_realization : ∀ O,
    D.reflection O =
      physicalGaugeInvariantObservablePrecompAlgEquiv S
        configurationReflection reflection_gauge_commute O
  interpolate_reflection : ∀ n A,
    configurationReflection (Q.interpolate n A) =
      Q.interpolate n
        (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev normalizedTracePowerReflectionCylinderRaw
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (j : ℕ) :=
  periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
    H beta hbeta j

/-- The single primitive pointwise input for one trace power: a physical
positive-time observable reads the desired finite positive-open-half cylinder. -/
structure NormalizedTracePowerPositiveHalfReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerReflectionCylinderReadoutTwoRankPositive
        beta hbeta)
    (n j : ℕ)
    (F : D.positiveTimeSubalgebra) : Prop where
  positive : ∀ A,
    ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ)
        (Q.interpolate n A) =
      normalizedTracePowerReflectionCylinderRaw
        (halfExtent n) (beta n) (hbeta n) j
        ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A)

/-- A theorem-generated family of positive-half trace-power cylinder readouts. -/
structure NormalizedTracePowerPositiveHalfReadoutFamily
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerReflectionCylinderReadoutTwoRankPositive
        beta hbeta)
    (n : ℕ) where
  observable : ℕ → D.positiveTimeSubalgebra
  readout : ∀ j, NormalizedTracePowerPositiveHalfReadout Q n j (observable j)

/-- Reflection/interpolation compatibility automatically supplies the reflected
half of a linear trace-power readout from the positive half alone. -/
def NormalizedTracePowerPositiveHalfReadout.toLinearHalfReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerReflectionCylinderReadoutTwoRankPositive
        beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (n j : ℕ)
    (F : D.positiveTimeSubalgebra)
    (R : NormalizedTracePowerPositiveHalfReadout Q n j F) :
    NormalizedTracePowerLinearHalfReadout Q n j F where
  positive := R.positive
  reflected := by
    intro A
    rw [C.reflection_realization]
    change
      ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ)
          (C.configurationReflection (Q.interpolate n A)) = _
    rw [C.interpolate_reflection n A]
    exact R.positive
      (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)

/-- Pointwise reflection compatibility upgrades a positive-half family to the
linear two-half family used by polarization. -/
def NormalizedTracePowerPositiveHalfReadoutFamily.toLinearHalfReadoutFamily
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerReflectionCylinderReadoutTwoRankPositive
        beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (n : ℕ)
    (R : NormalizedTracePowerPositiveHalfReadoutFamily Q n) :
    NormalizedTracePowerLinearHalfReadoutFamily Q n where
  observable := R.observable
  readout := fun j => (R.readout j).toLinearHalfReadout Q C n j (R.observable j)

/-- Consequently, after the already-established vacuum normalization, one
positive-half pointwise cylinder identity per trace power is enough to place
any normalized-trace polynomial raw actual-analysis vector in the exact
physical positive-time `L²` range. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_vacuumCompatibility_positiveHalfReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerReflectionCylinderReadoutTwoRankPositive
        beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (R : NormalizedTracePowerPositiveHalfReadoutFamily Q n) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n) := by
  exact
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_vacuumCompatibility_linearHalfReadout
      hInvariant U n k c (R.toLinearHalfReadoutFamily Q C n)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
