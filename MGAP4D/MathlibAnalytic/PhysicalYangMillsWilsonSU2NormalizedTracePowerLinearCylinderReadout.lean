import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerQuadraticCylinderVacuumNormalizedReadout
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerLinearCylinderReadoutTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerLinearCylinderReadoutNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerLinearCylinderReadoutTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerLinearCylinderReadoutCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerLinearCylinderReadoutSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerLinearCylinderReadoutMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerLinearCylinderReadoutBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerLinearCylinderReadoutSU2Nontrivial :
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

private abbrev normalizedTracePowerLinearCylinderRaw
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (j : ℕ) :=
  periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
    H beta hbeta j

/-- The two quadratic-cylinder identities required by polarization are already
forced by the two linear half-cylinder readouts: the positive readout of `F`
and the reflected readout of `Theta F`.  In particular the `F + 1` identity is
not independent model data; it follows from `AlgHom.map_add`, `map_one`, and
pointwise multiplication. -/
theorem normalizedTracePower_quadraticCylinder_of_linearHalfReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerLinearCylinderReadoutTwoRankPositive
        beta hbeta)
    (n j : ℕ)
    (F : D.positiveTimeSubalgebra)
    (hPositive : ∀ A,
      ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ)
          (Q.interpolate n A) =
        normalizedTracePowerLinearCylinderRaw
          (halfExtent n) (beta n) (hbeta n) j
          ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A))
    (hReflected : ∀ A,
      ((D.reflection
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ)
          (Q.interpolate n A) =
        normalizedTracePowerLinearCylinderRaw
          (halfExtent n) (beta n) (hbeta n) j
          ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction
            (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))) :
    (∀ A,
      D.quadraticBoundedContinuousFunction F (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (normalizedTracePowerLinearCylinderRaw
            (halfExtent n) (beta n) (hbeta n) j) A) ∧
    (∀ A,
      D.quadraticBoundedContinuousFunction
          (physicalYangMillsWilsonSU2PositiveTimeAddOne (D := D) F)
          (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (normalizedTracePowerLinearCylinderRaw
              (halfExtent n) (beta n) (hbeta n) j +
            (1 : BoundedContinuousFunction
              (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
                (halfExtent n) 2) ℝ)) A) := by
  constructor
  · intro A
    unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction
    unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable
    unfold periodicHypercubicEvenFullReflectedObservable
    change
      ((D.reflection
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) *
        ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) =
      normalizedTracePowerLinearCylinderRaw
          (halfExtent n) (beta n) (hbeta n) j
          ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A) *
        normalizedTracePowerLinearCylinderRaw
          (halfExtent n) (beta n) (hbeta n) j
          ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction
            (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))
    rw [hReflected A, hPositive A]
    ring
  · intro A
    unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction
    unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable
    unfold periodicHypercubicEvenFullReflectedObservable
    unfold physicalYangMillsWilsonSU2PositiveTimeAddOne
    change
      ((D.reflection
          ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) + 1) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) *
        (((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) + 1 :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) =
      (normalizedTracePowerLinearCylinderRaw
          (halfExtent n) (beta n) (hbeta n) j
          ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A) + 1) *
        (normalizedTracePowerLinearCylinderRaw
          (halfExtent n) (beta n) (hbeta n) j
          ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction
            (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)) + 1)
    rw [map_add, map_one]
    change
      (((D.reflection
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) + 1) *
        (((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) + 1) = _
    rw [hReflected A, hPositive A]
    ring

/-- Vacuum normalization plus the two linear half-cylinder readouts reconstructs
the exact coherent positive-half trace-power readout.  The shifted quadratic
identity is theorem-generated above rather than supplied independently. -/
theorem normalizedTracePower_positiveHalfPullback_eq_of_vacuumCompatibility_linearHalfReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerLinearCylinderReadoutTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n j : ℕ)
    (F : D.positiveTimeSubalgebra)
    (hPositive : ∀ A,
      ((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ)
          (Q.interpolate n A) =
        normalizedTracePowerLinearCylinderRaw
          (halfExtent n) (beta n) (hbeta n) j
          ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A))
    (hReflected : ∀ A,
      ((D.reflection
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ)
          (Q.interpolate n A) =
        normalizedTracePowerLinearCylinderRaw
          (halfExtent n) (beta n) (hbeta n) j
          ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction
            (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))) :
    Q.positiveHalfPullback n
        (⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule) =
      normalizedTracePowerLinearCylinderRaw
        (halfExtent n) (beta n) (hbeta n) j := by
  rcases Q.normalizedTracePower_quadraticCylinder_of_linearHalfReadout
      n j F hPositive hReflected with ⟨hQuadratic, hQuadraticAddOne⟩
  exact
    Q.normalizedTracePower_positiveHalfPullback_eq_of_vacuumCompatibility_quadraticCylinder
      hInvariant U n j F hQuadratic hQuadraticAddOne

/-- A family of linear positive/reflected cylinder readouts therefore puts every
normalized-trace polynomial raw actual-analysis vector in the exact physical
positive-time `L²` range. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_vacuumCompatibility_linearHalfReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerLinearCylinderReadoutTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (F : ℕ → D.positiveTimeSubalgebra)
    (hPositive : ∀ j A,
      (((F j : D.positiveTimeSubalgebra) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ)
          (Q.interpolate n A) =
        normalizedTracePowerLinearCylinderRaw
          (halfExtent n) (beta n) (hbeta n) j
          ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A))
    (hReflected : ∀ j A,
      ((D.reflection
          ((F j : D.positiveTimeSubalgebra) :
            physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ)
          (Q.interpolate n A) =
        normalizedTracePowerLinearCylinderRaw
          (halfExtent n) (beta n) (hbeta n) j
          ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction
            (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n) := by
  apply
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_vacuumCompatibility_quadraticCylinder
      hInvariant U n k c F
  · intro j A
    exact
      (Q.normalizedTracePower_quadraticCylinder_of_linearHalfReadout
        n j (F j) (hPositive j) (hReflected j)).1 A
  · intro j A
    exact
      (Q.normalizedTracePower_quadraticCylinder_of_linearHalfReadout
        n j (F j) (hPositive j) (hReflected j)).2 A

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
