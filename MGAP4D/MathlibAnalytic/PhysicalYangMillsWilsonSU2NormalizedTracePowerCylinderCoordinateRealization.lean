import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveHalfCoordinateRealization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerCylinderCoordinateTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerCylinderCoordinateNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerCylinderCoordinateTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerCylinderCoordinateCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerCylinderCoordinateSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerCylinderCoordinateMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerCylinderCoordinateBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerCylinderCoordinateSU2Nontrivial :
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

private abbrev normalizedTracePowerCylinderCoordinateTarget
    (halfExtent : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n j : ℕ) :=
  periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
    (halfExtent n) (beta n) (hbeta n) j

/-- Pull a bounded-continuous finite positive-half target back along a continuous
continuum coordinate.  No gauge statement is built into the coordinate itself:
raw link coordinates are allowed to transform covariantly. -/
noncomputable def positiveHalfCylinderCoordinatePullback
    {n : ℕ}
    (coordinate : S.Configuration →
      PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2)
    (hcoordinate : Continuous coordinate)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ) :
    BoundedContinuousFunction S.Configuration ℝ :=
  { toContinuousMap :=
      ⟨fun A => f (coordinate A), f.continuous.comp hcoordinate⟩
    map_bounded' := by
      rcases f.bounded with ⟨C, hC⟩
      exact ⟨C, fun A B => hC (coordinate A) (coordinate B)⟩ }

@[simp] theorem positiveHalfCylinderCoordinatePullback_apply
    {n : ℕ}
    (coordinate : S.Configuration →
      PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2)
    (hcoordinate : Continuous coordinate)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ)
    (A : S.Configuration) :
    positiveHalfCylinderCoordinatePullback coordinate hcoordinate f A =
      f (coordinate A) :=
  rfl

/-- Target-specific continuum cylinder realization for the normalized trace
powers used by the actual Wilson excitation route.

The finite positive-open-half coordinate itself need not be gauge invariant.
Instead, only each required trace-power cylinder is required to be invariant
after precomposition with that coordinate.  This matches the physical geometry:
link variables are gauge covariant while Wilson trace observables are gauge
invariant.

The other primitive requirement is the literal same-root identity on the actual
finite interpolation.  Positive-time support is imposed only for the canonical
trace-power pullbacks, not for every bounded function of the coordinate. -/
structure PhysicalYangMillsWilsonSU2NormalizedTracePowerCylinderCoordinateRealization
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerCylinderCoordinateTwoRankPositive beta hbeta)
    (n : ℕ) where
  coordinate :
    S.Configuration →
      PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2
  coordinate_continuous : Continuous coordinate
  interpolate_coordinate : ∀ A,
    coordinate (Q.interpolate n A) =
      (periodicHypercubicEvenEdgeOrbitPartition
        (halfExtent n)).positiveRestriction A
  tracePower_gaugeInvariant : ∀ j g A,
    normalizedTracePowerCylinderCoordinateTarget halfExtent beta hbeta n j
        (coordinate (S.action g A)) =
      normalizedTracePowerCylinderCoordinateTarget halfExtent beta hbeta n j
        (coordinate A)
  tracePower_positiveTime : ∀ j,
    (⟨positiveHalfCylinderCoordinatePullback coordinate coordinate_continuous
          (normalizedTracePowerCylinderCoordinateTarget halfExtent beta hbeta n j),
        tracePower_gaugeInvariant j⟩ :
      physicalYangMillsGaugeInvariantObservableSubalgebra S) ∈
      D.positiveTimeSubalgebra

namespace PhysicalYangMillsWilsonSU2NormalizedTracePowerCylinderCoordinateRealization

variable
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerCylinderCoordinateTwoRankPositive beta hbeta}
    {n : ℕ}

/-- The canonical gauge-invariant physical observable generated by one required
normalized trace-power target. -/
noncomputable def gaugeInvariantTracePowerObservable
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerCylinderCoordinateRealization
      Q n)
    (j : ℕ) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S :=
  ⟨positiveHalfCylinderCoordinatePullback R.coordinate R.coordinate_continuous
      (normalizedTracePowerCylinderCoordinateTarget halfExtent beta hbeta n j),
    R.tracePower_gaugeInvariant j⟩

@[simp] theorem gaugeInvariantTracePowerObservable_apply
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerCylinderCoordinateRealization
      Q n)
    (j : ℕ) (A : S.Configuration) :
    ((R.gaugeInvariantTracePowerObservable j :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) A =
      normalizedTracePowerCylinderCoordinateTarget halfExtent beta hbeta n j
        (R.coordinate A) :=
  rfl

/-- Package the canonical target-specific pullback as an element of the already
existing physical positive-time algebra. -/
noncomputable def positiveTimeTracePowerObservable
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerCylinderCoordinateRealization
      Q n)
    (j : ℕ) : D.positiveTimeSubalgebra :=
  ⟨R.gaugeInvariantTracePowerObservable j, R.tracePower_positiveTime j⟩

/-- Same-root readout of the canonical target-specific physical observable on
the actual finite Wilson interpolation. -/
theorem positiveTimeTracePowerObservable_interpolate
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerCylinderCoordinateRealization
      Q n)
    (j : ℕ)
    (A : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (((R.positiveTimeTracePowerObservable j : D.positiveTimeSubalgebra) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ)
        (Q.interpolate n A) =
      normalizedTracePowerCylinderCoordinateTarget halfExtent beta hbeta n j
        ((periodicHypercubicEvenEdgeOrbitPartition
          (halfExtent n)).positiveRestriction A) := by
  change
    normalizedTracePowerCylinderCoordinateTarget halfExtent beta hbeta n j
        (R.coordinate (Q.interpolate n A)) = _
  rw [R.interpolate_coordinate A]

/-- The target-specific coordinate realization generates exactly the positive
half readout family required by the #1670/#1671 reconstruction route. -/
noncomputable def toPositiveHalfReadoutFamily
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerCylinderCoordinateRealization
      Q n) :
    NormalizedTracePowerPositiveHalfReadoutFamily Q n where
  observable := R.positiveTimeTracePowerObservable
  readout := by
    intro j
    refine ⟨?_⟩
    intro A
    exact R.positiveTimeTracePowerObservable_interpolate j A

end PhysicalYangMillsWilsonSU2NormalizedTracePowerCylinderCoordinateRealization

private abbrev normalizedTracePowerCylinderCoordinatePreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerCylinderCoordinateTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 normalizedTracePowerCylinderCoordinateTwoRankPositive
      beta hbeta Q.toWeakStarBridge hInvariant n

/-- Terminal reconstructed-Hamiltonian consequence of the physically weaker,
target-specific cylinder-coordinate realization.

All reflection, polarization, exact positive-half range, open-half `L²`
realization, nonzero reconstructed excitation and variational mass transport are
provided by the already established theorem chain. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_normalizedTracePowerCylinderCoordinateRealization
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerCylinderCoordinateTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (M : PhysicalYangMillsWilsonSU2NormalizedTracePolynomialMassInput
      halfExtent beta hbeta n k c)
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerCylinderCoordinateRealization
      Q n)
    (T : (normalizedTracePowerCylinderCoordinatePreHilbert
      Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  exact
    Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_vacuumCompatibility_positiveHalfReadout
      C hInvariant U n k c M R.toPositiveHalfReadoutFamily T hSelf

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
