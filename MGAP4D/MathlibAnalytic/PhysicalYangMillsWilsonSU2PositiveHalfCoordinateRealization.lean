import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveHalfReadoutMassEndpoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem positiveHalfCoordinateRealizationTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance positiveHalfCoordinateRealizationNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveHalfCoordinateRealizationTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveHalfCoordinateRealizationCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveHalfCoordinateRealizationSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveHalfCoordinateRealizationMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveHalfCoordinateRealizationBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveHalfCoordinateRealizationSU2Nontrivial :
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

private abbrev PositiveHalfCoordinateTarget
    (halfExtent : ℕ → ℕ) (n : ℕ) :=
  BoundedContinuousFunction
    (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) 2) ℝ

/-- A concrete continuum readback of the actual finite positive-open-half
configuration at one Wilson scale.

This is deliberately kinematic.  It asks for one continuous finite-coordinate
map on the already-existing physical continuum carrier, fixed by the supplied
physical gauge symmetry, and for the literal same-root identity on the actual
finite interpolation.  It contains no OS positivity, density, range,
Hamiltonian or spectral input. -/
structure PhysicalYangMillsWilsonSU2PositiveHalfCoordinateRealization
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCoordinateRealizationTwoRankPositive beta hbeta)
    (n : ℕ) where
  coordinate :
    S.Configuration →
      PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2
  coordinate_continuous : Continuous coordinate
  coordinate_gaugeInvariant : ∀ g A,
    coordinate (S.action g A) = coordinate A
  interpolate_coordinate : ∀ A,
    coordinate (Q.interpolate n A) =
      (periodicHypercubicEvenEdgeOrbitPartition
        (halfExtent n)).positiveRestriction A

namespace PhysicalYangMillsWilsonSU2PositiveHalfCoordinateRealization

variable
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCoordinateRealizationTwoRankPositive beta hbeta}
    {n : ℕ}

/-- Pull a bounded-continuous finite positive-half target back along one concrete
continuum coordinate realization.  Gauge invariance is theorem-generated from
the coordinate invariance; no separate observable-level invariance premise is
needed. -/
noncomputable def gaugeInvariantPullback
    (R : PhysicalYangMillsWilsonSU2PositiveHalfCoordinateRealization Q n)
    (f : PositiveHalfCoordinateTarget halfExtent n) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S := by
  let O : BoundedContinuousFunction S.Configuration ℝ :=
    { toContinuousMap :=
        ⟨fun A => f (R.coordinate A),
          f.continuous.comp R.coordinate_continuous⟩
      map_bounded' := by
        rcases f.bounded with ⟨C, hC⟩
        exact ⟨C, fun A B => hC (R.coordinate A) (R.coordinate B)⟩ }
  refine ⟨O, ?_⟩
  intro g A
  change f (R.coordinate (S.action g A)) = f (R.coordinate A)
  rw [R.coordinate_gaugeInvariant g A]

@[simp] theorem gaugeInvariantPullback_apply
    (R : PhysicalYangMillsWilsonSU2PositiveHalfCoordinateRealization Q n)
    (f : PositiveHalfCoordinateTarget halfExtent n)
    (A : S.Configuration) :
    ((R.gaugeInvariantPullback f :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) A =
      f (R.coordinate A) :=
  rfl

/-- Same-root evaluation of every coordinate-pulled physical observable on the
actual finite Wilson interpolation. -/
theorem gaugeInvariantPullback_interpolate
    (R : PhysicalYangMillsWilsonSU2PositiveHalfCoordinateRealization Q n)
    (f : PositiveHalfCoordinateTarget halfExtent n)
    (A : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((R.gaugeInvariantPullback f :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) =
      f ((periodicHypercubicEvenEdgeOrbitPartition
        (halfExtent n)).positiveRestriction A) := by
  change f (R.coordinate (Q.interpolate n A)) = _
  rw [R.interpolate_coordinate A]

end PhysicalYangMillsWilsonSU2PositiveHalfCoordinateRealization

/-- Target-specific analytic enhancement of one continuum positive-half
coordinate readback.

Only the normalized-trace-power pullbacks actually needed by the reconstructed
excitation route are required to belong to the pre-existing physical
positive-time subalgebra.  This is strictly weaker than asking every bounded
function of the coordinate to be positive-time and avoids any global
surjectivity statement. -/
structure PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveHalfCoordinateRealization
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCoordinateRealizationTwoRankPositive beta hbeta)
    (n : ℕ)
    extends PhysicalYangMillsWilsonSU2PositiveHalfCoordinateRealization Q n where
  positiveTime : ∀ j,
    toPhysicalYangMillsWilsonSU2PositiveHalfCoordinateRealization.gaugeInvariantPullback
      (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j) ∈
      D.positiveTimeSubalgebra

namespace PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveHalfCoordinateRealization

variable
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCoordinateRealizationTwoRankPositive beta hbeta}
    {n : ℕ}

/-- A concrete continuum coordinate realization generates the exact
positive-half readout family consumed by the #1670 target-specific endpoint. -/
noncomputable def toPositiveHalfReadoutFamily
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveHalfCoordinateRealization
      Q n) :
    NormalizedTracePowerPositiveHalfReadoutFamily Q n where
  observable := fun j =>
    ⟨R.toPhysicalYangMillsWilsonSU2PositiveHalfCoordinateRealization.gaugeInvariantPullback
        (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) j),
      R.positiveTime j⟩
  readout := by
    intro j
    refine ⟨?_⟩
    intro A
    exact
      R.toPhysicalYangMillsWilsonSU2PositiveHalfCoordinateRealization.gaugeInvariantPullback_interpolate
        (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) j) A

end PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveHalfCoordinateRealization

private abbrev positiveHalfCoordinateRealizationPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCoordinateRealizationTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 positiveHalfCoordinateRealizationTwoRankPositive
      beta hbeta Q.toWeakStarBridge hInvariant n

/-- Terminal reconstructed-Hamiltonian consequence of one continuum
positive-half coordinate realization plus positive-time membership of the
required normalized trace powers.

The pointwise cylinder identities, reflected-half identities, quadratic
polarization, exact positive-half range and `L²` realization are all generated
by existing theorems. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_positiveHalfCoordinateRealization
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCoordinateRealizationTwoRankPositive beta hbeta)
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
    (R : PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveHalfCoordinateRealization
      Q n)
    (T : (positiveHalfCoordinateRealizationPreHilbert
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
