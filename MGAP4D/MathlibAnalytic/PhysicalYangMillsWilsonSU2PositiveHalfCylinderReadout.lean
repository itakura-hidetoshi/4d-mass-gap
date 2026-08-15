import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerReflectionCylinderReadout
import Mathlib.Topology.Sequences
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem positiveHalfCylinderReadoutTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance positiveHalfCylinderReadoutNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveHalfCylinderReadoutTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveHalfCylinderReadoutCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveHalfCylinderReadoutSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveHalfCylinderReadoutMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveHalfCylinderReadoutBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveHalfCylinderReadoutSU2Nontrivial :
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

/-- A concrete positive-time physical observable whose finite Wilson pullback
reads an arbitrary bounded-continuous target on the positive open half.

Unlike the earlier trace-power-specific readout structures, the target `f` is
completely arbitrary.  The only primitive datum is the positive-half pointwise
identity.  Reflection, quadratic polarization, exact pullback range membership,
and closure statements are derived below from existing OS compatibility. -/
structure PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadoutTwoRankPositive beta hbeta)
    (n : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ) where
  observable : D.positiveTimeSubalgebra
  positive : ∀ A,
    ((observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ)
        (Q.interpolate n A) =
      f ((periodicHypercubicEvenEdgeOrbitPartition
        (halfExtent n)).positiveRestriction A)

namespace PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout

variable
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadoutTwoRankPositive beta hbeta}
    {n : ℕ}
    {f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ}

/-- Reflection/interpolation compatibility supplies the reflected-half readout
for an arbitrary positive-half cylinder target.  Thus reflected readout data are
not an independent model assumption. -/
theorem reflected
    (R : PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n f)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (A : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((D.reflection
        (R.observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ)
        (Q.interpolate n A) =
      f ((periodicHypercubicEvenEdgeOrbitPartition
        (halfExtent n)).positiveRestriction
          (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)) := by
  rw [C.reflection_realization]
  change
    ((R.observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
      BoundedContinuousFunction S.Configuration ℝ)
        (C.configurationReflection (Q.interpolate n A)) = _
  rw [C.interpolate_reflection n A]
  exact R.positive
    (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)

end PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout

/-- The two quadratic identities needed by polarization follow algebraically
from one arbitrary positive-half cylinder readout and the existing
reflection/interpolation compatibility.  In particular the shifted `F + 1`
identity is theorem-generated rather than supplied as separate physical data. -/
theorem positiveHalfCylinder_quadratic_of_readout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadoutTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (n : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ)
    (R : PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n f) :
    (∀ A,
      D.quadraticBoundedContinuousFunction R.observable (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n) f A) ∧
    (∀ A,
      D.quadraticBoundedContinuousFunction
          (physicalYangMillsWilsonSU2PositiveTimeAddOne
            (D := D) R.observable)
          (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (f + (1 : BoundedContinuousFunction
            (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
              (halfExtent n) 2) ℝ)) A) := by
  constructor
  · intro A
    unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction
    unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable
    unfold periodicHypercubicEvenFullReflectedObservable
    change
      ((D.reflection
          (R.observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) *
        ((R.observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) =
      f ((periodicHypercubicEvenEdgeOrbitPartition
          (halfExtent n)).positiveRestriction A) *
        f ((periodicHypercubicEvenEdgeOrbitPartition
          (halfExtent n)).positiveRestriction
            (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))
    rw [R.reflected C A, R.positive A]
    ring
  · intro A
    unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction
    unfold PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable
    unfold periodicHypercubicEvenFullReflectedObservable
    unfold physicalYangMillsWilsonSU2PositiveTimeAddOne
    change
      ((D.reflection
          ((R.observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) + 1) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) *
        (((R.observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) + 1 :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) =
      (f ((periodicHypercubicEvenEdgeOrbitPartition
          (halfExtent n)).positiveRestriction A) + 1) *
        (f ((periodicHypercubicEvenEdgeOrbitPartition
          (halfExtent n)).positiveRestriction
            (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)) + 1)
    rw [map_add, map_one]
    change
      (((D.reflection
          (R.observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) + 1) *
        (((R.observable : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (Q.interpolate n A) + 1) = _
    rw [R.reflected C A, R.positive A]
    ring

/-- An arbitrary positive-half cylinder readout therefore reconstructs its
exact coherent positive-half pullback after the already-established vacuum-unit
normalization.  No multiplicativity of `positiveHalfPullback` is used. -/
theorem positiveHalfPullback_eq_of_vacuumCompatibility_positiveHalfCylinderReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadoutTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ)
    (R : PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n f) :
    Q.positiveHalfPullback n
        (⟨R.observable.1, R.observable.2⟩ :
          D.positiveTimeSubalgebra.toSubmodule) = f := by
  rcases Q.positiveHalfCylinder_quadratic_of_readout C n f R with
    ⟨hQuadratic, hQuadraticAddOne⟩
  exact
    Q.positiveHalfPullback_eq_of_quadratic_polarization
      n
      (Q.positiveHalfPullback_positiveTimeUnit_eq_one_of_vacuumCompatibility
        hInvariant U n)
      R.observable f hQuadratic hQuadraticAddOne

/-- Hence one concrete positive-half cylinder readout gives exact range
membership for an arbitrary bounded-continuous open-half target. -/
theorem positiveHalfCylinderReadout_mem_positiveHalfPullbackRange
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadoutTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ)
    (R : PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n f) :
    f ∈ LinearMap.range (Q.positiveHalfPullback n) := by
  refine ⟨(⟨R.observable.1, R.observable.2⟩ :
    D.positiveTimeSubalgebra.toSubmodule), ?_⟩
  exact
    Q.positiveHalfPullback_eq_of_vacuumCompatibility_positiveHalfCylinderReadout
      C hInvariant U n f R

/-- A sequence of genuine positive-half physical cylinder readouts converging
uniformly to `f` places `f` in the sup-norm closure of the coherent pullback
range.  Mathlib's sequential characterization of closure supplies the entire
approximation step; no chosen preimage of the limit is needed. -/
theorem mem_positiveHalfPullbackRangeClosure_of_tendsto_positiveHalfCylinderReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfCylinderReadoutTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ)
    (u : ℕ → BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ)
    (R : ∀ m,
      PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n (u m))
    (hu : Tendsto u atTop (𝓝 f)) :
    f ∈ closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨u, ?_, hu⟩
  intro m
  exact
    Q.positiveHalfCylinderReadout_mem_positiveHalfPullbackRange
      C hInvariant U n (u m) (R m)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
