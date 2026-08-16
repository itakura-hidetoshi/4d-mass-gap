import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTemporalReadout
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumMeasurePushforward

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumTemporalLawNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumTemporalLawTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumTemporalLawCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumTemporalLawSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumTemporalLawMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumTemporalLawBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The raw full-configuration boundary-vacuum scalar readout is measurable. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumMoment_measurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumMoment
        H N hN beta hbeta) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  have hCoordinates :
      Measurable
        (P.boundaryFiberedCoordinates
          (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
    P.boundaryFiberedCoordinates_measurable
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  have hBoundary :
      Measurable
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          P.boundaryRestriction A) := by
    have h := measurable_fst.comp hCoordinates
    simpa [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedCoordinates] using h
  exact
    (periodicHypercubicEvenBoundaryVacuumMoment_measurable
      H N hN beta hbeta).comp hBoundary

/-- Every integer-time boundary-vacuum readout is measurable. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_measurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (t : ℤ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
        H N hN beta hbeta t) := by
  exact
    (periodicHypercubicEvenRestrictedBoundaryVacuumMoment_measurable
      H N hN beta hbeta).comp
      (periodicHypercubicIntegerTemporalConfigurationTranslation
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
        (PeriodicHypercubicEvenSideLength H) (-t)).measurable

/-- Every integer time slice has exactly the same scalar law under the actual
finite Wilson Gibbs measure as the reflection-fixed time-zero readout.

This is the measure-level stationarity theorem generated from exact finite
integer temporal translation invariance; no stationarity premise is added. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_map_gibbsMeasure_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (t : ℤ) :
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
          H N hN beta hbeta t)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumMoment
          H N hN beta hbeta)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  let T := periodicHypercubicIntegerTemporalConfigurationTranslation
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
    (PeriodicHypercubicEvenSideLength H) (-t)
  have hReadout :
      Measurable
        (periodicHypercubicEvenRestrictedBoundaryVacuumMoment
          H N hN beta hbeta) :=
    periodicHypercubicEvenRestrictedBoundaryVacuumMoment_measurable
      H N hN beta hbeta
  have hT : Measurable T := T.measurable
  calc
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
          H N hN beta hbeta t)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumMoment
          H N hN beta hbeta)
        (Measure.map T
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) := by
      simpa [periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime, T] using
        (Measure.map_map
          (μ := (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure)
          hReadout hT).symm
    _ = Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumMoment
          H N hN beta hbeta)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      rw [periodicHypercubicSpecialUnitary_gibbs_map_integerTemporalTranslation_eq_self
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta (-t)]
      rfl

/-- Consequently every integer time slice has the same literal pushforward law
from the effective shared-boundary measure.

This extends the previously proved same-root time-zero identification to all
integer Euclidean times. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_map_gibbsMeasure_eq_map_effectiveMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (t : ℤ) :
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
          H N hN beta hbeta t)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment
          H N hN beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          H N hN beta hbeta) := by
  rw [periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_map_gibbsMeasure_eq_zero]
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumMoment_map_gibbsMeasure_eq_map_effectiveMeasure
      H N hN beta hbeta

/-- A simultaneous family of time-indexed scalar readouts.  The index type is
arbitrary; finite index types give the finite-dimensional temporal cylinders
used by later path-law constructions. -/
noncomputable def periodicHypercubicEvenRestrictedBoundaryVacuumTemporalReadoutFamily
    {ι : Type*}
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (times : ι → ℤ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ι → ℝ :=
  fun i =>
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
      H N hN beta hbeta (times i) A

/-- A common lattice-time translation of the configuration is exactly absorbed
by a common translation of every cylinder time index. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalReadoutFamily_integerTemporal_covariant
    {ι : Type*}
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (times : ι → ℤ) (k : ℤ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalReadoutFamily
        H N hN beta hbeta (fun i => times i + k)
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
          (PeriodicHypercubicEvenSideLength H) k A) =
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalReadoutFamily
        H N hN beta hbeta times A := by
  funext i
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime_integerTemporal_covariant
      H N hN beta hbeta (times i) k A

end

end MathlibAnalytic
end MGAP4D
