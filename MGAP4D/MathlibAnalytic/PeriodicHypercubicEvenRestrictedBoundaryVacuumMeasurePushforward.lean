import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalEffectiveMeasurePushforward
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMomentRestrictionGaugeTransport

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumPushforwardNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumPushforwardTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumPushforwardCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumPushforwardSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumPushforwardMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumPushforwardBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The scalar law obtained by evaluating the actual finite Wilson OS boundary
vacuum moment on the full finite configuration is exactly the pushforward of
the effective shared-boundary law by that same boundary vacuum moment.

Together with
`periodicHypercubicEvenBoundaryRestriction_map_gibbsMeasure_eq_effectiveMeasure`,
this identifies the finite scalar physical readout with the effective boundary
measure on one literal Gibbs root.  No extra interpolation or gauge hypothesis
is introduced. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumMoment_map_gibbsMeasure_eq_map_effectiveMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumMoment
          H N hN beta hbeta)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment
          H N hN beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          H N hN beta hbeta) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  have hCoordinates :
      Measurable (P.boundaryFiberedCoordinates Gauge) :=
    P.boundaryFiberedCoordinates_measurable Gauge
  have hBoundary : Measurable P.boundaryRestriction := by
    have h := measurable_fst.comp hCoordinates
    simpa [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedCoordinates] using h
  have hVacuum :
      Measurable (periodicHypercubicEvenBoundaryVacuumMoment
        H N hN beta hbeta) :=
    periodicHypercubicEvenBoundaryVacuumMoment_measurable
      H N hN beta hbeta
  calc
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumMoment
          H N hN beta hbeta) C.gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment
          H N hN beta hbeta)
        (Measure.map P.boundaryRestriction C.gibbsMeasure) := by
      simpa [periodicHypercubicEvenRestrictedBoundaryVacuumMoment, P] using
        (Measure.map_map
          (μ := C.gibbsMeasure)
          hVacuum hBoundary).symm
    _ = Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment
          H N hN beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          H N hN beta hbeta) := by
      rw [periodicHypercubicEvenBoundaryRestriction_map_gibbsMeasure_eq_effectiveMeasure
        H N hN beta hbeta]

end

end MathlibAnalytic
end MGAP4D
