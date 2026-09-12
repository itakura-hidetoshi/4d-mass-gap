import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTemporalPathCoordinateStationarity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedFloorTemporalApproximation

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorTemporalCoordinateNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorTemporalCoordinateTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorTemporalCoordinateCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorTemporalCoordinateSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorTemporalCoordinateMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorTemporalCoordinateBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- At every finite scale, evaluating the stationary path law at the canonical
floor step for a target physical time gives exactly the same effective-boundary
scalar probability law.

The floor selector only chooses an integer coordinate; no real-time invariance
is assumed. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure_map_floorCoordinate_eq_effectiveBoundaryVacuumProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure
      H N hN beta hbeta).map
        (measurable_pi_apply
          (physicalTemporalFloorStep latticeSpacing t n)).aemeasurable =
      periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
        H N hN beta hbeta := by
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure_map_coordinate_eq_effectiveBoundaryVacuumProbabilityMeasure
      H N hN beta hbeta
      (physicalTemporalFloorStep latticeSpacing t n)

/-- Along the same Prokhorov subsequence used by the path-valued continuum
limit, the physical times represented by the canonical floor coordinates still
converge to the prescribed real target time. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPath_floorPhysicalTime_tendsto_subsequence
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ((physicalTemporalFloorStep latticeSpacing t (L.subsequence n) : ℤ) : ℝ) *
          latticeSpacing (L.subsequence n))
      atTop (nhds t) := by
  exact
    (physicalTemporalFloorStep_tendsto
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero t).comp
      L.subsequence_strictMono.tendsto_atTop

/-- The law read at the varying floor coordinate for any real target time has
the same continuum weak limit as every fixed integer coordinate of the
path-valued limit.

Thus the floor approximation already transports scalar temporal stationarity
to arbitrary physical target times at the level of one-time laws, without
asserting a full real-parameter action on the path carrier. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPath_floorCoordinate_tendsto_continuum_coordinate
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (t : ℝ) (q : ℤ) :
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))).map
            (measurable_pi_apply
              (physicalTemporalFloorStep latticeSpacing t (L.subsequence n))).aemeasurable)
      atTop
      (nhds
        (L.continuumMeasure.map
          (measurable_pi_apply q).aemeasurable)) := by
  have h :=
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPath_effectiveBoundaryVacuumProbabilityMeasure_tendsto_coordinate
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L q
  have hSequence :
      (fun n : ℕ =>
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))).map
            (measurable_pi_apply
              (physicalTemporalFloorStep latticeSpacing t (L.subsequence n))).aemeasurable) =
      (fun n : ℕ =>
        periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))) := by
    funext n
    exact
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure_map_floorCoordinate_eq_effectiveBoundaryVacuumProbabilityMeasure
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n))
        latticeSpacing t (L.subsequence n)
  rw [hSequence]
  exact h

end

end MathlibAnalytic
end MGAP4D
