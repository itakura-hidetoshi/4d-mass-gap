import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorTemporalCoordinateLimit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTemporalPathSymmetryLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorTemporalPathNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorTemporalPathTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorTemporalPathCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorTemporalPathSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorTemporalPathMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorTemporalPathBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- At every finite scale, shifting the entire stationary path by the canonical
floor step representing a target physical time leaves the embedded path law
exactly unchanged.

This is only the existing integer path symmetry evaluated at a scale-dependent
floor step; no real-parameter action on the path carrier is introduced. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding_embeddedMeasure_map_floorShift_eq_self
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (n : ℕ) (t : ℝ) :
    let E :=
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding
    (E.embeddedMeasure n).map
        (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_continuous
          (physicalTemporalFloorStep latticeSpacing t n)).measurable.aemeasurable =
      E.embeddedMeasure n := by
  dsimp only
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding_embeddedMeasure_map_shift_eq_self
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop n
      (physicalTemporalFloorStep latticeSpacing t n)

/-- Along any path-valued Prokhorov subsequence, the full path laws shifted by
floor steps realizing an arbitrary real target time converge to the same
continuum path law.

The conclusion is a varying-floor approximation statement.  It deliberately
does not identify these scale-dependent integer shifts with a fixed real-time
homeomorphism of the continuum path carrier. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPath_floorShiftedEmbeddedMeasure_tendsto
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
    let E :=
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding
    Tendsto
      (fun n : ℕ =>
        (E.embeddedMeasure (L.subsequence n)).map
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_continuous
            (physicalTemporalFloorStep latticeSpacing t (L.subsequence n))).measurable.aemeasurable)
      atTop (nhds L.continuumMeasure) := by
  dsimp only
  let E :=
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding
  have hSequence :
      (fun n : ℕ =>
        (E.embeddedMeasure (L.subsequence n)).map
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathShift_continuous
            (physicalTemporalFloorStep latticeSpacing t (L.subsequence n))).measurable.aemeasurable) =
      (fun n : ℕ => E.embeddedMeasure (L.subsequence n)) := by
    funext n
    exact
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding_embeddedMeasure_map_floorShift_eq_self
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop
        (L.subsequence n) t
  rw [hSequence]
  exact L.weakConvergence

end

end MathlibAnalytic
end MGAP4D
