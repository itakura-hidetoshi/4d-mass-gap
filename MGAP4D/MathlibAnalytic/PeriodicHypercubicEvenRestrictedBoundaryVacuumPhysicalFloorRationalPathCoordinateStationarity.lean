import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalCoordinateStationarityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalCoordinateStationarityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalCoordinateStationarityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalCoordinateStationaritySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalCoordinateStationarityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalCoordinateStationarityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- All scalar coordinate limits extracted from one rational-path-valued limit
have the same continuum probability law.

Every rational coordinate limit uses the very same effective-boundary scalar
embedded sequence along the very same subsequence, so the proof is pure
uniqueness of weak limits. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit_continuumMeasure_eq
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
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (q r : ℚ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L q).continuumMeasure =
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L r).continuumMeasure := by
  let Es :=
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding
  have hq :
      Tendsto
        (fun n : ℕ => Es.embeddedMeasure (L.subsequence n))
        atTop
        (nhds
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop L q).continuumMeasure) :=
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L q).weakConvergence
  have hr :
      Tendsto
        (fun n : ℕ => Es.embeddedMeasure (L.subsequence n))
        atTop
        (nhds
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop L r).continuumMeasure) :=
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L r).weakConvergence
  exact tendsto_nhds_unique hq hr

/-- Therefore every rational-time coordinate marginal of the continuum rational
path law is exactly the same probability measure.

This is stationarity of all one-time rational marginals.  It does not assert a
full rational- or real-time shift action on the continuum path law. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_continuum_coordinate_eq
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
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (q r : ℚ) :
    L.continuumMeasure.map (measurable_pi_apply q).aemeasurable =
      L.continuumMeasure.map (measurable_pi_apply r).aemeasurable := by
  exact Eq.trans
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit_continuumMeasure
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L q).symm
    (Eq.trans
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit_continuumMeasure_eq
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L q r)
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit_continuumMeasure
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L r))

end

end MathlibAnalytic
end MGAP4D
