import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTemporalPathCoordinateLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumTemporalCoordinateStationarityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumTemporalCoordinateStationarityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumTemporalCoordinateStationarityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumTemporalCoordinateStationaritySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumTemporalCoordinateStationarityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumTemporalCoordinateStationarityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- All scalar coordinate limits extracted from one path-valued limit have the
same continuum probability law.

They are limits of the very same scalar embedded sequence along the very same
subsequence, so this is pure uniqueness of weak limits. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit_continuumMeasure_eq
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
    (s t : ℤ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L s).continuumMeasure =
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L t).continuumMeasure := by
  let Es :=
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding
  have hs :
      Tendsto
        (fun n : ℕ => Es.embeddedMeasure (L.subsequence n))
        atTop
        (nhds
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop L s).continuumMeasure) :=
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L s).weakConvergence
  have ht :
      Tendsto
        (fun n : ℕ => Es.embeddedMeasure (L.subsequence n))
        atTop
        (nhds
          (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop L t).continuumMeasure) :=
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L t).weakConvergence
  exact tendsto_nhds_unique hs ht

/-- Therefore every integer-time coordinate marginal of the continuum path law
is exactly the same probability measure. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPath_continuum_coordinate_eq
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
    (s t : ℤ) :
    L.continuumMeasure.map (measurable_pi_apply s).aemeasurable =
      L.continuumMeasure.map (measurable_pi_apply t).aemeasurable := by
  exact Eq.trans
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit_continuumMeasure
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L s).symm
    (Eq.trans
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit_continuumMeasure_eq
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L s t)
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit_continuumMeasure
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L t))

end

end MathlibAnalytic
end MGAP4D
