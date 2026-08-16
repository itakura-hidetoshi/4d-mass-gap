import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathShiftAction

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalEventualStationarityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalEventualStationarityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalEventualStationarityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalEventualStationaritySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalEventualStationarityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalEventualStationarityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Eventual exact stationarity of the embedded rational path laws along one
Prokhorov subsequence passes directly to exact stationarity of the continuum
rational path law.

The shifted sequence converges to the shifted continuum law by the continuous
mapping theorem.  Eventual equality with the unshifted sequence makes it also
converge to the original continuum law, and Hausdorff uniqueness of limits
identifies the two. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_continuum_shift_eq_of_eventually_embeddedMeasure_map_shift_eq_self
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
    (r : ℚ)
    (hEventually :
      ∀ᶠ n : ℕ in atTop,
        (((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure
            (L.subsequence n)).map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable) =
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure
            (L.subsequence n)) :
    L.continuumMeasure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable =
      L.continuumMeasure := by
  have hShifted :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_shiftedEmbeddedMeasure_tendsto
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L r
  have hSameLimit :
      Tendsto
        (fun n : ℕ =>
          ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure
              (L.subsequence n)).map
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable)
        atTop
        (nhds L.continuumMeasure) := by
    exact Tendsto.congr' hEventually.symm L.weakConvergence
  exact tendsto_nhds_unique hShifted hSameLimit

end

end MathlibAnalytic
end MGAP4D
