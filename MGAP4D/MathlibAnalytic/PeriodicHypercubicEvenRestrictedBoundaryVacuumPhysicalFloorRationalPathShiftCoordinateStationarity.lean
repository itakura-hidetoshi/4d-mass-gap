import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathShiftAction

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalShiftCoordinateNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalShiftCoordinateTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalShiftCoordinateCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalShiftCoordinateSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalShiftCoordinateMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalShiftCoordinateBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Every one-coordinate cylinder of the continuum rational path law is
unchanged after a rational path translation.

This is generated from the already proved equality of all rational coordinate
marginals together with the concrete rational shift action.  It deliberately
does not claim equality of the full shifted and unshifted path measures; no
finite-dimensional joint stationarity premise is inserted. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_continuum_shift_coordinate_eq
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
    (r q : ℚ) :
    (L.continuumMeasure.map
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable).map
        (measurable_pi_apply q).aemeasurable =
      L.continuumMeasure.map (measurable_pi_apply q).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  have hcomp :
      (fun x : ℚ → ℝ => x q) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r =
        fun x : ℚ → ℝ => x (q + r) := by
    funext x
    rfl
  calc
    Measure.map (fun x : ℚ → ℝ => x q)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
          (L.continuumMeasure : Measure (ℚ → ℝ))) =
      Measure.map
        ((fun x : ℚ → ℝ => x q) ∘
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
        (L.continuumMeasure : Measure (ℚ → ℝ)) := by
      exact Measure.map_map
        (measurable_pi_apply q)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r)
    _ = Measure.map (fun x : ℚ → ℝ => x (q + r))
        (L.continuumMeasure : Measure (ℚ → ℝ)) := by
      rw [hcomp]
    _ = Measure.map (fun x : ℚ → ℝ => x q)
        (L.continuumMeasure : Measure (ℚ → ℝ)) := by
      have h :=
        congrArg ProbabilityMeasure.toMeasure
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_continuum_coordinate_eq
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop L (q + r) q)
      simpa only [ProbabilityMeasure.toMeasure_map] using h

end

end MathlibAnalytic
end MGAP4D