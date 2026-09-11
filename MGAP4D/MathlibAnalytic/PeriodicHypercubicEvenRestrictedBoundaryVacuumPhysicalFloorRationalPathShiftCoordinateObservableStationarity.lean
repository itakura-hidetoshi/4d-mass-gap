import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathShiftCoordinateStationarity

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalShiftCoordinateObservableNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalShiftCoordinateObservableTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalShiftCoordinateObservableCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalShiftCoordinateObservableSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalShiftCoordinateObservableMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalShiftCoordinateObservableBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Every measurable readout of one rational-time coordinate has the same law
before and after a rational path translation.

This is the functorial one-coordinate cylinder lift of rational shift
stationarity.  It uses only `Measure.map_map` and the already proved equality of
the shifted and unshifted coordinate marginals.  In particular it does not
promote one-coordinate stationarity to equality of the full path measures. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_continuum_shift_coordinate_observable_law_eq
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
    {Y : Type*} [MeasurableSpace Y]
    (O : ℝ → Y) (hO : Measurable O)
    (r q : ℚ) :
    Measure.map
        (fun x : ℚ → ℝ =>
          O ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r x) q))
        (ProbabilityMeasure.toMeasure L.continuumMeasure) =
      Measure.map
        (fun x : ℚ → ℝ => O (x q))
        (ProbabilityMeasure.toMeasure L.continuumMeasure) := by
  have hshiftCoordinate :
      Measure.map (fun x : ℚ → ℝ => x q)
          (Measure.map
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
            (ProbabilityMeasure.toMeasure L.continuumMeasure)) =
        Measure.map (fun x : ℚ → ℝ => x q)
          (ProbabilityMeasure.toMeasure L.continuumMeasure) := by
    have h :=
      congrArg ProbabilityMeasure.toMeasure
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_continuum_shift_coordinate_eq
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop L r q)
    simpa only [ProbabilityMeasure.toMeasure_map] using h
  calc
    Measure.map
        (fun x : ℚ → ℝ =>
          O ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r x) q))
        (ProbabilityMeasure.toMeasure L.continuumMeasure) =
      Measure.map (O ∘ fun x : ℚ → ℝ => x q)
        (Measure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
          (ProbabilityMeasure.toMeasure L.continuumMeasure)) := by
      simpa [Function.comp_def] using
        (Measure.map_map
          (hO.comp (measurable_pi_apply q))
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r)).symm
    _ = Measure.map O
        (Measure.map (fun x : ℚ → ℝ => x q)
          (Measure.map
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r)
            (ProbabilityMeasure.toMeasure L.continuumMeasure))) := by
      exact (Measure.map_map hO (measurable_pi_apply q)).symm
    _ = Measure.map O
        (Measure.map (fun x : ℚ → ℝ => x q)
          (ProbabilityMeasure.toMeasure L.continuumMeasure)) := by
      rw [hshiftCoordinate]
    _ = Measure.map (O ∘ fun x : ℚ → ℝ => x q)
        (ProbabilityMeasure.toMeasure L.continuumMeasure) := by
      exact Measure.map_map hO (measurable_pi_apply q)
    _ = Measure.map (fun x : ℚ → ℝ => O (x q))
        (ProbabilityMeasure.toMeasure L.continuumMeasure) := by
      rfl

end

end MathlibAnalytic
end MGAP4D
