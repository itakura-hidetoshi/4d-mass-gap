import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateStationarity

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalShiftNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalShiftTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalShiftCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalShiftSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalShiftMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalShiftBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Translation of a rational-indexed scalar path. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift
    (r : ℚ) (x : ℚ → ℝ) : ℚ → ℝ :=
  fun q => x (q + r)

/-- Rational path translation is continuous in the countable product topology. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_continuous
    (r : ℚ) :
    Continuous
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r) := by
  refine continuous_pi ?_
  intro q
  exact continuous_apply (q + r)

/-- In particular every rational path translation is measurable. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable
    (r : ℚ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r) :=
  (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_continuous r).measurable

@[simp]
theorem periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_zero
    (x : ℚ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift 0 x = x := by
  funext q
  simp [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift]

/-- Rational path translations satisfy the additive action law. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_add
    (r s : ℚ) (x : ℚ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift (r + s) x =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift s x) := by
  funext q
  simp [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift,
    add_assoc]

/-- Continuous mapping of a rational-path Prokhorov limit by a fixed rational
translation.

This theorem only identifies the weak limit of the shifted finite laws with the
shifted continuum law.  It does not yet assert that the shifted and unshifted
continuum laws are equal. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_shiftedEmbeddedMeasure_tendsto
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
    (r : ℚ) :
    Tendsto
      (fun n : ℕ =>
        ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure
            (L.subsequence n)).map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable)
      atTop
      (nhds
        (L.continuumMeasure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable)) := by
  exact
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n : ℕ =>
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure
            (L.subsequence n))
      L.continuumMeasure L.weakConvergence
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_continuous r)

/-- Same continuous-mapping statement rewritten entirely in terms of the actual
finite same-Wilson-source rational floor path laws. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure_map_shift_tendsto
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
    (r : ℚ) :
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))
          latticeSpacing (L.subsequence n)).map
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable)
      atTop
      (nhds
        (L.continuumMeasure.map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable)) := by
  have h :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_shiftedEmbeddedMeasure_tendsto
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L r
  have hSequence :
      (fun n : ℕ =>
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))
          latticeSpacing (L.subsequence n)).map
            (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable) =
      (fun n : ℕ =>
        ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure
            (L.subsequence n)).map
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift_measurable r).aemeasurable) := by
    funext n
    rw [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding_embeddedMeasure_eq]
  rw [hSequence]
  exact h

end

end MathlibAnalytic
end MGAP4D
