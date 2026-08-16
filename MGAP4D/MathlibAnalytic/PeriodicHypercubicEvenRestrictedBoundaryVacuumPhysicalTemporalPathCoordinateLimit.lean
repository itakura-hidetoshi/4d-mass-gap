import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTemporalPathSymmetryLimit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalProbabilityLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumTemporalPathCoordinateNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumTemporalPathCoordinateTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumTemporalPathCoordinateCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumTemporalPathCoordinateSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumTemporalPathCoordinateMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumTemporalPathCoordinateBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Every coordinate of the stationary finite path probability law is exactly
the already constructed effective-boundary scalar probability law. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure_map_coordinate_eq_effectiveBoundaryVacuumProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) (t : ℤ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure
      H N hN beta hbeta).map
        (measurable_pi_apply t).aemeasurable =
      periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
        H N hN beta hbeta := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  rw [periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure_toMeasure]
  rw [periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure_toMeasure]
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathMeasure_coordinate_eq_map_effectiveMeasure
      H N hN beta hbeta t

/-- Along any path-valued Prokhorov subsequence, the same-root effective scalar
laws converge to every temporal coordinate marginal of the continuum path law.

This is the continuous-mapping theorem for coordinate evaluation combined with
the exact finite coordinate identity above. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPath_effectiveBoundaryVacuumProbabilityMeasure_tendsto_coordinate
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
    (t : ℤ) :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n)))
      atTop
      (nhds
        (L.continuumMeasure.map
          (measurable_pi_apply t).aemeasurable)) := by
  let E :=
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding
  have hMapped :
      Tendsto
        (fun n : ℕ =>
          (E.embeddedMeasure (L.subsequence n)).map
            (measurable_pi_apply t).aemeasurable)
        atTop
        (nhds
          (L.continuumMeasure.map
            (measurable_pi_apply t).aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n : ℕ => E.embeddedMeasure (L.subsequence n))
      L.continuumMeasure L.weakConvergence (continuous_apply t)
  have hSequence :
      (fun n : ℕ =>
        periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))) =
      (fun n : ℕ =>
        (E.embeddedMeasure (L.subsequence n)).map
          (measurable_pi_apply t).aemeasurable) := by
    funext n
    rw [periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathPhysicalEmbedding_embeddedMeasure_eq]
    exact
      (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathProbabilityMeasure_map_coordinate_eq_effectiveBoundaryVacuumProbabilityMeasure
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n)) t).symm
  rw [hSequence]
  exact hMapped

/-- Each temporal coordinate of a path-valued Prokhorov limit canonically
produces a scalar Prokhorov subsequence limit for the original boundary-vacuum
physical embedding, with exactly the same subsequence.

Thus the path-valued temporal theory reconnects directly to the already
constructed scalar state and OS Hilbert spine. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit
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
    (t : ℤ) :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding where
  continuumMeasure :=
    L.continuumMeasure.map (measurable_pi_apply t).aemeasurable
  subsequence := L.subsequence
  subsequence_strictMono := L.subsequence_strictMono
  weakConvergence := by
    have h :=
      periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPath_effectiveBoundaryVacuumProbabilityMeasure_tendsto_coordinate
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L t
    have hSequence :
        (fun n : ℕ =>
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure
              (L.subsequence n)) =
        (fun n : ℕ =>
          periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))) := by
      funext n
      exact
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding_embeddedMeasure_eq_effectiveBoundaryVacuumProbabilityMeasure
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop (L.subsequence n)
    rw [hSequence]
    exact h

@[simp]
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit_continuumMeasure
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
    (t : ℤ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumTemporalPathCoordinateScalarLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L t).continuumMeasure =
      L.continuumMeasure.map (measurable_pi_apply t).aemeasurable := by
  rfl

end

end MathlibAnalytic
end MGAP4D
