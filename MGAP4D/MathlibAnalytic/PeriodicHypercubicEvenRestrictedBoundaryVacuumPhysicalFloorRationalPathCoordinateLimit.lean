import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalProbabilityLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumFloorRationalCoordinateNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumFloorRationalCoordinateTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumFloorRationalCoordinateCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumFloorRationalCoordinateSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumFloorRationalCoordinateMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumFloorRationalCoordinateBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Every rational coordinate of the finite floor-path probability law is
exactly the already constructed effective-boundary scalar probability law. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure_map_coordinate_eq_effectiveBoundaryVacuumProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ) (n : ℕ) (q : ℚ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure
      H N hN beta hbeta latticeSpacing n).map
        (measurable_pi_apply q).aemeasurable =
      periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
        H N hN beta hbeta := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  rw [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure_toMeasure]
  rw [periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure_toMeasure]
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathMeasure_coordinate_eq_map_effectiveMeasure
      H N hN beta hbeta latticeSpacing n q

/-- Along any Prokhorov subsequence limit on the rational-time Polish carrier,
the same-root effective scalar laws converge to every rational coordinate
marginal of the continuum path law.

Only the continuous-mapping theorem for coordinate evaluation and the exact
finite same-source identity are used. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_effectiveBoundaryVacuumProbabilityMeasure_tendsto_coordinate
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
    (q : ℚ) :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n)))
      atTop
      (nhds
        (L.continuumMeasure.map
          (measurable_pi_apply q).aemeasurable)) := by
  let E :=
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding
  have hMapped :
      Tendsto
        (fun n : ℕ =>
          (E.embeddedMeasure (L.subsequence n)).map
            (measurable_pi_apply q).aemeasurable)
        atTop
        (nhds
          (L.continuumMeasure.map
            (measurable_pi_apply q).aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n : ℕ => E.embeddedMeasure (L.subsequence n))
      L.continuumMeasure L.weakConvergence (continuous_apply q)
  have hSequence :
      (fun n : ℕ =>
        periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))) =
      (fun n : ℕ =>
        (E.embeddedMeasure (L.subsequence n)).map
          (measurable_pi_apply q).aemeasurable) := by
    funext n
    rw [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding_embeddedMeasure_eq]
    exact
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathProbabilityMeasure_map_coordinate_eq_effectiveBoundaryVacuumProbabilityMeasure
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n))
        latticeSpacing (L.subsequence n) q).symm
  rw [hSequence]
  exact hMapped

/-- Each rational-time coordinate of a rational-path Prokhorov limit canonically
produces a scalar Prokhorov subsequence limit for the original boundary-vacuum
physical embedding, with exactly the same subsequence.

Thus the rational physical-time skeleton reconnects directly to the existing
scalar state and OS Hilbert spine without a new continuum-time premise. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit
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
    (q : ℚ) :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding where
  continuumMeasure :=
    L.continuumMeasure.map (measurable_pi_apply q).aemeasurable
  subsequence := L.subsequence
  subsequence_strictMono := L.subsequence_strictMono
  weakConvergence := by
    have h :=
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPath_effectiveBoundaryVacuumProbabilityMeasure_tendsto_coordinate
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L q
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
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit_continuumMeasure
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
    (q : ℚ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathCoordinateScalarLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L q).continuumMeasure =
      L.continuumMeasure.map (measurable_pi_apply q).aemeasurable := by
  rfl

end

end MathlibAnalytic
end MGAP4D
