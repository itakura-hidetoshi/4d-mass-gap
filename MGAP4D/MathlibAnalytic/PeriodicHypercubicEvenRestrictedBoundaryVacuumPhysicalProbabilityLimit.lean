import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalEffectiveProbabilityMeasure
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalMeasureLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumPhysicalProbabilityLimitNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumPhysicalProbabilityLimitTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumPhysicalProbabilityLimitCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumPhysicalProbabilityLimitSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumPhysicalProbabilityLimitMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumPhysicalProbabilityLimitBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The finite embedded physical probability law of the concrete boundary-
vacuum interpolation is exactly the probability pushforward of the effective
shared-boundary law by the finite OS vacuum moment.

This is the probability-measure form of the already proved same-root measure
identity; no normalization or interpolation premise is added. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding_embeddedMeasure_eq_effectiveBoundaryVacuumProbabilityMeasure
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (n : ℕ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure n =
      periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
        (H n) N hN (beta n) (hbeta n) := by
  apply ProbabilityMeasure.toMeasure_injective
  calc
    ProbabilityMeasure.toMeasure
        ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure n) =
      Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment
          (H n) N hN (beta n) (hbeta n))
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          (H n) N hN (beta n) (hbeta n)) :=
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding_embeddedMeasure_toMeasure_eq_map_effectiveMeasure
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop n
    _ = ProbabilityMeasure.toMeasure
        (periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
          (H n) N hN (beta n) (hbeta n)) := by
      rw [periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure_toMeasure]

/-- Along every supplied Prokhorov subsequence limit of the concrete
boundary-vacuum physical embedding, the scalar laws generated directly from the
effective finite boundary probabilities converge weakly to the continuum
probability law.

Equivalently,

`(boundaryVacuumMoment_n)_* μ_boundary,eff,n  ==>  μ_continuum`

in Mathlib's topology of convergence in distribution on probability measures. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuum_effectiveBoundaryVacuumProbabilityMeasure_tendsto
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding) :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n)))
      atTop
      (nhds L.continuumMeasure) := by
  have hSequence :
      (fun n : ℕ =>
        periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))) =
      (fun n : ℕ =>
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure
            (L.subsequence n)) := by
    funext n
    symm
    exact
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding_embeddedMeasure_eq_effectiveBoundaryVacuumProbabilityMeasure
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop (L.subsequence n)
  rw [hSequence]
  exact L.weakConvergence

end

end MathlibAnalytic
end MGAP4D
