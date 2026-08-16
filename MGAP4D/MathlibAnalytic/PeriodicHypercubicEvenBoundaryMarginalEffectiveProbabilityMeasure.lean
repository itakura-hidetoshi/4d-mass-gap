import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalEffectiveMeasurePushforward

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance boundaryEffectiveProbabilityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryEffectiveProbabilityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryEffectiveProbabilityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryEffectiveProbabilitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryEffectiveProbabilityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryEffectiveProbabilityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The effective shared-boundary measure has total mass one because it is
literally the measurable boundary-restriction pushforward of the normalized
finite Wilson Gibbs law.

No independent normalization hypothesis or integral normalization calculation
is introduced here. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveMeasure_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
        H N hN beta hbeta) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  have hCoordinates :
      Measurable
        (P.boundaryFiberedCoordinates
          (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
    P.boundaryFiberedCoordinates_measurable
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  have hBoundary :
      Measurable
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          P.boundaryRestriction A) := by
    have h := measurable_fst.comp hCoordinates
    simpa [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedCoordinates] using h
  letI : IsProbabilityMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
    periodicHypercubicSpecialUnitaryWilsonSystem_gibbsMeasure_probability
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  have hMap :
      IsProbabilityMeasure
        (Measure.map P.boundaryRestriction
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) :=
    Measure.isProbabilityMeasure_map hBoundary.aemeasurable
  have hMarginal :
      Measure.map P.boundaryRestriction
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure =
        periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          H N hN beta hbeta := by
    simpa [P] using
      (periodicHypercubicEvenBoundaryRestriction_map_gibbsMeasure_eq_effectiveMeasure
        H N hN beta hbeta)
  rw [hMarginal] at hMap
  exact hMap

/-- The actual effective finite Wilson boundary law, now packaged as a genuine
Mathlib probability measure. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalEffectiveProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ProbabilityMeasure
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :=
  ⟨periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
      H N hN beta hbeta,
    periodicHypercubicEvenBoundaryMarginalEffectiveMeasure_isProbabilityMeasure
      H N hN beta hbeta⟩

@[simp]
theorem periodicHypercubicEvenBoundaryMarginalEffectiveProbabilityMeasure_toMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ProbabilityMeasure.toMeasure
        (periodicHypercubicEvenBoundaryMarginalEffectiveProbabilityMeasure
          H N hN beta hbeta) =
      periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
        H N hN beta hbeta :=
  rfl

/-- Push the genuine effective boundary probability law through the finite OS
boundary vacuum moment.  This is the probability-law form of the scalar
physical readout used by the concrete interpolation. -/
noncomputable def periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) : ProbabilityMeasure ℝ :=
  (periodicHypercubicEvenBoundaryMarginalEffectiveProbabilityMeasure
    H N hN beta hbeta).map
      (periodicHypercubicEvenBoundaryVacuumMoment_measurable
        H N hN beta hbeta).aemeasurable

@[simp]
theorem periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure_toMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ProbabilityMeasure.toMeasure
        (periodicHypercubicEvenBoundaryVacuumEffectiveProbabilityMeasure
          H N hN beta hbeta) =
      Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment
          H N hN beta hbeta)
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          H N hN beta hbeta) :=
  rfl

end

end MathlibAnalytic
end MGAP4D
