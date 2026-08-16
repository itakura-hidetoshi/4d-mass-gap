import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalMeasureLimit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalProbabilityLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantContinuousState

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumPhysicalContinuousStateNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumPhysicalContinuousStateTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumPhysicalContinuousStateCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumPhysicalContinuousStateSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumPhysicalContinuousStateMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumPhysicalContinuousStateBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- On the scalar continuum carrier of the actual restricted boundary-vacuum
readout, every bounded continuous real observable is canonically gauge
invariant.

The membership proof is theorem-generated from the already constructed
identity physical gauge action; no observable-level gauge-invariance premise is
added. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumGaugeInvariantObservable
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
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (O : BoundedContinuousFunction ℝ ℝ) :
    physicalYangMillsGaugeInvariantObservableSubalgebra
      (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L) := by
  refine ⟨O, ?_⟩
  intro gamma x
  rw [periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit_action_eq
    H N hN beta hbeta
    latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
    physicalVolume physicalVolume_tendsto_atTop L gamma x]

/-- The finite effective shared-boundary expectation is literally the value of
the generic physical gauge-invariant continuous state on the canonical scalar
observable.

This is the state-level same-root identity

`Wilson Gibbs -> effective boundary law -> scalar physical law -> physical state`.

No new normalization, tightness, convergence, or gauge-invariance hypothesis is
introduced. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuum_effectiveBoundary_expectation_eq_approximatingGaugeInvariantContinuousState
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
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (n : ℕ)
    (O : BoundedContinuousFunction ℝ ℝ) :
    let S := periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
    let Oinv :=
      periodicHypercubicEvenRestrictedBoundaryVacuumGaugeInvariantObservable
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L O
    (∫ b,
      O (periodicHypercubicEvenBoundaryVacuumMoment
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n)) b)
      ∂(periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n)))) =
      (physicalYangMillsApproximatingGaugeInvariantContinuousState S n).
        toContinuousLinearMap Oinv := by
  dsimp only
  rw [physicalYangMillsApproximatingGaugeInvariantContinuousState_apply]
  rw [physicalYangMillsApproximatingGaugeInvariantExpectation_apply]
  change
    (∫ b,
      O (periodicHypercubicEvenBoundaryVacuumMoment
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n)) b)
      ∂(periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n)))) =
      ∫ x, O x
        ∂ProbabilityMeasure.toMeasure
          ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure
              (L.subsequence n))
  let k := L.subsequence n
  have hVacuum :
      Measurable
        (periodicHypercubicEvenBoundaryVacuumMoment
          (H k) N hN (beta k) (hbeta k)) :=
    periodicHypercubicEvenBoundaryVacuumMoment_measurable
      (H k) N hN (beta k) (hbeta k)
  have hLaw :
      ProbabilityMeasure.toMeasure
          ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure k) =
        Measure.map
          (periodicHypercubicEvenBoundaryVacuumMoment
            (H k) N hN (beta k) (hbeta k))
          (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
            (H k) N hN (beta k) (hbeta k)) :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding_embeddedMeasure_toMeasure_eq_map_effectiveMeasure
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop k
  change
    (∫ b,
      O (periodicHypercubicEvenBoundaryVacuumMoment
        (H k) N hN (beta k) (hbeta k) b)
      ∂(periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
        (H k) N hN (beta k) (hbeta k))) =
      ∫ x, O x
        ∂ProbabilityMeasure.toMeasure
          ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure k)
  calc
    (∫ b,
      O (periodicHypercubicEvenBoundaryVacuumMoment
        (H k) N hN (beta k) (hbeta k) b)
      ∂(periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
        (H k) N hN (beta k) (hbeta k))) =
        ∫ x, O x
          ∂Measure.map
            (periodicHypercubicEvenBoundaryVacuumMoment
              (H k) N hN (beta k) (hbeta k))
            (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
              (H k) N hN (beta k) (hbeta k)) := by
      symm
      exact MeasureTheory.integral_map
        hVacuum.aemeasurable O.continuous.aestronglyMeasurable
    _ = ∫ x, O x
        ∂ProbabilityMeasure.toMeasure
          ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure k) := by
      exact congrArg
        (fun μ : Measure ℝ => ∫ x, O x ∂μ)
        hLaw.symm

/-- The continuum physical gauge-invariant continuous state evaluates the
canonical scalar observable by integration against the same Prokhorov continuum
law. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuum_continuumGaugeInvariantContinuousState_apply
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
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (O : BoundedContinuousFunction ℝ ℝ) :
    let S := periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
    let Oinv :=
      periodicHypercubicEvenRestrictedBoundaryVacuumGaugeInvariantObservable
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L O
    (physicalYangMillsContinuumGaugeInvariantContinuousState S).
        toContinuousLinearMap Oinv =
      ∫ x, O x ∂ProbabilityMeasure.toMeasure L.continuumMeasure := by
  rfl

/-- For every bounded continuous scalar observable, the finite effective
boundary expectations converge directly to the value of the existing physical
gauge-invariant continuum continuous state.

This is the canonical specialization of the generic normalized positive
contractive state convergence to the actual Wilson boundary-vacuum root. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuum_effectiveBoundary_expectation_tendsto_continuumGaugeInvariantContinuousState
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
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (O : BoundedContinuousFunction ℝ ℝ) :
    let S := periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
    let Oinv :=
      periodicHypercubicEvenRestrictedBoundaryVacuumGaugeInvariantObservable
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L O
    Tendsto
      (fun n : ℕ =>
        ∫ b,
          O (periodicHypercubicEvenBoundaryVacuumMoment
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n)) b)
          ∂(periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))))
      atTop
      (nhds
        ((physicalYangMillsContinuumGaugeInvariantContinuousState S).
          toContinuousLinearMap Oinv)) := by
  dsimp only
  have hSequence :
      (fun n : ℕ =>
        ∫ b,
          O (periodicHypercubicEvenBoundaryVacuumMoment
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n)) b)
          ∂(periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n)))) =
      (fun n : ℕ =>
        (physicalYangMillsApproximatingGaugeInvariantContinuousState
          (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
            H N hN beta hbeta
            latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop L) n).
          toContinuousLinearMap
            (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeInvariantObservable
              H N hN beta hbeta
              latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
              physicalVolume physicalVolume_tendsto_atTop L O)) := by
    funext n
    exact
      periodicHypercubicEvenRestrictedBoundaryVacuum_effectiveBoundary_expectation_eq_approximatingGaugeInvariantContinuousState
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L n O
  rw [hSequence]
  exact
    physical_yang_mills_gaugeInvariantContinuousState_pointwise_converges
      (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L)
      (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeInvariantObservable
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L O)

end

end MathlibAnalytic
end MGAP4D
