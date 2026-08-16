import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumMeasurePushforward
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalGaugeAction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsProkhorovLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance restrictedBoundaryVacuumPhysicalMeasureLimitNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumPhysicalMeasureLimitTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumPhysicalMeasureLimitCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumPhysicalMeasureLimitSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumPhysicalMeasureLimitMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumPhysicalMeasureLimitBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- At every scale, the embedded physical scalar law of the concrete
boundary-vacuum readout is exactly the pushforward of the effective shared-
boundary measure by the finite OS vacuum moment.

This is the measure-level same-root identity

`Wilson Gibbs -> boundary effective law -> scalar physical readout`.

No additional weak-limit, interpolation, or gauge-invariance premise is used. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding_embeddedMeasure_toMeasure_eq_map_effectiveMeasure
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
    let E := periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop
    ProbabilityMeasure.toMeasure (E.toLatticeEmbedding.embeddedMeasure n) =
      Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment
          (H n) N hN (beta n) (hbeta n))
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          (H n) N hN (beta n) (hbeta n)) := by
  dsimp only
  let E := periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
    H N hN beta hbeta
    latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
    physicalVolume physicalVolume_tendsto_atTop
  have hEmbedded :
      ProbabilityMeasure.toMeasure (E.toLatticeEmbedding.embeddedMeasure n) =
        Measure.map (E.interpolate n) (E.system n).gibbsMeasure := by
    exact
      ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalGaugeAction.embeddedMeasure_toMeasure_eq
        n
  rw [hEmbedded]
  change
    Measure.map
        (periodicHypercubicEvenRestrictedBoundaryVacuumMoment
          (H n) N hN (beta n) (hbeta n))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (H n)) N hN
          (beta n) (hbeta n)).gibbsMeasure =
      Measure.map
        (periodicHypercubicEvenBoundaryVacuumMoment
          (H n) N hN (beta n) (hbeta n))
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          (H n) N hN (beta n) (hbeta n))
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumMoment_map_gibbsMeasure_eq_map_effectiveMeasure
      (H n) N hN (beta n) (hbeta n)

/-- Along any supplied Prokhorov subsequence limit of the concrete scalar
boundary-vacuum embedding, expectations computed directly on the finite
effective boundary laws converge to the continuum scalar expectation.

Thus the finite effective boundary expectation and the physical weak-limit
state are connected through the literal same Wilson Gibbs root, rather than an
independently postulated continuum readout. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuum_effectiveBoundary_expectation_converges
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
        (∫ x, O x ∂ProbabilityMeasure.toMeasure L.continuumMeasure)) := by
  have hWeak :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      L.weakConvergence) O
  have hSequence :
      (fun n : ℕ =>
        ∫ b,
          O (periodicHypercubicEvenBoundaryVacuumMoment
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n)) b)
          ∂(periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n)))) =
      fun n : ℕ =>
        ∫ x, O x
          ∂ProbabilityMeasure.toMeasure
            ((periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
              H N hN beta hbeta
              latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
              physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.embeddedMeasure
                (L.subsequence n)) := by
    funext n
    let k := L.subsequence n
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
              (H k) N hN (beta k) (hbeta k)) := by
      exact
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding_embeddedMeasure_toMeasure_eq_map_effectiveMeasure
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop k
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
  rw [hSequence]
  exact hWeak

end

end MathlibAnalytic
end MGAP4D
