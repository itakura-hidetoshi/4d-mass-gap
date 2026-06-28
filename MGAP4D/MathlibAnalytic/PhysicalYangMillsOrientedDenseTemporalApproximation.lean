import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedDiscreteTemporalAction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsProkhorovLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- A choice of integer lattice steps whose realized physical times converge to
every prescribed real time.

No additivity is required of `approximateStep`.  Additivity belongs to the exact
integer action at each finite scale, whereas this choice only supplies convergent
approximating times. -/
structure ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction.DenseTemporalApproximation
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (A : E.PhysicalDiscreteTemporalAction) where
  approximateStep : ℝ → ℕ → ℤ
  approximateTime_tendsto : ∀ t,
    Tendsto (fun n => A.latticeTime n (approximateStep t n)) atTop (nhds t)

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction.DenseTemporalApproximation

variable {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
variable {A : E.PhysicalDiscreteTemporalAction}

/-- Exact interpolation covariance at the selected approximating lattice step. -/
theorem interpolate_approximateStep_equivariant
    (D : A.DenseTemporalApproximation) (t : ℝ) (n : ℕ)
    (U : (E.system n).base.Configuration) :
    E.interpolate n (A.latticeTranslate n (D.approximateStep t n) U) =
      A.physicalTranslate
        (A.latticeTime n (D.approximateStep t n)) (E.interpolate n U) :=
  A.interpolate_equivariant n (D.approximateStep t n) U

/-- The embedded law is exactly invariant at every selected approximating time. -/
theorem embeddedMeasure_map_approximateTime_eq_self
    (D : A.DenseTemporalApproximation) (t : ℝ) (n : ℕ) :
    (E.toLatticeEmbedding.embeddedMeasure n).map
        (A.physicalTranslate
          (A.latticeTime n (D.approximateStep t n))).continuous.measurable.aemeasurable =
      E.toLatticeEmbedding.embeddedMeasure n :=
  A.embeddedMeasure_map_latticeTime_eq_self n (D.approximateStep t n)

/-- Realized physical times still converge after passage to any strictly
increasing Prokhorov subsequence. -/
theorem approximateTime_tendsto_subsequence
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (t : ℝ) :
    Tendsto
      (fun n => A.latticeTime (L.subsequence n)
        (D.approximateStep t (L.subsequence n)))
      atTop (nhds t) :=
  (D.approximateTime_tendsto t).comp
    L.subsequence_strictMono.tendsto_atTop

/-- The remaining analytic input for passing varying lattice times through a
weak limit. -/
def WeakLimitContinuity
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) : Prop :=
  ∀ t,
    Tendsto
      (fun n =>
        (E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)).map
          (A.physicalTranslate
            (A.latticeTime (L.subsequence n)
              (D.approximateStep t (L.subsequence n)))).continuous.measurable.aemeasurable)
      atTop
      (nhds
        (L.continuumMeasure.map
          (A.physicalTranslate t).continuous.measurable.aemeasurable))

namespace WeakLimitContinuity

/-- A direct varying-time convergence proof yields invariance of the continuum
probability law. -/
theorem continuumProbabilityMeasure_map_eq_self_of_tendsto
    {D : A.DenseTemporalApproximation}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (hMapped : ∀ s : ℝ,
      Tendsto
        (fun n =>
          (E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)).map
            (A.physicalTranslate
              (A.latticeTime (L.subsequence n)
                (D.approximateStep s (L.subsequence n)))).continuous.measurable.aemeasurable)
        atTop
        (nhds
          (L.continuumMeasure.map
            (A.physicalTranslate s).continuous.measurable.aemeasurable)))
    (t : ℝ) :
    L.continuumMeasure.map
        (A.physicalTranslate t).continuous.measurable.aemeasurable =
      L.continuumMeasure := by
  have hOriginal :
      Tendsto
        (fun n =>
          (E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)).map
            (A.physicalTranslate
              (A.latticeTime (L.subsequence n)
                (D.approximateStep t (L.subsequence n)))).continuous.measurable.aemeasurable)
        atTop (nhds L.continuumMeasure) := by
    simpa only [D.embeddedMeasure_map_approximateTime_eq_self] using
      L.weakConvergence
  exact tendsto_nhds_unique (hMapped t) hOriginal

/-- Exact finite-scale invariance plus continuity of the varying translated laws
forces real-time invariance of the Prokhorov continuum measure. -/
theorem continuumProbabilityMeasure_map_eq_self
    {D : A.DenseTemporalApproximation}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (C : D.WeakLimitContinuity L) (t : ℝ) :
    L.continuumMeasure.map
        (A.physicalTranslate t).continuous.measurable.aemeasurable =
      L.continuumMeasure :=
  continuumProbabilityMeasure_map_eq_self_of_tendsto C t

/-- Measure-valued form of continuum invariance obtained from the dense-time
approximation bridge. -/
theorem continuumMeasure_map_eq_self
    {D : A.DenseTemporalApproximation}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (C : D.WeakLimitContinuity L) (t : ℝ) :
    Measure.map (A.physicalTranslate t)
        (ProbabilityMeasure.toMeasure L.continuumMeasure) =
      ProbabilityMeasure.toMeasure L.continuumMeasure := by
  have h := congrArg ProbabilityMeasure.toMeasure
    (C.continuumProbabilityMeasure_map_eq_self t)
  simpa only [ProbabilityMeasure.toMeasure_map] using h

end WeakLimitContinuity

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction.DenseTemporalApproximation

end

end MathlibAnalytic
end MGAP4D
