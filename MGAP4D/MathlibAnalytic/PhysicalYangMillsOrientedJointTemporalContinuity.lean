import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedDenseTemporalApproximation
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

variable {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}

/-- The time-configuration evaluation map associated with a physical temporal action. -/
def jointTranslate
    (A : E.PhysicalDiscreteTemporalAction) :
    ℝ × E.PhysicalConfiguration → E.PhysicalConfiguration :=
  fun p => A.physicalTranslate p.1 p.2

/-- Joint continuity in physical time and physical configuration. -/
structure JointContinuity (A : E.PhysicalDiscreteTemporalAction) : Prop where
  jointTranslate_continuous : Continuous A.jointTranslate

namespace JointContinuity

variable {A : E.PhysicalDiscreteTemporalAction}

/-- Mapping a fixed-time Dirac product by the joint action equals fixed-time translation. -/
theorem diracProba_prod_map_jointTranslate
    (J : A.JointContinuity) (s : ℝ)
    (μ : ProbabilityMeasure E.PhysicalConfiguration) :
    ((diracProba s).prod μ).map
        J.jointTranslate_continuous.measurable.aemeasurable =
      μ.map
        (A.physicalTranslate s).continuous.measurable.aemeasurable := by
  apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
  intro B hB
  change
    Measure.map A.jointTranslate
        ((Measure.dirac s).prod (μ : Measure E.PhysicalConfiguration)) B =
      Measure.map (A.physicalTranslate s)
        (μ : Measure E.PhysicalConfiguration) B
  rw [Measure.map_apply J.jointTranslate_continuous.measurable hB]
  rw [Measure.map_apply (A.physicalTranslate s).continuous.measurable hB]
  rw [Measure.dirac_prod]
  rw [Measure.map_apply measurable_prodMk_left
    (J.jointTranslate_continuous.measurable hB)]
  apply congrArg
    (fun U : Set E.PhysicalConfiguration =>
      (μ : Measure E.PhysicalConfiguration) U)
  ext X
  rfl

/-- Joint continuity supplies varying-time weak convergence at each target time. -/
theorem mappedApproximating_tendsto
    (J : A.JointContinuity)
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding)
    (t : ℝ) :
    Tendsto
      (fun n =>
        (E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)).map
          (A.physicalTranslate
            (A.latticeTime (L.subsequence n)
              (D.approximateStep t (L.subsequence n)))).continuous.measurable.aemeasurable)
      atTop
      (nhds
        (L.continuumMeasure.map
          (A.physicalTranslate t).continuous.measurable.aemeasurable)) := by
  let τ : ℕ → ℝ := fun n =>
    A.latticeTime (L.subsequence n)
      (D.approximateStep t (L.subsequence n))
  let μs : ℕ → ProbabilityMeasure E.PhysicalConfiguration := fun n =>
    E.toLatticeEmbedding.embeddedMeasure (L.subsequence n)
  have hτ : Tendsto τ atTop (nhds t) := by
    simpa only [τ] using D.approximateTime_tendsto_subsequence L t
  have hdirac :
      Tendsto (fun n => diracProba (τ n)) atTop
        (nhds (diracProba t)) :=
    continuous_diracProba.continuousAt.comp hτ
  have hpair :
      Tendsto (fun n => (diracProba (τ n), μs n)) atTop
        (nhds (diracProba t, L.continuumMeasure)) :=
    (Prod.tendsto_iff _ _).2 ⟨hdirac, L.weakConvergence⟩
  have hprod :
      Tendsto
        (fun n => (diracProba (τ n)).prod (μs n)) atTop
        (nhds ((diracProba t).prod L.continuumMeasure)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.comp hpair
  have hmap :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => (diracProba (τ n)).prod (μs n))
      ((diracProba t).prod L.continuumMeasure)
      hprod J.jointTranslate_continuous
  simpa only [τ, μs, J.diracProba_prod_map_jointTranslate] using hmap

end JointContinuity

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

end

end MathlibAnalytic
end MGAP4D
