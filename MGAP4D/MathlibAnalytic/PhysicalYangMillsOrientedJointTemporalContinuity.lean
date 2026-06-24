import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedDenseTemporalApproximation
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

variable {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}

/-- The time-configuration evaluation map associated with a physical temporal
action. -/
def jointTranslate
    (A : E.PhysicalDiscreteTemporalAction) :
    ℝ × E.PhysicalConfiguration → E.PhysicalConfiguration :=
  fun p => A.physicalTranslate p.1 p.2

/-- Joint continuity in physical time and physical configuration.

This is stronger than continuity of each individual homeomorphism, and is the
analytic input needed to pass scale-dependent times through weak convergence. -/
structure JointContinuity (A : E.PhysicalDiscreteTemporalAction) : Prop where
  jointTranslate_continuous : Continuous A.jointTranslate

namespace JointContinuity

variable {A : E.PhysicalDiscreteTemporalAction}

/-- Mapping the product of a Dirac time law and a configuration law by the joint
action is the same as translating the configuration law at that fixed time. -/
@[simp]
theorem diracProba_prod_map_jointTranslate
    (J : A.JointContinuity) (s : ℝ)
    (μ : ProbabilityMeasure E.PhysicalConfiguration) :
    ((diracProba s).prod μ).map
        J.jointTranslate_continuous.measurable.aemeasurable =
      μ.map
        (A.physicalTranslate s).continuous.measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_prod]
  change
    Measure.map A.jointTranslate
        ((Measure.dirac s).prod (μ : Measure E.PhysicalConfiguration)) =
      Measure.map (A.physicalTranslate s)
        (μ : Measure E.PhysicalConfiguration)
  calc
    Measure.map A.jointTranslate
        ((Measure.dirac s).prod (μ : Measure E.PhysicalConfiguration)) =
      Measure.map A.jointTranslate
        (Measure.map (Prod.mk s) (μ : Measure E.PhysicalConfiguration)) := by
      rw [Measure.dirac_prod]
    _ = Measure.map (A.jointTranslate ∘ Prod.mk s)
        (μ : Measure E.PhysicalConfiguration) :=
      Measure.map_map J.jointTranslate_continuous.measurable
        measurable_prodMk_left
    _ = Measure.map (A.physicalTranslate s)
        (μ : Measure E.PhysicalConfiguration) := rfl

/-- Joint continuity automatically supplies the varying-time weak-limit
continuity field.

The proof packages each time as a Dirac probability measure, uses continuity of
probability-measure products, and then applies the continuous mapping theorem to
the fixed joint action. -/
noncomputable def toWeakLimitContinuity
    (J : A.JointContinuity)
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) :=
  ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction.DenseTemporalApproximation.WeakLimitContinuity.mk
    (E := E) (A := A) (D := D) (L := L) (fun t => by
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
      simpa only [τ, μs, J.diracProba_prod_map_jointTranslate] using hmap)

end JointContinuity

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

end

end MathlibAnalytic
end MGAP4D
