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

private theorem jointTranslate_comp_prodMk
    (s : ℝ) :
    A.jointTranslate ∘ Prod.mk s = A.physicalTranslate s := by
  funext x
  rfl

private theorem map_jointTranslate_map_prodMk
    (J : A.JointContinuity) (s : ℝ)
    (μ : Measure E.PhysicalConfiguration) [SFinite μ] :
    Measure.map A.jointTranslate (Measure.map (Prod.mk s) μ) =
      Measure.map (A.physicalTranslate s) μ := by
  calc
    Measure.map A.jointTranslate (Measure.map (Prod.mk s) μ) =
      Measure.map (A.jointTranslate ∘ Prod.mk s) μ :=
        Measure.map_map J.jointTranslate_continuous.measurable
          measurable_prodMk_left
    _ = Measure.map (A.physicalTranslate s) μ :=
      congrArg
        (fun f : E.PhysicalConfiguration → E.PhysicalConfiguration =>
          Measure.map f μ)
        (jointTranslate_comp_prodMk (A := A) s)

private theorem map_jointTranslate_dirac_prod
    (J : A.JointContinuity) (s : ℝ)
    (μ : Measure E.PhysicalConfiguration) [SFinite μ] :
    Measure.map A.jointTranslate ((Measure.dirac s).prod μ) =
      Measure.map (A.physicalTranslate s) μ := by
  rw [Measure.dirac_prod]
  exact map_jointTranslate_map_prodMk J s μ

private theorem toMeasure_diracProba_prod_map_jointTranslate
    (J : A.JointContinuity) (s : ℝ)
    (μ : ProbabilityMeasure E.PhysicalConfiguration) :
    ((((diracProba s).prod μ).map
        J.jointTranslate_continuous.measurable.aemeasurable) :
      Measure E.PhysicalConfiguration) =
      ((μ.map
        (A.physicalTranslate s).continuous.measurable.aemeasurable) :
      Measure E.PhysicalConfiguration) := by
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_prod]
  change
    Measure.map A.jointTranslate
        ((Measure.dirac s).prod (μ : Measure E.PhysicalConfiguration)) =
      Measure.map (A.physicalTranslate s)
        (μ : Measure E.PhysicalConfiguration)
  exact map_jointTranslate_dirac_prod J s μ

/-- Mapping a fixed-time Dirac product by the joint action equals fixed-time translation. -/
set_option maxHeartbeats 400000 in
theorem diracProba_prod_map_jointTranslate
    (J : A.JointContinuity) (s : ℝ)
    (μ : ProbabilityMeasure E.PhysicalConfiguration) :
    ((diracProba s).prod μ).map
        J.jointTranslate_continuous.measurable.aemeasurable =
      μ.map
        (A.physicalTranslate s).continuous.measurable.aemeasurable :=
  ProbabilityMeasure.toMeasure_injective
    (toMeasure_diracProba_prod_map_jointTranslate J s μ)

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
