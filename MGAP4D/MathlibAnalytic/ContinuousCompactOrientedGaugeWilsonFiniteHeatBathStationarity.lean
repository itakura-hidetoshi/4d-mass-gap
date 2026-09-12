import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonGibbsCompatibility
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MeasureComp

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The actual one-link heat-bath kernel leaves the canonical finite-volume
Wilson Gibbs law invariant. -/
theorem continuous_compact_oriented_singleLinkHeatBathKernel_comp_gibbsMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.singleLinkHeatBathKernel target ∘ₘ C.gibbsMeasure = C.gibbsMeasure := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  let f : C.base.Configuration → ℝ≥0∞ :=
    s.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hInv :=
    continuous_compact_oriented_gibbs_lintegral_singleLinkConditionalMeasure
      C target f hf
  calc
    (∫⁻ A : C.base.Configuration,
      C.singleLinkHeatBathKernel target A s ∂C.gibbsMeasure) =
        ∫⁻ A : C.base.Configuration,
          (∫⁻ g : C.base.Gauge,
            f (C.base.replaceLink A target g)
            ∂C.singleLinkConditionalMeasure A target)
          ∂C.gibbsMeasure := by
      apply lintegral_congr
      intro A
      calc
        C.singleLinkHeatBathKernel target A s =
            ∫⁻ B : C.base.Configuration, f B
              ∂C.singleLinkHeatBathKernel target A := by
          simp [f, hs]
        _ = ∫⁻ g : C.base.Gauge,
            f (C.base.replaceLink A target g)
            ∂C.singleLinkConditionalMeasure A target :=
          continuous_compact_oriented_lintegral_singleLinkHeatBathKernel
            C target A f hf
    _ = ∫⁻ A : C.base.Configuration, f A ∂C.gibbsMeasure := hInv
    _ = C.gibbsMeasure s := by
      simp [f, hs]

/-- Compose a finite ordered list of actual one-link heat-bath updates.  The
head of the list acts first. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.finiteSingleLinkHeatBathKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    List C.base.geometry.Edge → Kernel C.base.Configuration C.base.Configuration
  | [] => Kernel.id
  | target :: targets =>
      C.finiteSingleLinkHeatBathKernel targets ∘ₖ
        C.singleLinkHeatBathKernel target

@[simp] theorem continuous_compact_oriented_finiteSingleLinkHeatBathKernel_nil
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.finiteSingleLinkHeatBathKernel [] = Kernel.id := by
  rfl

@[simp] theorem continuous_compact_oriented_finiteSingleLinkHeatBathKernel_cons
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge) :
    C.finiteSingleLinkHeatBathKernel (target :: targets) =
      C.finiteSingleLinkHeatBathKernel targets ∘ₖ
        C.singleLinkHeatBathKernel target := by
  rfl

/-- Every finite ordered composition of the actual one-link heat-bath kernels
is again a Markov kernel. -/
noncomputable instance continuousCompactOriented_finiteSingleLinkHeatBathKernel_isMarkovKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge) :
    IsMarkovKernel (C.finiteSingleLinkHeatBathKernel targets) := by
  induction targets with
  | nil =>
      simp only [continuous_compact_oriented_finiteSingleLinkHeatBathKernel_nil]
      infer_instance
  | cons target targets ih =>
      simp only [continuous_compact_oriented_finiteSingleLinkHeatBathKernel_cons]
      letI : IsMarkovKernel (C.finiteSingleLinkHeatBathKernel targets) := ih
      infer_instance

/-- Any finite ordered sequence of actual one-link heat-bath updates preserves
the canonical finite-volume Wilson Gibbs law exactly. -/
theorem continuous_compact_oriented_finiteSingleLinkHeatBathKernel_comp_gibbsMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge) :
    C.finiteSingleLinkHeatBathKernel targets ∘ₘ C.gibbsMeasure =
      C.gibbsMeasure := by
  induction targets with
  | nil =>
      simp
  | cons target targets ih =>
      rw [continuous_compact_oriented_finiteSingleLinkHeatBathKernel_cons]
      rw [← Measure.comp_assoc]
      rw [continuous_compact_oriented_singleLinkHeatBathKernel_comp_gibbsMeasure]
      exact ih

end

end MathlibAnalytic
end MGAP4D
