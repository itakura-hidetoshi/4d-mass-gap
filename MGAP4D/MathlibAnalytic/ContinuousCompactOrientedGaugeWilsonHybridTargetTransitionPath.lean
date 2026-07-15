import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalOverlapAnchoredCouplingReconstruction
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridBoundaryResidualSourcePathBCF
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- The explicit anchored target-value transition attached to one consecutive
step of the canonical finite hybrid path from `A` to `B`. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTransitionKernelAtStep
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (k : ℕ) : Kernel C.base.Gauge C.base.Gauge :=
  C.configurationPairConditionalAnchoredOverlapTransitionKernelAt target
    (C.independentPairHybridConfiguration A B k,
      C.independentPairHybridConfiguration A B (k + 1))

/-- Every consecutive hybrid target-value transition is Markov. -/
instance continuousCompactOriented_independentPairHybridTargetTransitionKernelAtStep_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (k : ℕ) :
    IsMarkovKernel
      (C.independentPairHybridTargetTransitionKernelAtStep A B target k) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTransitionKernelAtStep
  infer_instance

/-- One anchored hybrid-path transition sends the exact conditional law at rank
`k` to the exact conditional law at rank `k+1`. -/
theorem continuous_compact_oriented_independentPairHybridTargetTransitionKernelAtStep_comp_measure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (k : ℕ) :
    C.independentPairHybridTargetTransitionKernelAtStep A B target k ∘ₘ
        C.singleLinkConditionalMeasure
          (C.independentPairHybridConfiguration A B k) target =
      C.singleLinkConditionalMeasure
        (C.independentPairHybridConfiguration A B (k + 1)) target := by
  let left := C.independentPairHybridConfiguration A B k
  let right := C.independentPairHybridConfiguration A B (k + 1)
  let κ := C.independentPairHybridTargetTransitionKernelAtStep A B target k
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure left target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C left target
  have hsnd :=
    continuous_compact_oriented_map_snd_singleLinkConditionalAnchoredOverlapCouplingMeasure
      C left right target
  change κ ∘ₘ C.singleLinkConditionalMeasure left target =
    C.singleLinkConditionalMeasure right target
  rw [← Measure.snd_compProd]
  change Measure.map Prod.snd
      (C.singleLinkConditionalMeasure left target ⊗ₘ κ) =
    C.singleLinkConditionalMeasure right target
  simpa [κ, left, right,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTransitionKernelAtStep,
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalAnchoredOverlapCouplingMeasure]
    using hsnd

/-- Kernel obtained by composing the consecutive anchored target-value
transitions along the first `m` steps of the canonical hybrid path. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTransitionPathKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    ℕ → Kernel C.base.Gauge C.base.Gauge
  | 0 => Kernel.id
  | k + 1 =>
      C.independentPairHybridTargetTransitionKernelAtStep A B target k ∘ₖ
        C.independentPairHybridTargetTransitionPathKernel A B target k

/-- Every finite prefix of the composed hybrid target-value transition path is
Markov. -/
instance continuousCompactOriented_independentPairHybridTargetTransitionPathKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (m : ℕ) :
    IsMarkovKernel
      (C.independentPairHybridTargetTransitionPathKernel A B target m) := by
  induction m with
  | zero =>
      rw [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTransitionPathKernel]
      infer_instance
  | succ m ih =>
      letI : IsMarkovKernel
          (C.independentPairHybridTargetTransitionPathKernel A B target m) := ih
      rw [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTransitionPathKernel]
      infer_instance

/-- Starting from the exact target-link conditional law at the left endpoint,
the first `m` composed anchored transitions produce exactly the conditional law
at hybrid rank `m`. -/
theorem continuous_compact_oriented_independentPairHybridTargetTransitionPathKernel_comp_measure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (m : ℕ) :
    C.independentPairHybridTargetTransitionPathKernel A B target m ∘ₘ
        C.singleLinkConditionalMeasure A target =
      C.singleLinkConditionalMeasure
        (C.independentPairHybridConfiguration A B m) target := by
  induction m with
  | zero =>
      simp [
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTransitionPathKernel]
  | succ m ih =>
      rw [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTransitionPathKernel,
        ← Measure.comp_assoc, ih]
      simpa [Nat.succ_eq_add_one] using
        continuous_compact_oriented_independentPairHybridTargetTransitionKernelAtStep_comp_measure
          C A B target m

/-- Composing all canonical hybrid steps transports the exact target-link
conditional law at `A` to the exact target-link conditional law at `B`. -/
theorem continuous_compact_oriented_independentPairHybridTargetTransitionPathKernel_card_comp_measure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridTargetTransitionPathKernel A B target
        (Fintype.card C.base.geometry.Edge) ∘ₘ
      C.singleLinkConditionalMeasure A target =
        C.singleLinkConditionalMeasure B target := by
  rw [continuous_compact_oriented_independentPairHybridTargetTransitionPathKernel_comp_measure,
    continuous_compact_oriented_independentPairHybridConfiguration_card]

end

end MathlibAnalytic
end MGAP4D
