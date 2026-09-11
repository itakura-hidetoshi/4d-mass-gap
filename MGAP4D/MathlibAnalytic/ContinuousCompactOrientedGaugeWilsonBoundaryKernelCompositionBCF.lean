import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryConditionalKernelBCF
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Deterministic Markov kernel that restricts a full configuration to its
actual off-target boundary. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryRestrictionKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel C.base.Configuration (C.OffTargetBoundary target) :=
  Kernel.deterministic (C.offTargetBoundaryMap target)
    (continuous_compact_oriented_offTargetBoundaryMap_measurable C target)

/-- The boundary-restriction kernel is Markov. -/
instance continuousCompactOriented_offTargetBoundaryRestrictionKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel (C.offTargetBoundaryRestrictionKernel target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryRestrictionKernel
  infer_instance

/-- Pointwise, boundary restriction is the corresponding Dirac law. -/
theorem continuous_compact_oriented_offTargetBoundaryRestrictionKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    C.offTargetBoundaryRestrictionKernel target A =
      Measure.dirac (C.offTargetBoundaryMap target A) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryRestrictionKernel
  rw [Kernel.deterministic_apply]

/-- The original configuration-indexed native joint kernel is exactly the
composition of deterministic boundary restriction with the measurable
boundary-indexed joint kernel. -/
theorem continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairKernel_eq_comp_boundaryKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.singleLinkHeatBathBoundaryTargetPairKernel target =
      C.singleLinkBoundaryTargetPairKernel target ∘ₖ
        C.offTargetBoundaryRestrictionKernel target := by
  ext A
  rw [Kernel.comp_apply,
    continuous_compact_oriented_offTargetBoundaryRestrictionKernel_apply,
    Measure.dirac_bind (Kernel.measurable _),
    continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairKernel_apply_eq_boundaryKernel]

/-- The Gibbs off-target boundary law is the composition of deterministic
boundary restriction with the Gibbs configuration measure. -/
theorem continuous_compact_oriented_gibbsOffTargetBoundaryMeasure_eq_kernel_comp
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.gibbsOffTargetBoundaryMeasure target =
      C.offTargetBoundaryRestrictionKernel target ∘ₘ C.gibbsMeasure := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsOffTargetBoundaryMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryRestrictionKernel
  symm
  exact Measure.deterministic_comp_eq_map
    (continuous_compact_oriented_offTargetBoundaryMap_measurable C target)

/-- The Gibbs-averaged native boundary-target-pair law is reconstructed exactly
by feeding the genuine Gibbs boundary marginal into the boundary kernel. -/
theorem continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairMeasure_eq_boundaryKernel_comp
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.singleLinkHeatBathBoundaryTargetPairMeasure target =
      C.singleLinkBoundaryTargetPairKernel target ∘ₘ
        C.gibbsOffTargetBoundaryMeasure target := by
  rw [continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairMeasure_eq_kernel_comp,
    continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairKernel_eq_comp_boundaryKernel,
    continuous_compact_oriented_gibbsOffTargetBoundaryMeasure_eq_kernel_comp,
    Measure.comp_assoc]

/-- Mapping every output of the boundary-target-pair kernel to its boundary
coordinate gives the identity kernel. -/
theorem continuous_compact_oriented_map_fst_singleLinkBoundaryTargetPairKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.singleLinkBoundaryTargetPairKernel target).map Prod.fst =
      Kernel.id := by
  ext boundary
  rw [Kernel.map_apply _ measurable_fst boundary,
    continuous_compact_oriented_singleLinkBoundaryTargetPairKernel_apply,
    continuous_compact_oriented_map_fst_singleLinkBoundaryTargetPairMeasure,
    Kernel.id_apply]

/-- Mapping every output of the boundary-target-pair kernel to its sampled pair
coordinate gives the conditional-pair kernel. -/
theorem continuous_compact_oriented_map_snd_singleLinkBoundaryTargetPairKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.singleLinkBoundaryTargetPairKernel target).map Prod.snd =
      C.singleLinkBoundaryConditionalPairKernel target := by
  ext boundary
  rw [Kernel.map_apply _ measurable_snd boundary,
    continuous_compact_oriented_singleLinkBoundaryTargetPairKernel_apply,
    continuous_compact_oriented_map_snd_singleLinkBoundaryTargetPairMeasure,
    continuous_compact_oriented_singleLinkBoundaryConditionalPairKernel_apply]

/-- Composing the boundary-target-pair kernel with any boundary measure preserves
that measure exactly as the output boundary marginal. -/
theorem continuous_compact_oriented_map_fst_boundaryTargetPairKernel_comp
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (μ : Measure (C.OffTargetBoundary target)) :
    Measure.map Prod.fst
        (C.singleLinkBoundaryTargetPairKernel target ∘ₘ μ) = μ := by
  change (C.singleLinkBoundaryTargetPairKernel target ∘ₘ μ).map Prod.fst = μ
  rw [Measure.map_comp μ
      (C.singleLinkBoundaryTargetPairKernel target) measurable_fst,
    continuous_compact_oriented_map_fst_singleLinkBoundaryTargetPairKernel,
    Measure.id_comp]

/-- The target-pair marginal after boundary mixing is obtained by mixing the
conditional-pair kernel against the same boundary law. -/
theorem continuous_compact_oriented_map_snd_boundaryTargetPairKernel_comp
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (μ : Measure (C.OffTargetBoundary target)) :
    Measure.map Prod.snd
        (C.singleLinkBoundaryTargetPairKernel target ∘ₘ μ) =
      C.singleLinkBoundaryConditionalPairKernel target ∘ₘ μ := by
  change (C.singleLinkBoundaryTargetPairKernel target ∘ₘ μ).map Prod.snd =
    C.singleLinkBoundaryConditionalPairKernel target ∘ₘ μ
  rw [Measure.map_comp μ
      (C.singleLinkBoundaryTargetPairKernel target) measurable_snd,
    continuous_compact_oriented_map_snd_singleLinkBoundaryTargetPairKernel]

/-- Boundary mixing through the boundary-target-pair kernel is injective because
the original boundary measure is recovered by the first marginal. -/
theorem continuous_compact_oriented_boundaryTargetPairKernel_comp_injective
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Function.Injective
      (fun μ : Measure (C.OffTargetBoundary target) =>
        C.singleLinkBoundaryTargetPairKernel target ∘ₘ μ) := by
  intro μ ν h
  have hmap := congrArg
    (fun ξ : Measure (C.OffTargetBoundaryTargetPair target) =>
      Measure.map Prod.fst ξ) h
  change Measure.map Prod.fst
      (C.singleLinkBoundaryTargetPairKernel target ∘ₘ μ) =
    Measure.map Prod.fst
      (C.singleLinkBoundaryTargetPairKernel target ∘ₘ ν) at hmap
  rw [continuous_compact_oriented_map_fst_boundaryTargetPairKernel_comp C target μ,
    continuous_compact_oriented_map_fst_boundaryTargetPairKernel_comp C target ν] at hmap
  exact hmap

/-- Two boundary-mixed joint laws are equal exactly when their input boundary
measures are equal. -/
theorem continuous_compact_oriented_boundaryTargetPairKernel_comp_eq_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (μ ν : Measure (C.OffTargetBoundary target)) :
    C.singleLinkBoundaryTargetPairKernel target ∘ₘ μ =
        C.singleLinkBoundaryTargetPairKernel target ∘ₘ ν ↔
      μ = ν := by
  constructor
  · intro h
    exact
      (continuous_compact_oriented_boundaryTargetPairKernel_comp_injective
        C target) h
  · intro h
    rw [h]

/-- Comparison law obtained by feeding the canonical hybrid pre-endpoint
boundary distribution into the exact native boundary conditional kernel. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryDrivenTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure (C.OffTargetBoundaryTargetPair target) :=
  C.singleLinkBoundaryTargetPairKernel target ∘ₘ
    C.independentPairHybridOffTargetBoundaryMeasure target

/-- The boundary marginal of the hybrid boundary-driven comparison law is the
canonical hybrid pre-endpoint boundary distribution. -/
theorem continuous_compact_oriented_map_fst_independentPairHybridBoundaryDrivenTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.fst
        (C.independentPairHybridBoundaryDrivenTargetPairMeasure target) =
      C.independentPairHybridOffTargetBoundaryMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryDrivenTargetPairMeasure
  exact continuous_compact_oriented_map_fst_boundaryTargetPairKernel_comp
    C target _

/-- The target-pair marginal of the hybrid boundary-driven comparison law is the
exact conditional-pair kernel mixed against the hybrid boundary law. -/
theorem continuous_compact_oriented_map_snd_independentPairHybridBoundaryDrivenTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.snd
        (C.independentPairHybridBoundaryDrivenTargetPairMeasure target) =
      C.singleLinkBoundaryConditionalPairKernel target ∘ₘ
        C.independentPairHybridOffTargetBoundaryMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryDrivenTargetPairMeasure
  exact continuous_compact_oriented_map_snd_boundaryTargetPairKernel_comp
    C target _

/-- The hybrid boundary-driven law equals the Gibbs-averaged native law if and
only if the hybrid and Gibbs off-target boundary distributions themselves are
equal.  No such equality is asserted here. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryDrivenTargetPairMeasure_eq_native_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridBoundaryDrivenTargetPairMeasure target =
        C.singleLinkHeatBathBoundaryTargetPairMeasure target ↔
      C.independentPairHybridOffTargetBoundaryMeasure target =
        C.gibbsOffTargetBoundaryMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryDrivenTargetPairMeasure
  rw [continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairMeasure_eq_boundaryKernel_comp]
  exact continuous_compact_oriented_boundaryTargetPairKernel_comp_eq_iff
    C target _ _

/-- The target-pair marginal of the Gibbs-averaged native law is the exact
conditional-pair kernel mixed against the genuine Gibbs boundary law. -/
theorem continuous_compact_oriented_map_snd_singleLinkHeatBathBoundaryTargetPairMeasure_eq_boundaryKernel_comp
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.snd
        (C.singleLinkHeatBathBoundaryTargetPairMeasure target) =
      C.singleLinkBoundaryConditionalPairKernel target ∘ₘ
        C.gibbsOffTargetBoundaryMeasure target := by
  rw [continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairMeasure_eq_boundaryKernel_comp]
  exact continuous_compact_oriented_map_snd_boundaryTargetPairKernel_comp
    C target _

end

end MathlibAnalytic
end MGAP4D
