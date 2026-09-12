import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHeatBathVacuumL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionIdempotent
import Mathlib.Probability.Kernel.MeasurableIntegral

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

/-- For a strongly measurable observable, exact compact one-link Haar
conditional expectation is strongly measurable in the ambient configuration
space. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f) :
    StronglyMeasurable (C.singleLinkHeatBathProjection target f) := by
  have hJoint : StronglyMeasurable
      (fun z : C.base.Configuration × C.base.Gauge =>
        f (C.base.replaceLink z.1 target z.2)) :=
    hf.comp_measurable
      (continuous_compact_oriented_replaceLink_uncurry C target).measurable
  have hKernel : StronglyMeasurable
      (fun A : C.base.Configuration =>
        ∫ g, f (C.base.replaceLink A target g)
          ∂C.singleLinkConditionalKernel target A) :=
    hJoint.integral_kernel_prod_right'
  have hEq :
      (fun A : C.base.Configuration =>
        ∫ g, f (C.base.replaceLink A target g)
          ∂C.singleLinkConditionalKernel target A) =
        C.singleLinkHeatBathProjection target f := by
    funext A
    rw [continuous_compact_oriented_singleLinkConditionalKernel_apply]
    rfl
  rw [← hEq]
  exact hKernel

/-- Canonical off-link representative of one-link Haar conditional
expectation, obtained by inserting the identity at the selected link. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionRepresentative
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ) :
    C.base.OffLinkConfiguration target → ℝ :=
  fun Aoff =>
    C.singleLinkHeatBathProjection target f
      (C.base.singleLinkAssemble target 1 Aoff)

/-- The off-link representative is strongly measurable whenever the original
observable is strongly measurable. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionRepresentative_stronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f) :
    StronglyMeasurable
      (C.singleLinkHeatBathProjectionRepresentative target f) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionRepresentative
  exact
    (continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C target f hf).comp_measurable
      ((measurable_compact_oriented_singleLinkAssemble_uncurry C target).comp
        (measurable_const.prodMk measurable_id))

/-- Pointwise exact Haar conditional expectation factors through restriction
to all off-link coordinates. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_eq_representative_comp_restriction
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ) :
    C.singleLinkHeatBathProjection target f =
      C.singleLinkHeatBathProjectionRepresentative target f ∘
        C.base.offLinkRestriction target := by
  funext A
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionRepresentative
    CompactOrientedGaugeWilsonSystem.offLinkRestriction
  apply
    continuous_compact_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
  intro e he
  symm
  exact compact_oriented_singleLinkAssemble_offLink
    C.base target 1
    (fun eoff : C.base.OffLinkEdge target => A eoff.1)
    ⟨e, he⟩

/-- Exact compact one-link Haar conditional expectation is strongly measurable
with respect to the off-link sigma-algebra. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_offLinkStronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f) :
    StronglyMeasurable[C.base.offLinkMeasurableSpace target]
      (C.singleLinkHeatBathProjection target f) := by
  rw [continuous_compact_oriented_singleLinkHeatBathProjection_eq_representative_comp_restriction]
  exact
    (continuous_compact_oriented_singleLinkHeatBathProjectionRepresentative_stronglyMeasurable
      C target f hf).comp_measurable
      (comap_measurable (C.base.offLinkRestriction target))

end

end MathlibAnalytic
end MGAP4D
