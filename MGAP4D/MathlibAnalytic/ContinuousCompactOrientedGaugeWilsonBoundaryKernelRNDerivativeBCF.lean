import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryKernelAbsoluteContinuityBCF
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Since the boundary-target-pair kernel retains its input boundary as the first
output coordinate, the Radon--Nikodym derivative of two boundary mixtures is
exactly the Radon--Nikodym derivative of the input boundary laws, pulled back by
`Prod.fst`. -/
theorem continuous_compact_oriented_boundaryTargetPairKernel_comp_rnDeriv
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (μ ν : Measure (C.OffTargetBoundary target))
    [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    (C.singleLinkBoundaryTargetPairKernel target ∘ₘ μ).rnDeriv
        (C.singleLinkBoundaryTargetPairKernel target ∘ₘ ν) =ᵐ[
          C.singleLinkBoundaryTargetPairKernel target ∘ₘ ν]
      fun z => μ.rnDeriv ν z.1 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoundaryTargetPairKernel
  rw [← Measure.compProd_eq_comp_prod,
    ← Measure.compProd_eq_comp_prod]
  exact ProbabilityTheory.rnDeriv_measure_compProd_left μ ν
    (C.singleLinkBoundaryConditionalPairKernel target)

/-- The Radon--Nikodym derivative of the hybrid boundary-driven joint law with
respect to the Gibbs-averaged native joint law is the boundary-law derivative,
pulled back along the retained boundary coordinate.  This theorem does not
assert that the hybrid boundary law is absolutely continuous with respect to the
Gibbs boundary law. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryDrivenTargetPairMeasure_rnDeriv_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridBoundaryDrivenTargetPairMeasure target |>.rnDeriv
        (C.singleLinkHeatBathBoundaryTargetPairMeasure target) =ᵐ[
          C.singleLinkHeatBathBoundaryTargetPairMeasure target]
      fun z =>
        (C.independentPairHybridOffTargetBoundaryMeasure target).rnDeriv
          (C.gibbsOffTargetBoundaryMeasure target) z.1 := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  letI : IsProbabilityMeasure
      (C.independentPairHybridPreEndpointMeasure target) := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMeasure
    exact Measure.isProbabilityMeasure_map
      (continuous_compact_oriented_independentPairHybridPreEndpointMap_measurable
        C target).aemeasurable
  letI : IsProbabilityMeasure
      (C.independentPairHybridOffTargetBoundaryMeasure target) := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridOffTargetBoundaryMeasure
    exact Measure.isProbabilityMeasure_map
      (continuous_compact_oriented_offTargetBoundaryMap_measurable
        C target).aemeasurable
  letI : IsProbabilityMeasure
      (C.gibbsOffTargetBoundaryMeasure target) := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.gibbsOffTargetBoundaryMeasure
    exact Measure.isProbabilityMeasure_map
      (continuous_compact_oriented_offTargetBoundaryMap_measurable
        C target).aemeasurable
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryDrivenTargetPairMeasure
  rw [continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairMeasure_eq_boundaryKernel_comp]
  exact continuous_compact_oriented_boundaryTargetPairKernel_comp_rnDeriv
    C target _ _

/-- The reverse Radon--Nikodym derivative is likewise the reverse boundary-law
derivative pulled back along the first coordinate. -/
theorem continuous_compact_oriented_native_rnDeriv_independentPairHybridBoundaryDrivenTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.singleLinkHeatBathBoundaryTargetPairMeasure target |>.rnDeriv
        (C.independentPairHybridBoundaryDrivenTargetPairMeasure target) =ᵐ[
          C.independentPairHybridBoundaryDrivenTargetPairMeasure target]
      fun z =>
        (C.gibbsOffTargetBoundaryMeasure target).rnDeriv
          (C.independentPairHybridOffTargetBoundaryMeasure target) z.1 := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  letI : IsProbabilityMeasure
      (C.independentPairHybridPreEndpointMeasure target) := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMeasure
    exact Measure.isProbabilityMeasure_map
      (continuous_compact_oriented_independentPairHybridPreEndpointMap_measurable
        C target).aemeasurable
  letI : IsProbabilityMeasure
      (C.independentPairHybridOffTargetBoundaryMeasure target) := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridOffTargetBoundaryMeasure
    exact Measure.isProbabilityMeasure_map
      (continuous_compact_oriented_offTargetBoundaryMap_measurable
        C target).aemeasurable
  letI : IsProbabilityMeasure
      (C.gibbsOffTargetBoundaryMeasure target) := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.gibbsOffTargetBoundaryMeasure
    exact Measure.isProbabilityMeasure_map
      (continuous_compact_oriented_offTargetBoundaryMap_measurable
        C target).aemeasurable
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryDrivenTargetPairMeasure
  rw [continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairMeasure_eq_boundaryKernel_comp]
  exact continuous_compact_oriented_boundaryTargetPairKernel_comp_rnDeriv
    C target _ _

end

end MathlibAnalytic
end MGAP4D
