import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryKernelCompositionBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Because the measurable boundary-target-pair kernel retains the input
boundary as its first output coordinate, absolute continuity of two mixed joint
laws is equivalent to absolute continuity of their input boundary laws. -/
theorem continuous_compact_oriented_boundaryTargetPairKernel_comp_absolutelyContinuous_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (μ ν : Measure (C.OffTargetBoundary target)) :
    (C.singleLinkBoundaryTargetPairKernel target ∘ₘ μ) ≪
        (C.singleLinkBoundaryTargetPairKernel target ∘ₘ ν) ↔
      μ ≪ ν := by
  constructor
  · intro h
    have hmap := h.map measurable_fst
    rw [continuous_compact_oriented_map_fst_boundaryTargetPairKernel_comp
          C target μ,
        continuous_compact_oriented_map_fst_boundaryTargetPairKernel_comp
          C target ν] at hmap
    exact hmap
  · intro h
    exact h.comp_right (C.singleLinkBoundaryTargetPairKernel target)

/-- The hybrid boundary-driven joint law is absolutely continuous with respect
to the Gibbs-averaged native law exactly when the hybrid off-target boundary law
is absolutely continuous with respect to the genuine Gibbs boundary law. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryDrivenTargetPairMeasure_absolutelyContinuous_native_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridBoundaryDrivenTargetPairMeasure target ≪
        C.singleLinkHeatBathBoundaryTargetPairMeasure target ↔
      C.independentPairHybridOffTargetBoundaryMeasure target ≪
        C.gibbsOffTargetBoundaryMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryDrivenTargetPairMeasure
  rw [continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairMeasure_eq_boundaryKernel_comp]
  exact
    continuous_compact_oriented_boundaryTargetPairKernel_comp_absolutelyContinuous_iff
      C target _ _

/-- Conversely, the Gibbs-averaged native law is absolutely continuous with
respect to the hybrid boundary-driven law exactly when the genuine Gibbs
boundary law is absolutely continuous with respect to the hybrid boundary law. -/
theorem continuous_compact_oriented_native_absolutelyContinuous_independentPairHybridBoundaryDrivenTargetPairMeasure_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.singleLinkHeatBathBoundaryTargetPairMeasure target ≪
        C.independentPairHybridBoundaryDrivenTargetPairMeasure target ↔
      C.gibbsOffTargetBoundaryMeasure target ≪
        C.independentPairHybridOffTargetBoundaryMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryDrivenTargetPairMeasure
  rw [continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairMeasure_eq_boundaryKernel_comp]
  exact
    continuous_compact_oriented_boundaryTargetPairKernel_comp_absolutelyContinuous_iff
      C target _ _

/-- Mutual absolute continuity of the hybrid boundary-driven and native joint
laws is equivalent to mutual absolute continuity of the two input off-target
boundary laws. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryDrivenTargetPairMeasure_mutuallyAbsolutelyContinuous_native_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.independentPairHybridBoundaryDrivenTargetPairMeasure target ≪
        C.singleLinkHeatBathBoundaryTargetPairMeasure target ∧
      C.singleLinkHeatBathBoundaryTargetPairMeasure target ≪
        C.independentPairHybridBoundaryDrivenTargetPairMeasure target) ↔
      (C.independentPairHybridOffTargetBoundaryMeasure target ≪
          C.gibbsOffTargetBoundaryMeasure target ∧
        C.gibbsOffTargetBoundaryMeasure target ≪
          C.independentPairHybridOffTargetBoundaryMeasure target) := by
  constructor
  · rintro ⟨hHybridNative, hNativeHybrid⟩
    exact
      ⟨(continuous_compact_oriented_independentPairHybridBoundaryDrivenTargetPairMeasure_absolutelyContinuous_native_iff
          C target).1 hHybridNative,
        (continuous_compact_oriented_native_absolutelyContinuous_independentPairHybridBoundaryDrivenTargetPairMeasure_iff
          C target).1 hNativeHybrid⟩
  · rintro ⟨hHybridBoundary, hGibbsBoundary⟩
    exact
      ⟨(continuous_compact_oriented_independentPairHybridBoundaryDrivenTargetPairMeasure_absolutelyContinuous_native_iff
          C target).2 hHybridBoundary,
        (continuous_compact_oriented_native_absolutelyContinuous_independentPairHybridBoundaryDrivenTargetPairMeasure_iff
          C target).2 hGibbsBoundary⟩

/-- Boundary-law domination propagates to the target-pair marginals after the
common exact conditional-pair kernel is applied. -/
theorem continuous_compact_oriented_map_snd_independentPairHybridBoundaryDrivenTargetPairMeasure_absolutelyContinuous_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (hBoundary :
      C.independentPairHybridOffTargetBoundaryMeasure target ≪
        C.gibbsOffTargetBoundaryMeasure target) :
    Measure.map Prod.snd
        (C.independentPairHybridBoundaryDrivenTargetPairMeasure target) ≪
      Measure.map Prod.snd
        (C.singleLinkHeatBathBoundaryTargetPairMeasure target) := by
  have hJoint :
      C.independentPairHybridBoundaryDrivenTargetPairMeasure target ≪
        C.singleLinkHeatBathBoundaryTargetPairMeasure target :=
    (continuous_compact_oriented_independentPairHybridBoundaryDrivenTargetPairMeasure_absolutelyContinuous_native_iff
      C target).2 hBoundary
  exact hJoint.map measurable_snd

/-- Reverse boundary-law domination likewise propagates to the target-pair
marginals. -/
theorem continuous_compact_oriented_map_snd_native_absolutelyContinuous_independentPairHybridBoundaryDrivenTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (hBoundary :
      C.gibbsOffTargetBoundaryMeasure target ≪
        C.independentPairHybridOffTargetBoundaryMeasure target) :
    Measure.map Prod.snd
        (C.singleLinkHeatBathBoundaryTargetPairMeasure target) ≪
      Measure.map Prod.snd
        (C.independentPairHybridBoundaryDrivenTargetPairMeasure target) := by
  have hJoint :
      C.singleLinkHeatBathBoundaryTargetPairMeasure target ≪
        C.independentPairHybridBoundaryDrivenTargetPairMeasure target :=
    (continuous_compact_oriented_native_absolutelyContinuous_independentPairHybridBoundaryDrivenTargetPairMeasure_iff
      C target).2 hBoundary
  exact hJoint.map measurable_snd

end

end MathlibAnalytic
end MGAP4D
