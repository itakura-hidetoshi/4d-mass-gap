import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridNativeBoundaryTargetJointBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Canonical full configuration extending one off-target boundary.  The omitted
physical link is filled by the group identity. -/
def ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundarySection
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.OffTargetBoundary target → C.base.Configuration := by
  classical
  exact fun boundary source =>
    if h : source = target then 1 else boundary ⟨source, h⟩

@[simp]
theorem continuous_compact_oriented_offTargetBoundarySection_apply_target
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target) :
    C.offTargetBoundarySection target boundary target = 1 := by
  classical
  simp [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundarySection]

@[simp]
theorem continuous_compact_oriented_offTargetBoundarySection_apply_of_ne
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target)
    (hsource : source ≠ target) :
    C.offTargetBoundarySection target boundary source =
      boundary ⟨source, hsource⟩ := by
  classical
  simp [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundarySection,
    hsource]

/-- The canonical extension of an off-target boundary is continuous. -/
theorem continuous_compact_oriented_offTargetBoundarySection_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (C.offTargetBoundarySection target) := by
  classical
  apply continuous_pi
  intro source
  by_cases hsource : source = target
  · subst source
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundarySection]
      using
        (continuous_const : Continuous
          (fun _ : C.OffTargetBoundary target => (1 : C.base.Gauge)))
  · let source' : {source : C.base.geometry.Edge // source ≠ target} :=
      ⟨source, hsource⟩
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundarySection,
      hsource, source']
      using
        (continuous_apply source' : Continuous
          (fun boundary : C.OffTargetBoundary target => boundary source'))

/-- The canonical boundary extension is measurable. -/
theorem continuous_compact_oriented_offTargetBoundarySection_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.offTargetBoundarySection target) :=
  (continuous_compact_oriented_offTargetBoundarySection_continuous C target).measurable

/-- Restricting the canonical extension recovers the original boundary exactly. -/
@[simp]
theorem continuous_compact_oriented_offTargetBoundaryMap_section
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target) :
    C.offTargetBoundaryMap target
        (C.offTargetBoundarySection target boundary) = boundary := by
  classical
  funext source
  simp [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryMap,
    ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundarySection,
    source.2]

/-- The canonical extension of a configuration's boundary agrees with the
configuration away from the omitted physical link. -/
theorem continuous_compact_oriented_offTargetBoundarySection_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    C.base.AgreeOffLink
      (C.offTargetBoundarySection target (C.offTargetBoundaryMap target A))
      A target := by
  classical
  intro source hsource
  simp [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryMap,
    ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundarySection,
    hsource]

/-- Exact one-link conditional law indexed by the actual off-target boundary. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoundaryConditionalMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target) : Measure C.base.Gauge :=
  C.singleLinkConditionalMeasure
    (C.offTargetBoundarySection target boundary) target

/-- Every boundary-indexed conditional law is a probability measure. -/
theorem continuous_compact_oriented_singleLinkBoundaryConditionalMeasure_isProbabilityMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target) :
    IsProbabilityMeasure
      (C.singleLinkBoundaryConditionalMeasure target boundary) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoundaryConditionalMeasure
  exact
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C (C.offTargetBoundarySection target boundary) target

/-- The native one-link conditional law factors exactly through boundary
restriction. -/
theorem continuous_compact_oriented_singleLinkBoundaryConditionalMeasure_offTargetBoundaryMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    C.singleLinkBoundaryConditionalMeasure target
        (C.offTargetBoundaryMap target A) =
      C.singleLinkConditionalMeasure A target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoundaryConditionalMeasure
  exact
    continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_agreeOffLink
      C _ A target
      (continuous_compact_oriented_offTargetBoundarySection_agreeOffLink
        C target A)

/-- Equal off-target boundaries induce equal exact conditional laws. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_boundary_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A B : C.base.Configuration)
    (hboundary : C.offTargetBoundaryMap target A =
      C.offTargetBoundaryMap target B) :
    C.singleLinkConditionalMeasure A target =
      C.singleLinkConditionalMeasure B target := by
  rw [← continuous_compact_oriented_singleLinkBoundaryConditionalMeasure_offTargetBoundaryMap
    C target A]
  rw [← continuous_compact_oriented_singleLinkBoundaryConditionalMeasure_offTargetBoundaryMap
    C target B]
  rw [hboundary]

/-- Two conditionally independent target-link samples indexed only by their
common off-target boundary. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoundaryConditionalPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target) :
    Measure (C.base.Gauge × C.base.Gauge) :=
  (C.singleLinkBoundaryConditionalMeasure target boundary).prod
    (C.singleLinkBoundaryConditionalMeasure target boundary)

/-- The boundary-indexed conditional-pair law is a probability measure. -/
theorem continuous_compact_oriented_singleLinkBoundaryConditionalPairMeasure_isProbabilityMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target) :
    IsProbabilityMeasure
      (C.singleLinkBoundaryConditionalPairMeasure target boundary) := by
  letI : IsProbabilityMeasure
      (C.singleLinkBoundaryConditionalMeasure target boundary) :=
    continuous_compact_oriented_singleLinkBoundaryConditionalMeasure_isProbabilityMeasure
      C target boundary
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoundaryConditionalPairMeasure
  infer_instance

/-- The configuration-indexed conditional product is exactly the boundary-indexed
conditional-pair law. -/
theorem continuous_compact_oriented_singleLinkBoundaryConditionalPairMeasure_offTargetBoundaryMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    C.singleLinkBoundaryConditionalPairMeasure target
        (C.offTargetBoundaryMap target A) =
      (C.singleLinkConditionalMeasure A target).prod
        (C.singleLinkConditionalMeasure A target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoundaryConditionalPairMeasure
  rw [continuous_compact_oriented_singleLinkBoundaryConditionalMeasure_offTargetBoundaryMap
    C target A]

/-- Insert a boundary beside a pair of target-link values. -/
def ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairBoundaryInsertMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target) :
    C.base.Gauge × C.base.Gauge → C.OffTargetBoundaryTargetPair target :=
  fun z => (boundary, z)

/-- Boundary-target-pair insertion is continuous. -/
theorem continuous_compact_oriented_offTargetBoundaryTargetPairBoundaryInsertMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target) :
    Continuous
      (C.offTargetBoundaryTargetPairBoundaryInsertMap target boundary) := by
  exact
    (continuous_const : Continuous
      (fun _ : C.base.Gauge × C.base.Gauge => boundary)).prodMk
      continuous_id

/-- Boundary-target-pair insertion is measurable. -/
theorem continuous_compact_oriented_offTargetBoundaryTargetPairBoundaryInsertMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target) :
    Measurable
      (C.offTargetBoundaryTargetPairBoundaryInsertMap target boundary) :=
  (continuous_compact_oriented_offTargetBoundaryTargetPairBoundaryInsertMap_continuous
    C target boundary).measurable

/-- Native joint law for one fixed off-target boundary. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoundaryTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target) :
    Measure (C.OffTargetBoundaryTargetPair target) :=
  Measure.map
    (C.offTargetBoundaryTargetPairBoundaryInsertMap target boundary)
    (C.singleLinkBoundaryConditionalPairMeasure target boundary)

/-- Its boundary marginal is Dirac. -/
theorem continuous_compact_oriented_map_fst_singleLinkBoundaryTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target) :
    Measure.map Prod.fst
        (C.singleLinkBoundaryTargetPairMeasure target boundary) =
      Measure.dirac boundary := by
  letI : IsProbabilityMeasure
      (C.singleLinkBoundaryConditionalPairMeasure target boundary) :=
    continuous_compact_oriented_singleLinkBoundaryConditionalPairMeasure_isProbabilityMeasure
      C target boundary
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoundaryTargetPairMeasure
  rw [Measure.map_map measurable_fst
    (continuous_compact_oriented_offTargetBoundaryTargetPairBoundaryInsertMap_measurable
      C target boundary)]
  change Measure.map
      (fun _ : C.base.Gauge × C.base.Gauge => boundary)
      (C.singleLinkBoundaryConditionalPairMeasure target boundary) =
    Measure.dirac boundary
  simp

/-- Its target-pair marginal is the exact conditional product at that boundary. -/
theorem continuous_compact_oriented_map_snd_singleLinkBoundaryTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (boundary : C.OffTargetBoundary target) :
    Measure.map Prod.snd
        (C.singleLinkBoundaryTargetPairMeasure target boundary) =
      C.singleLinkBoundaryConditionalPairMeasure target boundary := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoundaryTargetPairMeasure
  rw [Measure.map_map measurable_snd
    (continuous_compact_oriented_offTargetBoundaryTargetPairBoundaryInsertMap_measurable
      C target boundary)]
  change Measure.map
      (fun z : C.base.Gauge × C.base.Gauge => z)
      (C.singleLinkBoundaryConditionalPairMeasure target boundary) =
    C.singleLinkBoundaryConditionalPairMeasure target boundary
  simp

/-- The configuration-indexed native joint kernel factors pointwise through the
single common off-target boundary. -/
theorem continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairKernel_apply_eq_boundary
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathBoundaryTargetPairKernel target A =
      C.singleLinkBoundaryTargetPairMeasure target
        (C.offTargetBoundaryMap target A) := by
  rw [continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairKernel_apply]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoundaryTargetPairMeasure
  rw [continuous_compact_oriented_singleLinkBoundaryConditionalPairMeasure_offTargetBoundaryMap
    C target A]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairBoundaryInsertMap
    ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairInsertMap
  rfl

/-- Backgrounds with the same off-target boundary induce identical native joint
laws. -/
theorem continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairKernel_apply_eq_of_boundary_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A B : C.base.Configuration)
    (hboundary : C.offTargetBoundaryMap target A =
      C.offTargetBoundaryMap target B) :
    C.singleLinkHeatBathBoundaryTargetPairKernel target A =
      C.singleLinkHeatBathBoundaryTargetPairKernel target B := by
  rw [continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairKernel_apply_eq_boundary
    C target A]
  rw [continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairKernel_apply_eq_boundary
    C target B]
  rw [hboundary]

end

end MathlibAnalytic
end MGAP4D
