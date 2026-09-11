import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkAENormalizedFiberProbability
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkTargetGroupCoordinateEquiv
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Evaluation through the canonical singleton-target measurable equivalence is
literal evaluation at the selected link. -/
@[simp] theorem periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv_apply
    {H : ℕ}
    {Gauge : Type}
    [MeasurableSpace Gauge]
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (targetCfg : PeriodicHypercubicEvenSpatialSliceTargetLink H target → Gauge) :
    periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv target targetCfg =
      targetCfg ⟨target, rfl⟩ := by
  rfl

/-- Reconstructing a complete configuration from a singleton target factor and
the off-target restriction of `right` is exactly the same as updating `right`
at the selected link with the evaluated target factor.

This is a pure coordinate identity. -/
theorem periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update
    {H : ℕ}
    {Gauge : Type}
    [MeasurableSpace Gauge]
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (right : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge)
    (targetCfg : PeriodicHypercubicEvenSpatialSliceTargetLink H target → Gauge) :
    (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv target).symm
        (targetCfg, periodicHypercubicEvenSpatialSliceOffTargetRestriction target right) =
      Function.update right target
        (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv target targetCfg) := by
  classical
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := Gauge) target
  let right' := split.symm
    (targetCfg, periodicHypercubicEvenSpatialSliceOffTargetRestriction target right)
  let g := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv target targetCfg
  have htarget : right' target = g := by
    have h :=
      periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_target target right'
    change (split right').1 ⟨target, rfl⟩ = right' target at h
    rw [show split right' =
      (targetCfg, periodicHypercubicEvenSpatialSliceOffTargetRestriction target right) by
        exact split.apply_symm_apply _] at h
    exact h.symm.trans (by simp [g])
  have hoff :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right' =
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right := by
    have h :=
      periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_snd target right'
    change (split right').2 =
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target right' at h
    rw [show split right' =
      (targetCfg, periodicHypercubicEvenSpatialSliceOffTargetRestriction target right) by
        exact split.apply_symm_apply _] at h
    exact h.symm
  have hself : Function.update right' target g = right' := by
    funext e
    by_cases he : e = target
    · subst e
      simp [htarget]
    · simp [Function.update, he]
  change right' = Function.update right target g
  calc
    right' = Function.update right' target g := hself.symm
    _ = Function.update right target g :=
      periodicHypercubicEvenSpatialSlice_update_eq_of_offTargetRestriction_eq
        target right' right hoff g

/-- Under the direct singleton-target evaluation coordinate, the split
right-joint density is exactly the already-canonical literal direct one-link
ground-state fiber weight.

No Wilson conditional-law identification is made here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_offTargetRestriction_eq_directFiberWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (targetCfg : PeriodicHypercubicEvenSpatialSliceTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
        H N hN beta hbeta left target
          (targetCfg, periodicHypercubicEvenSpatialSliceOffTargetRestriction target right) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right target
          (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv target targetCfg) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight,
    periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update]

/-- The split target-fiber mass over the singleton product Haar carrier is
exactly the existing direct `SU(N)` one-link ground-state fiber mass when the
retained context is the off-target restriction of the complete right boundary.

This is still a ground-state density/coordinate statement, not an RCD or
Wilson conditional-law statement. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_offTargetRestriction_eq_directFiberMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
        H N hN beta hbeta left target
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target right) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
        H N hN beta hbeta left right target := by
  classical
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μGroup := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  have heval : MeasurePreserving eval μTarget μGroup := by
    simpa [eval, μTarget, μGroup] using
      (periodicHypercubicEvenSpatialSliceTargetEvaluation_measurePreserving
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target μGroup)
  have htransport := heval.lintegral_comp_emb eval.measurableEmbedding
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target)
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass]
  calc
    (∫⁻ targetCfg,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
          H N hN beta hbeta left target
            (targetCfg, periodicHypercubicEvenSpatialSliceOffTargetRestriction target right)
      ∂μTarget) =
      ∫⁻ targetCfg,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
          H N hN beta hbeta left right target (eval targetCfg)
      ∂μTarget := by
        apply lintegral_congr
        intro targetCfg
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_offTargetRestriction_eq_directFiberWeight
            H N hN beta hbeta left right target targetCfg
    _ = ∫⁻ g,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
          H N hN beta hbeta left right target g
      ∂μGroup := by
        simpa [eval, μTarget, μGroup] using htransport
    _ = periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
        H N hN beta hbeta left right target := by
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMeasure_apply
          H N hN beta hbeta left right target Set.univ MeasurableSet.univ]
      simp [μGroup]

end

end MathlibAnalytic
end MGAP4D
