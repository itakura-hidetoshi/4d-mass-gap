import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRightFiberVarianceFubiniTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitDirectFiberBridge
import Mathlib.Tactic

/-!
# P4-Q2-DK: original Wilson right split is the true pair-Haar Hilbert defect

DJ proves Fubini's formula on the actual original Wilson right-link
(left×off-right)×SU(N) Haar split, without introducing an alternate law.
DA/CY/DI prove the coordinate Haar mean and its genuine Hilbert L²
orthogonal projection on the actual same original spatial pair-Haar law.

This module proves the literal two descriptions of the selected right
link update are IDENTICAL pointwise on original configurations, so the
original Wilson direct Haar mean equals the genuine right-coordinate
Haar mean. The original Wilson outer-Haar integrated right fiber
variance is consequently exactly the CR Hilbert L² squared coordinate
projection defect (for every bounded strongly measurable representative).

No positive-beta interacting coordinate commutation, surrogate measure,
or continuum Yang--Mills mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

/-- Literal original right-link split context in the same canonical
physical carrier as DJ. Avoid referring to a declaration scoped privately
inside a distinct Lean module. -/
private abbrev p4Q2DK_rightContext (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Type :=
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)

private noncomputable def p4Q2DK_rightOuterHaar (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (p4Q2DK_rightContext H N target) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
    (Measure.pi
      (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

section ActualRightLink
variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "muH" => normalizedCompactHaar G
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N
local notation "Section" =>
  periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection H N

/-- Literal right update of the original two boundary configurations
equals an update at the right-summand coordinate of the actual canonical
joint finite-product measurable equivalence. -/
theorem p4Q2DK_rightUpdate_eq_jointCoordinateUpdate
    (target : Link) (z : Joint) (u : G) :
    (z.1, Function.update z.2 target u) =
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
        H N).symm
        (Function.update
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
            H N z) (Sum.inr target) u) := by
  classical
  apply Prod.ext
  · funext j
    change z.1 j =
      (Function.update
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
          H N z) (Sum.inr target) u) (Sum.inl j)
    simp
  · funext j
    change (Function.update z.2 target u) j =
      (Function.update
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
          H N z) (Sum.inr target) u) (Sum.inr j)
    by_cases hj : j = target
    · subst j
      simp
    · simp [hj]

/-- A direct SU(N) fiber section in CJ's ORIGINAL Wilson coordinates is
literally the same observable as updating the selected right boundary
link, with the other physical coordinates fixed. -/
theorem p4Q2DK_originalRightSection_eq_update
    (target : Link) (F : Joint → ℝ) (z : Joint) (u : G) :
    Section target F z.1
      (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.2) u =
      F (z.1, Function.update z.2 target u) := by
  classical
  let split :=
    periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
      (Gauge := G) target
  let ev :=
    periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
      (Gauge := G) target
  have hs :=
    periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update
      target z.2 (ev.symm u)
  change F (z.1, split.symm
      (ev.symm u, periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.2)) =
        F (z.1, Function.update z.2 target u)
  rw [hs, ev.apply_symm_apply]

/-- The original Wilson RIGHT Haar mean is precisely CU's literal
coordinate Haar mean, for every concrete function and every full joint
configuration. No conditional-law or L² point evaluation is invoked. -/
theorem p4Q2DK_originalRightRetainedHaarMean_eq_CU
    (target : Link) (F : Joint → ℝ) (z : Joint) :
    p4Q2CJ_rightRetainedHaarMean H N target F z =
      p4Q2CU_actualPairHaarCoordinateMean H N (Sum.inr target) F z := by
  classical
  unfold p4Q2CJ_rightRetainedHaarMean
    p4Q2CU_actualPairHaarCoordinateMean
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    calc
      Section target F z.1
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.2) u =
          F (z.1, Function.update z.2 target u) :=
        p4Q2DK_originalRightSection_eq_update H N target F z u
      _ = F ((periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
            H N).symm
          (Function.update
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
              H N z) (Sum.inr target) u)) := by
        rw [← p4Q2DK_rightUpdate_eq_jointCoordinateUpdate H N target z u]

/-- Under the exact original Wilson direct split equivalence, the
retained physical right-Haar mean at a reconstructed configuration is
the Haar integral of the same original direct-link reconstructed
sections. -/
theorem p4Q2DK_retainedMean_reconstruct
    (target : Link) (F : Joint → ℝ)
    (ctx : p4Q2DK_rightContext H N target) (g : G) :
    p4Q2CJ_rightRetainedHaarMean H N target F
        (p4Q2CJ_directLinkJointMeasurableEquiv H N target (ctx, g)) =
      ∫ u : G, F
        (p4Q2CJ_directLinkJointMeasurableEquiv H N target (ctx, u))
        ∂muH := by
  classical
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := G) target
  let ev := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := G) target
  have hoff :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target
        (split.symm (ev.symm g, ctx.2)) = ctx.2 := by
    rw [← periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv_snd]
    exact congrArg Prod.snd (split.apply_symm_apply _)
  change (∫ u : G, Section target F ctx.1
      (periodicHypercubicEvenSpatialSliceOffTargetRestriction target
        (split.symm (ev.symm g, ctx.2))) u ∂muH) =
        ∫ u : G, Section target F ctx.1 ctx.2 u ∂muH
  rw [hoff]

/-- The direct original Wilson right-fiber mean, transported back
from the split, is pointwise the genuine right coordinate Haar mean. -/
theorem p4Q2DK_originalDirectFiberMean_eq_CU
    (target : Link) (F : Joint → ℝ) (z : Joint) :
    (∫ u : G, F
      (p4Q2CJ_directLinkJointMeasurableEquiv H N target
        (((p4Q2CJ_directLinkJointMeasurableEquiv H N target).symm z).1, u))
      ∂muH) =
      p4Q2CU_actualPairHaarCoordinateMean H N (Sum.inr target) F z := by
  let e := p4Q2CJ_directLinkJointMeasurableEquiv H N target
  have h := p4Q2DK_retainedMean_reconstruct H N target F
    (e.symm z).1 (e.symm z).2
  rw [e.apply_symm_apply] at h
  exact h.symm.trans
    (p4Q2DK_originalRightRetainedHaarMean_eq_CU H N target F z)

/-- The original Wilson RIGHT reference unweighted Haar fiber variance
is exactly the right-link CR Hilbert L² projection defect squared under
the SAME original pair-Haar physical law, for every bounded strongly
measurable representative of a real pair-Haar L² vector. -/
theorem p4Q2DK_originalRightHaarFiberVariance_eq_CR_defect
    (target : Link) (f : JH)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hEq : F =ᵐ[muPair] (f : Joint → ℝ)) :
    (∫⁻ ctx : p4Q2DK_rightContext H N target,
      evariance
        (Section target F ctx.1 ctx.2)
        muH
      ∂(p4Q2DK_rightOuterHaar H N target)) =
        ENNReal.ofReal
          (‖f - P (Sum.inr target) f‖ ^ 2) := by
  have hOriginal :=
    p4Q2DJ_originalRightLinkHaarFiberVariance_eq_pairHaarSplitMeanSquare
      H N target F hF
  have hDI :=
    p4Q2DI_actualPairHaarIntegratedFiberVariance_eq_L2_defect_sq
      H N (Sum.inr target) f F hF M hM hEq
  have hDH :=
    p4Q2DH_actualPairHaarIntegratedFiberVariance_eq_CUmeanSquare
      H N (Sum.inr target) F hF
  calc
    (∫⁻ ctx : p4Q2DK_rightContext H N target,
      evariance (Section target F ctx.1 ctx.2) muH
      ∂(p4Q2DK_rightOuterHaar H N target)) =
      ∫⁻ z : Joint, ENNReal.ofReal
        ((F z -
          ∫ u : G, F
            (p4Q2CJ_directLinkJointMeasurableEquiv H N target
              (((p4Q2CJ_directLinkJointMeasurableEquiv H N target).symm z).1, u))
            ∂muH) ^ 2)
        ∂muPair := hOriginal
    _ = ∫⁻ z : Joint,
          ENNReal.ofReal ((F z -
            p4Q2CU_actualPairHaarCoordinateMean H N (Sum.inr target) F z) ^ 2)
          ∂muPair := by
      apply lintegral_congr
      intro z
      rw [p4Q2DK_originalDirectFiberMean_eq_CU H N target F z]
    _ = (∫⁻ a : {j : I // j ≠ (Sum.inr target : I)} → G,
      evariance (fun u : G =>
        F ((p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N
          (Sum.inr target)).symm (a, u)))
        muH ∂(Measure.pi
          (fun _ : {j : I // j ≠ (Sum.inr target : I)} => muH))) := hDH.symm
    _ = ENNReal.ofReal
          (‖f - P (Sum.inr target) f‖ ^ 2) := hDI

end ActualRightLink
end

end MathlibAnalytic
end MGAP4D
