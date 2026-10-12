import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2SelectedPhysicalLinkStrictPositive
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRightFiberHilbertL2Defect
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# P4-Q2-EL: original Wilson selected-link Haar variance support

The real gauge-invariant SU(2) relative-link Wilson-energy observable of
ED–EK is unchanged by replacing a right coordinate other than its selected
spatial link. We transport that exact pointwise fact through the genuine
original right-link split reconstruction (DK and CJ). The original SU(2)
Haar section is therefore constant for EVERY outer physical split context,
so its literal Haar evariance vanishes before weighting by the true Wilson
Perron-vacuum split-fiber mass.

The observable is also invariant under exchange of its two boundaries by
SU(2) Wilson-energy inversion invariance. Hence the genuine original
reflected left-link Haar reference vanishes off the same selected link.

This is an actual original AZ/BB mass-weighted HAAR VARIANCE statement,
strictly stronger than EJ's frozen-density single-update difference-zero
identity. The selected original physical link references are strictly
positive by EK. No Wilson conditional-projection equality or continuum
gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section
set_option maxHeartbeats 1800000
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

section ActualOriginalWilsonOffTargetVariance

variable (H : ℕ)

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Joint" => Cfg × Cfg
local notation "F" => p4Q2EE_SU2_relativeWilsonEnergyBCF H
local notation "Section" =>
  periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection H 2

/-- Off-target, the literal original right Wilson Haar section of the
gauge-invariant relative-link SU(2) observable is a constant function
for every TRUE Wilson split outer context, not just almost everywhere. -/
theorem p4Q2EL_SU2_offTarget_originalRightHaarSection_constant
    (e target : Link) (hOther : target ≠ e)
    (ctx : Cfg ×
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G)) :
    ∃ c : ℝ,
      (fun u : G => Section target (fun z : Joint => F e z) ctx.1 ctx.2 u) =
        (fun _ : G => c) := by
  classical
  let split :=
    periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
      (Gauge := G) target
  let ev :=
    periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
      (Gauge := G) target
  let z : Joint := (ctx.1, split.symm (ev.symm (1 : G), ctx.2))
  have hLeft : z.1 = ctx.1 := rfl
  have hOff :
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.2 =
        ctx.2 := by
    change (split (split.symm (ev.symm (1 : G), ctx.2))).2 = ctx.2
    rw [split.apply_symm_apply]
  have hR : (Sum.inr target :
      PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H) ≠
        Sum.inr e := by
    intro h
    exact hOther (Sum.inr.inj h)
  refine ⟨F e z, ?_⟩
  funext u
  have hs :=
    p4Q2DK_originalRightSection_eq_update
      H 2 target (fun v : Joint => F e v) z u
  have hUpdate :=
    p4Q2DK_rightUpdate_eq_jointCoordinateUpdate H 2 target z u
  have hFixed : F e (z.1, Function.update z.2 target u) = F e z := by
    rw [hUpdate]
    exact p4Q2EF_SU2_relativeWilsonEnergy_otherCoordinate_update_eq
      H e (Sum.inr target) (by simp) hR z u
  simpa only [hLeft, hOff] using hs.trans hFixed

/-- Genuine original right Haar one-link variance vanishes identically
in every physical retained outer context off the selected SU(2) link. -/
theorem p4Q2EL_SU2_offTarget_originalRightHaarVariance_zero
    (e target : Link) (hOther : target ≠ e)
    (ctx : Cfg ×
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G)) :
    evariance
      (Section target (fun z : Joint => F e z) ctx.1 ctx.2)
      (normalizedCompactHaar G) = 0 := by
  obtain ⟨c, hConst⟩ :=
    p4Q2EL_SU2_offTarget_originalRightHaarSection_constant
      H e target hOther ctx
  rw [hConst]
  simp [evariance]

/-- The LITERAL original physical Wilson-Perron split-mass-weighted
Haar VARIANCE reference, not the independent pair-Haar projection,
is zero at EVERY off-target right spatial link. -/
theorem p4Q2EL_SU2_offTarget_originalWilsonRightLinkReference_zero
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (e target : Link) (hOther : target ≠ e) :
    p4Q2AZ_originalJointHaarReferenceEnergy
      H 2 (by norm_num) beta hbeta target
      (fun z : Joint => F e z) = 0 := by
  unfold p4Q2AZ_originalJointHaarReferenceEnergy
  simp [p4Q2EL_SU2_offTarget_originalRightHaarVariance_zero
    H e target hOther]

/-- SU(2) Wilson relative-link energy is invariant under swapping the
two actual physical spatial boundaries, by group inversion symmetry. -/
theorem p4Q2EL_SU2_relativeWilsonEnergy_swap_eq
    (e : Link) (z : Joint) : F e z.swap = F e z := by
  rw [p4Q2EE_SU2_relativeWilsonEnergyBCF_apply,
    p4Q2EE_SU2_relativeWilsonEnergyBCF_apply]
  have hInv :=
    specialUnitaryWilsonPlaquetteEnergy_inv ((z.2 e)⁻¹ * z.1 e)
  simpa only [mul_inv_rev, inv_inv] using hInv.symm

/-- The exact ORIGINAL reflected left-link Wilson Haar reference
vanishes off target, since boundary swapping preserves this observable. -/
theorem p4Q2EL_SU2_offTarget_originalWilsonLeftLinkReference_zero
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (e target : Link) (hOther : target ≠ e) :
    p4Q2BB_originalLeftLinkHaarReferenceEnergy
      H 2 (by norm_num) beta hbeta target
      (fun z : Joint => F e z) = 0 := by
  have hSwap :
      p4Q2BB_swapConcrete H 2 (fun z : Joint => F e z) =
        (fun z : Joint => F e z) := by
    funext z
    exact p4Q2EL_SU2_relativeWilsonEnergy_swap_eq H e z
  change p4Q2AZ_originalJointHaarReferenceEnergy
    H 2 (by norm_num) beta hbeta target
      (p4Q2BB_swapConcrete H 2 (fun z : Joint => F e z)) = 0
  rw [hSwap]
  exact p4Q2EL_SU2_offTarget_originalWilsonRightLinkReference_zero
    H beta hbeta e target hOther

/-- The complete genuine original RIGHT boundary sum over every physical
spatial link equals exactly the reference at its one selected link. -/
theorem p4Q2EL_SU2_originalWilsonAllRightLinks_eq_selected
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    (∑ target : Link,
      p4Q2AZ_originalJointHaarReferenceEnergy
        H 2 (by norm_num) beta hbeta target
        (fun z : Joint => F e z)) =
      p4Q2AZ_originalJointHaarReferenceEnergy
        H 2 (by norm_num) beta hbeta e
        (fun z : Joint => F e z) := by
  classical
  exact Finset.sum_eq_single e
    (by
      intro target _ ht
      exact p4Q2EL_SU2_offTarget_originalWilsonRightLinkReference_zero
        H beta hbeta e target ht)
    (by simp)

/-- The complete genuine original LEFT boundary sum is exactly the
selected LEFT link's strictly positive physical Wilson Haar reference. -/
theorem p4Q2EL_SU2_originalWilsonAllLeftLinks_eq_selected
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    (∑ target : Link,
      p4Q2BB_originalLeftLinkHaarReferenceEnergy
        H 2 (by norm_num) beta hbeta target
        (fun z : Joint => F e z)) =
      p4Q2BB_originalLeftLinkHaarReferenceEnergy
        H 2 (by norm_num) beta hbeta e
        (fun z : Joint => F e z) := by
  classical
  exact Finset.sum_eq_single e
    (by
      intro target _ ht
      exact p4Q2EL_SU2_offTarget_originalWilsonLeftLinkReference_zero
        H beta hbeta e target ht)
    (by simp)

end ActualOriginalWilsonOffTargetVariance
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EL_SU2_offTarget_originalRightHaarSection_constant
#print axioms MGAP4D.MathlibAnalytic.p4Q2EL_SU2_offTarget_originalRightHaarVariance_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2EL_SU2_offTarget_originalWilsonRightLinkReference_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2EL_SU2_relativeWilsonEnergy_swap_eq
#print axioms MGAP4D.MathlibAnalytic.p4Q2EL_SU2_offTarget_originalWilsonLeftLinkReference_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2EL_SU2_originalWilsonAllRightLinks_eq_selected
#print axioms MGAP4D.MathlibAnalytic.p4Q2EL_SU2_originalWilsonAllLeftLinks_eq_selected
