import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2SelectedHaarStrictDefects
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2TwoCoordinateHaarReference
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalBoundedCoreKernelExactFrontier
import Mathlib.Tactic

/-!
# P4-Q2-EI: strictly positive genuine ORIGINAL Wilson Haar reference for a physical SU(2) witness

EE constructs one actual gauge-invariant bounded continuous relative-link SU(2)
Wilson-energy observable F_e on the original physical pair-spatial carrier,
with separate original Wilson and independent pair-Haar joint L² classes.
EF and EG show EXACT pair-Haar coordinate support only at the genuine
left and right copies of the selected physical spatial link. EH now proves
BOTH selected independent pair-Haar projection residuals STRICTLY POSITIVE,
using the actual normalized SU(2) Haar open support and Wilson-energy
nonconstancy.

The original EB/EG positive finite-volume physical Wilson fiber-mass
comparison therefore has a STRICTLY POSITIVE left-hand side for this
genuine gauge-invariant F_e, and consequently its ACTUAL original Wilson
normalized twelve-color Haar-reference energy is STRICTLY POSITIVE.
The literal original unnormalized twelve-color Wilson Haar reference
and its full physical joint L² Riesz quadratic are also positive for the
SAME concrete observable via the exact BD/BP/EE definitions.

Important: this does NOT replace the original mass-weighted Haar reference
with independent pair-Haar energy or with the separate interacting
physical conditional Dirichlet D12. It adds no claim that every
physically admissible observable admits an H-uniform lower bound.
The finite-H Wilson fiber mass coefficient remains m(H,2,beta)>0.
No new axioms, sorry, or synthetic physical probability laws.
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

section ActualSU2PositiveOriginalWilsonReference

variable (H : ℕ)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "muPair" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H 2
local notation "f" => p4Q2EE_SU2_pairHaarJointL2 H
local notation "F" => p4Q2EE_SU2_relativeWilsonEnergyBCF H

/-- EB's TRUE finite-volume Wilson/Haar mass lower bound and EH's two
STRICTLY positive selected pair-Haar coordinate residuals imply the
original physical Wilson normalized twelve-color Haar-reference energy
is STRICTLY positive for the SAME actual SU(2) gauge-invariant witness. -/
theorem p4Q2EI_SU2_originalWilsonNormalizedHaarReference_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    0 <
      p4Q2BC_originalPhysicalTwelveColorHaarReference H 2
        (by norm_num) beta hbeta (fun z : Joint => F e z) := by
  obtain ⟨m, hm, hLower⟩ :=
    p4Q2EG_SU2_originalWilsonReference_ge_selectedTwoHaarDefects
      H beta hbeta e
  obtain ⟨hLeft, _hRight⟩ :=
    p4Q2EH_bothSelectedPairHaarDefects_pos H e
  have hSelected :
      0 <
        ENNReal.ofReal (‖f e - P (Sum.inl e) (f e)‖ ^ 2) +
          ENNReal.ofReal (‖f e - P (Sum.inr e) (f e)‖ ^ 2) := by
    have hLp : 0 <
        ENNReal.ofReal (‖f e - P (Sum.inl e) (f e)‖ ^ 2) :=
      ENNReal.ofReal_pos.mpr hLeft
    exact lt_of_lt_of_le hLp (le_add_right le_rfl)
  have hCoefficient : 0 <
      p4Q2EB_maxColorHilbertFloorCoefficient H beta m :=
    p4Q2EB_maxColorHilbertFloorCoefficient_pos H beta m hm
  exact (ENNReal.mul_pos_iff.mpr ⟨hCoefficient, hSelected⟩).trans_le hLower

/-- The literal ORIGINAL UNNORMALIZED twelve-color Wilson Haar-reference
real energy is strictly positive for this bounded, strongly measurable,
simultaneously gauge-invariant SU(2) relative-link Wilson observable. -/
theorem p4Q2EI_SU2_originalWilsonUnnormalizedHaarReferenceReal_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    0 <
      p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
        H 2 (by norm_num) beta hbeta (fun z : Joint => F e z) := by
  let sumRef : ENNReal :=
    ∑ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
      p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H 2 (by norm_num) beta hbeta c (fun z : Joint => F e z)
  have hNormalized :
      0 < (12 : ENNReal)⁻¹ * sumRef := by
    simpa only [p4Q2BC_originalPhysicalTwelveColorHaarReference, sumRef] using
      p4Q2EI_SU2_originalWilsonNormalizedHaarReference_pos
        H beta hbeta e
  have hSumPos : 0 < sumRef := by
    by_contra hNot
    have hZero : sumRef = 0 :=
      le_antisymm (not_lt.mp hNot) bot_le
    simp [hZero] at hNormalized
  have hStrong : StronglyMeasurable (fun z : Joint => F e z) :=
    (F e).continuous.stronglyMeasurable
  have hBound : ∀ z : Joint, ‖F e z‖ ≤ (2 : ℝ) := by
    intro z
    have hz := p4Q2EE_SU2_relativeWilsonEnergyBCF_mem_Icc H e z
    have habs : |F e z| ≤ (2 : ℝ) :=
      abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
    simpa [Real.norm_eq_abs] using habs
  have hFinite : sumRef ≠ ∞ :=
    p4Q2BD_originalWilsonTwelveColorHaarReference_ne_top
      H 2 (by norm_num) beta hbeta
      (fun z : Joint => F e z) hStrong 2 hBound
  change 0 < sumRef.toReal
  exact ENNReal.toReal_pos hSumPos.ne' hFinite

/-- The TRUE original Wilson full physical joint-L² Riesz quadratic is
strictly positive on this ACTUAL gauge-invariant SU(2) relative-link class.
This follows from EE's literal original core-quadratic identity, not by
identifying the interacting physical D12 and the Haar-reference forms. -/
theorem p4Q2EI_SU2_originalWilsonFullJointRieszQuadratic_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    0 <
      p4Q2BX_originalFullJointQuadratic H 2 (by norm_num) beta hbeta
        (p4Q2EE_SU2_physicalWilsonJointL2 H beta hbeta e) := by
  rw [p4Q2EE_SU2_originalWilsonRieszQuadratic_eq_literal H beta hbeta e]
  change 0 <
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H 2 (by norm_num) beta hbeta
      ((p4Q2EE_SU2_originalWilsonPhysicalCore H e).1)
  have hFunction :
      ((p4Q2EE_SU2_originalWilsonPhysicalCore H e).1 : Joint → ℝ) =
        (fun z : Joint => F e z) := by
    funext z
    exact p4Q2EE_SU2_originalWilsonPhysicalCore_apply H e z
  rw [hFunction]
  exact p4Q2EI_SU2_originalWilsonUnnormalizedHaarReferenceReal_pos
    H beta hbeta e

end ActualSU2PositiveOriginalWilsonReference
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EI_SU2_originalWilsonNormalizedHaarReference_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2EI_SU2_originalWilsonUnnormalizedHaarReferenceReal_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2EI_SU2_originalWilsonFullJointRieszQuadratic_pos
