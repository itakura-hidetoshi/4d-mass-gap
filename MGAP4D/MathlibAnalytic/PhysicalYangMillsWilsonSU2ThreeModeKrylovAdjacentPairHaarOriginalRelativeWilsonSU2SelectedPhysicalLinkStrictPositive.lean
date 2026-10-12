import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2OffTargetPhysicalHaarFiberZero
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalAllLinkHaarMassFloorHilbertDefects
import Mathlib.Tactic

/-!
# P4-Q2-EK: genuine selected left/right original Wilson link reference positivity

EH proves strict independent pair-Haar projection defects on BOTH physical
coordinates of one actual gauge-invariant SU(2) relative Wilson-energy
observable. DG supplies a SINGLE positive finite-H lower Wilson fiber mass
for every original right and left link; DO identifies its original Haar
variance mass floor exactly with the corresponding separate independent
pair-Haar Hilbert defect, using the actual unswapped physical coordinates.

We derive a shared genuine Wilson mass witness on this concrete observable
and strictly positive ACTUAL original Wilson left AND right one-link Haar
reference energies. Unlike EH, the conclusion is on original physical
Wilson Haar REFERENCES, not just pair-Haar projection residuals.

EJ proves original Wilson weighted off-target literal squared differences
vanish. EK proves both selected physical link reference energies positive.
Neither result identifies original reference with interacting Wilson
conditional expectations, asserts their commutation, or provides any
H-/spacing-uniform or continuum Yang--Mills gap.
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

section ActualOriginalWilsonSelectedLinks

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H 2
local notation "f" => p4Q2EE_SU2_pairHaarJointL2 H
local notation "F" => p4Q2EE_SU2_relativeWilsonEnergyBCF H

/-- The SAME strictly positive actual finite-volume original Wilson fiber
mass witnesses a quantitative, separate lower bound on both selected link
references of the one genuine gauge-invariant SU(2) relative observable. -/
theorem p4Q2EK_SU2_selectedOriginalWilsonLinkReference_lower_witness
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    ∃ m : ℝ, 0 < m ∧
      ENNReal.ofReal m *
        (ENNReal.ofReal (Real.exp (-32 * beta)) *
          ENNReal.ofReal (‖f e - P (Sum.inl e) (f e)‖ ^ 2)) ≤
        p4Q2BB_originalLeftLinkHaarReferenceEnergy
          H 2 (by norm_num) beta hbeta e (fun z : Joint => F e z) ∧
      ENNReal.ofReal m *
        (ENNReal.ofReal (Real.exp (-32 * beta)) *
          ENNReal.ofReal (‖f e - P (Sum.inr e) (f e)‖ ^ 2)) ≤
        p4Q2AZ_originalJointHaarReferenceEnergy
          H 2 (by norm_num) beta hbeta e (fun z : Joint => F e z) := by
  obtain ⟨m, hm, hMass⟩ :=
    p4Q2DG_originalBothEndpoints_linkHaarMassFloor
      H 2 (by norm_num) beta hbeta
  have hStrong : StronglyMeasurable (fun z : Joint => F e z) :=
    (F e).continuous.stronglyMeasurable
  have hBound : ∀ z : Joint, ‖F e z‖ ≤ (2 : ℝ) := by
    intro z
    have hz := p4Q2EE_SU2_relativeWilsonEnergyBCF_mem_Icc H e z
    have habs : |F e z| ≤ (2 : ℝ) :=
      abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
    simpa [Real.norm_eq_abs] using habs
  have hEq :
      (fun z : Joint => F e z) =ᵐ[muPair]
        ((f e : Lp ℝ 2 muPair) : Joint → ℝ) :=
    (p4Q2EE_SU2_pairHaarJointL2_ae_eq H e).symm
  refine ⟨m, hm, ?_, ?_⟩
  · rw [← p4Q2DO_originalLeftHaarMassFloor_eq_CR_defect
        H 2 beta m e (f e) (fun z : Joint => F e z)
        hStrong 2 hBound hEq]
    exact (hMass e (fun z : Joint => F e z) hStrong).2
  · rw [← p4Q2DO_originalRightHaarMassFloor_eq_CR_defect
        H 2 beta m e (f e) (fun z : Joint => F e z)
        hStrong 2 hBound hEq]
    exact (hMass e (fun z : Joint => F e z) hStrong).1

/-- The actual original Wilson-Perron LEFT and RIGHT selected-link Haar
reference energies are BOTH STRICTLY POSITIVE for the very same genuine
SU(2) physical gauge-invariant relative-link Wilson-energy observable. -/
theorem p4Q2EK_SU2_bothSelectedOriginalWilsonLinkReferences_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    0 < p4Q2BB_originalLeftLinkHaarReferenceEnergy
      H 2 (by norm_num) beta hbeta e (fun z : Joint => F e z) ∧
    0 < p4Q2AZ_originalJointHaarReferenceEnergy
      H 2 (by norm_num) beta hbeta e (fun z : Joint => F e z) := by
  obtain ⟨m, hm, hLeftBound, hRightBound⟩ :=
    p4Q2EK_SU2_selectedOriginalWilsonLinkReference_lower_witness
      H beta hbeta e
  obtain ⟨hLeft, hRight⟩ :=
    p4Q2EH_bothSelectedPairHaarDefects_pos H e
  have hmPos : 0 < ENNReal.ofReal m :=
    ENNReal.ofReal_pos.mpr hm
  have hExpPos : 0 < ENNReal.ofReal (Real.exp (-32 * beta)) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hLeftFloor :
      0 < ENNReal.ofReal m *
        (ENNReal.ofReal (Real.exp (-32 * beta)) *
          ENNReal.ofReal (‖f e - P (Sum.inl e) (f e)‖ ^ 2)) :=
    ENNReal.mul_pos_iff.mpr
      ⟨hmPos, ENNReal.mul_pos_iff.mpr
        ⟨hExpPos, ENNReal.ofReal_pos.mpr hLeft⟩⟩
  have hRightFloor :
      0 < ENNReal.ofReal m *
        (ENNReal.ofReal (Real.exp (-32 * beta)) *
          ENNReal.ofReal (‖f e - P (Sum.inr e) (f e)‖ ^ 2)) :=
    ENNReal.mul_pos_iff.mpr
      ⟨hmPos, ENNReal.mul_pos_iff.mpr
        ⟨hExpPos, ENNReal.ofReal_pos.mpr hRight⟩⟩
  exact ⟨hLeftFloor.trans_le hLeftBound,
    hRightFloor.trans_le hRightBound⟩

end ActualOriginalWilsonSelectedLinks
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EK_SU2_selectedOriginalWilsonLinkReference_lower_witness
#print axioms MGAP4D.MathlibAnalytic.p4Q2EK_SU2_bothSelectedOriginalWilsonLinkReferences_pos
