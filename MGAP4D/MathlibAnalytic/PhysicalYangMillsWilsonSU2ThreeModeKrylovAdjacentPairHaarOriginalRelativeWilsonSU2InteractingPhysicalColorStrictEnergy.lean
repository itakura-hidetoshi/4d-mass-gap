import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2OffTargetWilsonVarianceTwoLinkSupport
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGroundStateTwoSidedTwelveColorDirichlet
import Mathlib.Tactic

/-!
# P4-Q2-EM: genuine interacting Wilson color conditional residual witness

EL gives exact two-link support of the actual original Wilson mass-weighted
Haar REFERENCE and the original physical joint-L² Riesz quadratic.
The genuine interacting Wilson twelve-color conditional projections are
different operators. We now connect them rigorously in their OWN physical
joint-L² measure through AZ and BB's original one-link reference upper
comparisons and the sigma-algebra-inclusion color residual inequalities.

For the SAME concrete bounded, gauge-invariant SU(2) relative-link
Wilson-energy witness, both selected right and left PHYSICAL Wilson
color-block conditional-expectation residuals are strictly positive.
No Haar/Wilson measure identification, projection commutation, H-uniform
spectral gap, or continuum mass gap is asserted.
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

section ActualPhysicalWilsonColor

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "F" => p4Q2EE_SU2_relativeWilsonEnergyBCF H
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H 2 (by norm_num)
local notation "W" => p4Q2EE_SU2_physicalWilsonJointL2 H
local notation "C" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H 2 (by norm_num)

/-- Strong measurability and boundedness are certified for the actual
SU(2) two-boundary Wilson-energy BCF, not postulated for an abstract
measurable representative. -/
private theorem p4Q2EM_SU2_physicalWitness_bound
    (e : Link) : ∀ z : Joint, ‖F e z‖ ≤ (2 : ℝ) := by
  intro z
  have hz := p4Q2EE_SU2_relativeWilsonEnergyBCF_mem_Icc H e z
  have habs : |F e z| ≤ (2 : ℝ) :=
    abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
  simpa [Real.norm_eq_abs] using habs

/-- The canonical original AZ L² class and the EE original ground-state
joint L² class coincide, under the physical Wilson law (not pair Haar).
The representative statement is used only up to Wilson-a.e. equality. -/
theorem p4Q2EM_SU2_originalAZJointL2_eq_EE
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    p4Q2AZ_originalJointL2
      H 2 (by norm_num) beta hbeta
      (fun z : Joint => F e z) (F e).continuous.stronglyMeasurable 2
      (p4Q2EM_SU2_physicalWitness_bound H e) =
      W beta hbeta e := by
  apply Lp.ext
  have hAz :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
      H 2 (by norm_num) beta hbeta
      (fun z : Joint => F e z) (F e).continuous.stronglyMeasurable 2
      (p4Q2EM_SU2_physicalWitness_bound H e)
  exact hAz.trans (p4Q2EE_SU2_physicalWilsonJointL2_ae_eq
    H beta hbeta e).symm

/-- Both selected genuine interacting PHYSICAL Wilson twelve-color
conditional-expectation residuals are strictly positive for the
same gauge-invariant SU(2) relative-link observable. This is a
separate measure/operator statement from EL's original Haar reference. -/
theorem p4Q2EM_SU2_bothSelectedPhysicalWilsonColorDefects_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    0 < ‖W beta hbeta e -
      C beta hbeta
        (Sum.inl (periodicHypercubicEvenGroundStateSpatialColorEquivFin
          (periodicHypercubicEvenSpatialSliceLinkColor H e)))
        (W beta hbeta e)‖ ^ 2 ∧
    0 < ‖W beta hbeta e -
      C beta hbeta
        (Sum.inr (periodicHypercubicEvenGroundStateSpatialColorEquivFin
          (periodicHypercubicEvenSpatialSliceLinkColor H e)))
        (W beta hbeta e)‖ ^ 2 := by
  let F0 : Joint → ℝ := fun z => F e z
  have hStrong : StronglyMeasurable F0 := (F e).continuous.stronglyMeasurable
  have hBound : ∀ z : Joint, ‖F0 z‖ ≤ (2 : ℝ) :=
    p4Q2EM_SU2_physicalWitness_bound H e
  let x := p4Q2AZ_originalJointL2
    H 2 (by norm_num) beta hbeta F0 hStrong 2 hBound
  have hx : x = W beta hbeta e :=
    p4Q2EM_SU2_originalAZJointL2_eq_EE H beta hbeta e
  let k : Fin 6 :=
    periodicHypercubicEvenGroundStateSpatialColorEquivFin
      (periodicHypercubicEvenSpatialSliceLinkColor H e)
  have hRightRef :
      0 < p4Q2AZ_originalJointHaarReferenceEnergy
        H 2 (by norm_num) beta hbeta e F0 :=
    (p4Q2EK_SU2_bothSelectedOriginalWilsonLinkReferences_pos
      H beta hbeta e).2
  have hLeftRef :
      0 < p4Q2BB_originalLeftLinkHaarReferenceEnergy
        H 2 (by norm_num) beta hbeta e F0 :=
    (p4Q2EK_SU2_bothSelectedOriginalWilsonLinkReferences_pos
      H beta hbeta e).1
  have hRightLink :=
    p4Q2AZ_originalJointHaarReferenceEnergy_le_physicalCondExpResidual
      H 2 (by norm_num) beta hbeta e F0 hStrong 2 hBound
  have hLeftLink :=
    p4Q2BB_originalLeftLinkHaarReferenceEnergy_le_leftResidual
      H 2 (by norm_num) beta hbeta e F0 hStrong 2 hBound
  have hRightColor :
      ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H 2 (by norm_num) beta hbeta e x‖ ^ 2 ≤
      ‖x -
        C beta hbeta (Sum.inl k) x‖ ^ 2 := by
    simpa only [C,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2,
      k, Equiv.symm_apply_apply] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_residual_sq_le_color
        H 2 (by norm_num) beta hbeta e x)
  have hLeftColor :
      ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H 2 (by norm_num) beta hbeta e x‖ ^ 2 ≤
      ‖x -
        C beta hbeta (Sum.inr k) x‖ ^ 2 := by
    simpa only [C,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2,
      k, Equiv.symm_apply_apply] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_residual_sq_le_color
        H 2 (by norm_num) beta hbeta e x)
  have hRight :
      0 < ENNReal.ofReal (‖x - C beta hbeta (Sum.inl k) x‖ ^ 2) := by
    have ht :
      p4Q2AZ_originalJointHaarReferenceEnergy
          H 2 (by norm_num) beta hbeta e F0 ≤
        ENNReal.ofReal
          (‖x - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H 2 (by norm_num) beta hbeta e x‖ ^ 2) := hRightLink
    exact hRightRef.trans_le (ht.trans (ENNReal.ofReal_le_ofReal hRightColor))
  have hLeft :
      0 < ENNReal.ofReal (‖x - C beta hbeta (Sum.inr k) x‖ ^ 2) := by
    have ht :
      p4Q2BB_originalLeftLinkHaarReferenceEnergy
          H 2 (by norm_num) beta hbeta e F0 ≤
        ENNReal.ofReal
          (‖x - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
            H 2 (by norm_num) beta hbeta e x‖ ^ 2) := hLeftLink
    exact hLeftRef.trans_le (ht.trans (ENNReal.ofReal_le_ofReal hLeftColor))
  have hRealR : 0 < ‖x - C beta hbeta (Sum.inl k) x‖ ^ 2 :=
    ENNReal.ofReal_pos.mp hRight
  have hRealL : 0 < ‖x - C beta hbeta (Sum.inr k) x‖ ^ 2 :=
    ENNReal.ofReal_pos.mp hLeft
  rw [hx] at hRealR hRealL
  exact ⟨hRealR, hRealL⟩

end ActualPhysicalWilsonColor
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EM_SU2_originalAZJointL2_eq_EE
#print axioms MGAP4D.MathlibAnalytic.p4Q2EM_SU2_bothSelectedPhysicalWilsonColorDefects_pos
