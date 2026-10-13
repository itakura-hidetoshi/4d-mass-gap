import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2PhysicalEnergyBilateralBridge
import Mathlib.Tactic

/-!
# P4-Q2-EP: Selected original Wilson Haar references and interacting physical colors

For the SAME genuine SU(2) gauge-invariant relative-link original Wilson
physical joint-L² observable, we retain simultaneously:

* each selected actual Wilson mass-weighted one-link Haar reference
  bounded by its OWN genuine interacting physical Wilson color-conditional
  L² residual (no independent pair-Haar substitute);
* original selected right/left Haar sum with its ACTUAL inverse
  selected-color physical link count;
* genuine normalized twelve-color physical D12 equal to the exactly
  TWO selected interacting physical residuals, with native factor 1/12;
* the SAME original Wilson EC m,M finite-H coefficient in the quantitative
  bilateral comparison and the resulting strictly positive Rayleigh ratio.

No operator identification, H-uniformity, continuum reconstruction,
or Yang–Mills mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace ENNReal

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

section SamePhysicalSelectedColor

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "col" => periodicHypercubicEvenSpatialSliceLinkColor H
local notation "kappa" => periodicHypercubicEvenGroundStateSpatialColorEquivFin
local notation "F" => p4Q2EE_SU2_relativeWilsonEnergyBCF H
local notation "W" => p4Q2EE_SU2_physicalWilsonJointL2 H
local notation "Q" => p4Q2BX_originalFullJointQuadratic H 2 (Nat.zero_lt_succ 1)
local notation "E" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H 2 (Nat.zero_lt_succ 1)
local notation "P12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H 2 (Nat.zero_lt_succ 1)

/-- EXACT original Wilson two selected physical links, with genuine mass
weighted Haar references in ENNReal and inverse cardinality in ENNReal,
then literal toReal. This is NOT the interacting D12 form. -/
noncomputable def p4Q2EP_SU2_selectedOriginalWilsonHaarReal
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) : ℝ :=
  ((Fintype.card (p4Q2BA_ColorLinks H (kappa (col e))) : ENNReal)⁻¹ *
      p4Q2AZ_originalJointHaarReferenceEnergy
        H 2 (Nat.zero_lt_succ 1) beta hbeta e
        (fun z : Joint => F e z) +
    (Fintype.card (p4Q2BA_ColorLinks H (kappa (col e))) : ENNReal)⁻¹ *
      p4Q2BB_originalLeftLinkHaarReferenceEnergy
        H 2 (Nat.zero_lt_succ 1) beta hbeta e
        (fun z : Joint => F e z)).toReal

/-- Exactly the genuine TWO selected right/left interacting Wilson physical
conditional color residuals; no average and no Haar or pair-Haar replacement. -/
noncomputable def p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) : ℝ :=
  ‖W beta hbeta e -
    P12 beta hbeta (Sum.inl (kappa (col e))) (W beta hbeta e)‖ ^ 2 +
  ‖W beta hbeta e -
    P12 beta hbeta (Sum.inr (kappa (col e))) (W beta hbeta e)‖ ^ 2

/-- The SAME canonical original Wilson physical witness has BOTH exact
energies, with their intentionally DIFFERENT normalizations. -/
theorem p4Q2EP_SU2_exactSelectedHaarAndPhysicalColorIdentities
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    Q beta hbeta (W beta hbeta e) =
        p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e ∧
    E beta hbeta (W beta hbeta e) =
        (12 : ℝ)⁻¹ *
          p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e := by
  exact p4Q2EO_SU2_exactOriginalHaarAndInteractingD12_twoSupport
    H beta hbeta e

/-- The two actual selected Wilson one-link Haar references are separately
bounded by THEIR OWN genuine interacting physical Wilson six-color
conditional-projection squared residuals. These comparisons are for the
original finite-volume interacting Wilson physical measure and are not
consequences of any alleged commutation of its conditional projections. -/
theorem p4Q2EP_SU2_bothSelectedOriginalHaarRefs_le_physicalColorDefects
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    p4Q2AZ_originalJointHaarReferenceEnergy
        H 2 (Nat.zero_lt_succ 1) beta hbeta e (fun z : Joint => F e z) ≤
      ENNReal.ofReal
        (‖W beta hbeta e -
          P12 beta hbeta (Sum.inl (kappa (col e))) (W beta hbeta e)‖ ^ 2) ∧
    p4Q2BB_originalLeftLinkHaarReferenceEnergy
        H 2 (Nat.zero_lt_succ 1) beta hbeta e (fun z : Joint => F e z) ≤
      ENNReal.ofReal
        (‖W beta hbeta e -
          P12 beta hbeta (Sum.inr (kappa (col e))) (W beta hbeta e)‖ ^ 2) := by
  let F0 : Joint → ℝ := fun z => F e z
  have hStrong : StronglyMeasurable F0 :=
    (F e).continuous.stronglyMeasurable
  have hBound : ∀ z : Joint, ‖F0 z‖ ≤ (2 : ℝ) := by
    intro z
    have hz := p4Q2EE_SU2_relativeWilsonEnergyBCF_mem_Icc H e z
    have hAbs : |F e z| ≤ (2 : ℝ) :=
      abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
    simpa [F0, Real.norm_eq_abs] using hAbs
  let x := p4Q2AZ_originalJointL2
    H 2 (Nat.zero_lt_succ 1) beta hbeta F0 hStrong 2 hBound
  have hx : x = W beta hbeta e :=
    p4Q2EM_SU2_originalAZJointL2_eq_EE H beta hbeta e
  let k : Fin 6 := kappa (col e)
  have hRightLink :=
    p4Q2AZ_originalJointHaarReferenceEnergy_le_physicalCondExpResidual
      H 2 (Nat.zero_lt_succ 1) beta hbeta e F0 hStrong 2 hBound
  have hLeftLink :=
    p4Q2BB_originalLeftLinkHaarReferenceEnergy_le_leftResidual
      H 2 (Nat.zero_lt_succ 1) beta hbeta e F0 hStrong 2 hBound
  have hRightColor :
      ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H 2 (Nat.zero_lt_succ 1) beta hbeta e x‖ ^ 2 ≤
      ‖x - P12 beta hbeta (Sum.inl k) x‖ ^ 2 := by
    simpa only [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2,
      k, Equiv.symm_apply_apply] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_residual_sq_le_color
        H 2 (Nat.zero_lt_succ 1) beta hbeta e x)
  have hLeftColor :
      ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H 2 (Nat.zero_lt_succ 1) beta hbeta e x‖ ^ 2 ≤
      ‖x - P12 beta hbeta (Sum.inr k) x‖ ^ 2 := by
    simpa only [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2,
      k, Equiv.symm_apply_apply] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_residual_sq_le_color
        H 2 (Nat.zero_lt_succ 1) beta hbeta e x)
  have hRight :
      p4Q2AZ_originalJointHaarReferenceEnergy
          H 2 (Nat.zero_lt_succ 1) beta hbeta e F0 ≤
        ENNReal.ofReal (‖x - P12 beta hbeta (Sum.inl k) x‖ ^ 2) :=
    hRightLink.trans (ENNReal.ofReal_le_ofReal hRightColor)
  have hLeft :
      p4Q2BB_originalLeftLinkHaarReferenceEnergy
          H 2 (Nat.zero_lt_succ 1) beta hbeta e F0 ≤
        ENNReal.ofReal (‖x - P12 beta hbeta (Sum.inr k) x‖ ^ 2) :=
    hLeftLink.trans (ENNReal.ofReal_le_ofReal hLeftColor)
  rw [hx] at hRight hLeft
  exact ⟨hRight, hLeft⟩

/-- Both selected genuine interacting Wilson physical defects are positive,
so their TWO-color sum is strictly positive on the original physical law. -/
theorem p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    0 < p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e := by
  unfold p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects
  obtain ⟨hR, hL⟩ :=
    p4Q2EM_SU2_bothSelectedPhysicalWilsonColorDefects_pos H beta hbeta e
  exact add_pos hR hL

/-- Quantitative DIRECT finite-volume physical two-selected-color versus
original two-selected-link Wilson Haar comparison. The exact true
EC coefficient uses Wilson fiber mass m>0, variance M>=0 and max actual
six-color link cardinality, and is NOT uniform in H by these methods. -/
theorem p4Q2EP_SU2_selectedHaarReal_physicalTwoColor_bilateral
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M ∧
      p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M *
          ((12 : ℝ)⁻¹ *
            p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e) ≤
        p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e ∧
      p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e ≤
        p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e := by
  obtain ⟨m, M, hm, hM, hκ, hLower, hUpper⟩ :=
    p4Q2EO_SU2_explicitWilsonMass_selectedPhysicalBilateral
      H beta hbeta e
  obtain ⟨hQ, hE⟩ :=
    p4Q2EP_SU2_exactSelectedHaarAndPhysicalColorIdentities H beta hbeta e
  refine ⟨m, M, hm, hM, hκ, ?_, ?_⟩
  · calc
      p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M *
          ((12 : ℝ)⁻¹ *
            p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e) =
          p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M *
            E beta hbeta (W beta hbeta e) := by rw [hE]
      _ ≤ Q beta hbeta (W beta hbeta e) := hLower
      _ = p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e := hQ
  · calc
      p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e =
          Q beta hbeta (W beta hbeta e) := hQ.symm
      _ ≤ p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects
          H beta hbeta e := hUpper

/-- A genuine dimensionless SU(2) physical Rayleigh quotient.
The quotient divides by the ACTUAL strictly positive physical TWO-color
defect sum. Its finite-H lower bound is precisely EC's original Wilson
mass-weighted coefficient divided by twelve, and its upper bound is one.
This ratio is not a continuum spectral gap certificate. -/
theorem p4Q2EP_SU2_selectedHaar_over_physicalTwoColor_ratio_bounds
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M ∧
      0 < p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e ∧
      p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M / 12 ≤
        p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e /
          p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e ∧
      p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e /
          p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e ≤ 1 := by
  obtain ⟨m, M, hm, hM, hκ, hLower, hUpper⟩ :=
    p4Q2EP_SU2_selectedHaarReal_physicalTwoColor_bilateral
      H beta hbeta e
  have hPos :=
    p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects_pos H beta hbeta e
  refine ⟨m, M, hm, hM, hκ, hPos, ?_, ?_⟩
  · apply (le_div_iff₀ hPos).2
    calc
      (p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M / 12) *
          p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e =
          p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M *
            ((12 : ℝ)⁻¹ *
              p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e) := by
                ring
      _ ≤ p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e :=
        hLower
  · apply (div_le_iff₀ hPos).2
    simpa only [one_mul] using hUpper

end SamePhysicalSelectedColor
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EP_SU2_exactSelectedHaarAndPhysicalColorIdentities
#print axioms MGAP4D.MathlibAnalytic.p4Q2EP_SU2_bothSelectedOriginalHaarRefs_le_physicalColorDefects
#print axioms MGAP4D.MathlibAnalytic.p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2EP_SU2_selectedHaarReal_physicalTwoColor_bilateral
#print axioms MGAP4D.MathlibAnalytic.p4Q2EP_SU2_selectedHaar_over_physicalTwoColor_ratio_bounds
