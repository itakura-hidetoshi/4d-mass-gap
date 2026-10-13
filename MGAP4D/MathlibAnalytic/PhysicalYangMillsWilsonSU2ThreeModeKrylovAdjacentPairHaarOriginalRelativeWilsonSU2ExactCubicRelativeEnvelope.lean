import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2ExactSixColorCardinality
import Mathlib.Tactic

/-!
# P4-Q2-ET: Exact cubic envelope on the genuine physical SU(2) relative witness

ES proves that each ACTUAL original Wilson spatial six-color contains exactly
4*(H+1)^3 physical links. EQ bounds the ratio of the original Wilson
Haar-reference Riesz quadratic AW to the DIFFERENT genuine interacting
physical conditional Dirichlet D12 on the SAME concrete gauge-invariant
SU(2) relative-link observable. Combining them sharpens the bound to
the exact cubic coefficient 3/(H+1)^3.

The original mass-floor m>0 and variance witness M>=0 are retained as
finite-H data, not replaced by an artificial independent Haar law.
No absolute AW or D12 spectral no-go and no continuum mass-gap assertion.
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

section ActualPhysicalCubicEnvelope

variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "W" => p4Q2EE_SU2_physicalWilsonJointL2 H
local notation "E" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H 2 (Nat.zero_lt_succ 1)
local notation "Q" =>
  p4Q2BX_originalFullJointQuadratic H 2 (Nat.zero_lt_succ 1)

/-- Genuine physical six-color maximum cardinality is EXACTLY the
same actual cubic number for every original spatial color, not merely
bounded by the total physical spatial link number. -/
theorem p4Q2ET_actualMaxSixColorCard_exact :
    p4Q2EB_maxColorCard H = 4 * (H + 1) ^ 3 := by
  apply le_antisymm
  · unfold p4Q2EB_maxColorCard
    apply Finset.sup_le
    intro c _
    exact (p4Q2ES_actualSixColorLinkCard_exact H c).le
  · calc
      4 * (H + 1) ^ 3 =
          Fintype.card (p4Q2BA_ColorLinks H (0 : Fin 6)) :=
        (p4Q2ES_actualSixColorLinkCard_exact H 0).symm
      _ ≤ p4Q2EB_maxColorCard H :=
        p4Q2EB_colorCard_le_max H 0

/-- Original spatial-color count cast to real scalar with the native
periodic cubic power. This remains an ACTUAL physical count. -/
private theorem p4Q2ET_selectedColorCard_real
    (e : Link) :
    (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ) =
      (4 : ℝ) * (H + 1 : ℝ) ^ 3 := by
  exact_mod_cast p4Q2ES_selectedPhysicalColorLinkCard_exact H e

/-- The exact factor-12 original unnormalized Haar Riesz versus the
genuine normalized physical D12 coefficient is 3/(H+1)^3.
No equality of the two forms/operators is asserted. -/
private theorem p4Q2ET_twelve_div_actualColorCard
    (e : Link) :
    (12 : ℝ) / (p4Q2EQ_SU2_selectedPhysicalColorLinkCard H e : ℝ) =
      (3 : ℝ) / (H + 1 : ℝ) ^ 3 := by
  rw [p4Q2ET_selectedColorCard_real]
  have hden : (H + 1 : ℝ) ^ 3 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- ANY real relative AW >= κ D12 comparison coefficient holding on
this actual SU(2) gauge-invariant physical Wilson witness satisfies
the EXACT cubic spatial-volume necessary upper envelope. -/
theorem p4Q2ET_SU2_anyRelativeCoefficient_le_three_div_cube
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link)
    (κ : ℝ)
    (hLower :
      κ * E beta hbeta (W beta hbeta e) ≤
        Q beta hbeta (W beta hbeta e)) :
    κ ≤ (3 : ℝ) / (H + 1 : ℝ) ^ 3 := by
  have hBound :=
    p4Q2EQ_SU2_anyRelativeCoefficient_le_twelve_div_selectedColorCard
      H beta hbeta e κ hLower
  exact hBound.trans (le_of_eq (p4Q2ET_twelve_div_actualColorCard H e))

/-- Equivalent coefficient-times-true-periodic-spatial-volume envelope,
valid at arbitrary original finite H and nonnegative beta. -/
theorem p4Q2ET_SU2_anyRelativeCoefficient_mul_cube_le_three
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link)
    (κ : ℝ)
    (hLower :
      κ * E beta hbeta (W beta hbeta e) ≤
        Q beta hbeta (W beta hbeta e)) :
    κ * (H + 1 : ℝ) ^ 3 ≤ 3 := by
  have hCoeff :=
    p4Q2ET_SU2_anyRelativeCoefficient_le_three_div_cube
      H beta hbeta e κ hLower
  have hCubePos : 0 < (H + 1 : ℝ) ^ 3 := by positivity
  exact (le_div_iff₀ hCubePos).mp hCoeff

/-- The ORIGINAL strictly positive finite-H physical Wilson EC mass and
variance certificate itself obeys the exact cubic physical witness envelope.
No uniform lower coefficient is obtained from this finite-H statement. -/
theorem p4Q2ET_SU2_originalEC_coefficient_le_three_div_cube
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M ∧
      p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M ≤
        (3 : ℝ) / (H + 1 : ℝ) ^ 3 := by
  obtain ⟨m, M, hm, hM, hκ, hBound⟩ :=
    p4Q2EQ_SU2_originalEC_coefficient_le_twelve_div_selectedColorCard
      H beta hbeta e
  refine ⟨m, M, hm, hM, hκ, ?_⟩
  exact hBound.trans (le_of_eq (p4Q2ET_twelve_div_actualColorCard H e))

/-- The SAME actual SU(2) gauge-invariant Wilson selected two-link
original-Haar / interacting-physical two-color Rayleigh quotient lies
between genuine EC's positive finite-H coefficient /12 and the exact
original physical cubic 1/[4(H+1)^3] upper. -/
theorem p4Q2ET_SU2_selectedHaar_physicalTwoColor_exactCubicRatio
    (beta : ℝ) (hbeta : 0 ≤ beta) (e : Link) :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      0 < p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M ∧
      0 < p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e ∧
      p4Q2EC_originalSharpMaxColorRieszCoefficient H beta m M / 12 ≤
        p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e /
          p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e ∧
      p4Q2EP_SU2_selectedOriginalWilsonHaarReal H beta hbeta e /
          p4Q2EP_SU2_selectedPhysicalWilsonTwoColorDefects H beta hbeta e ≤
        ((4 : ℝ) * (H + 1 : ℝ) ^ 3)⁻¹ := by
  obtain ⟨m, M, hm, hM, hκ, hPos, hLower, hUpper⟩ :=
    p4Q2EQ_SU2_selectedHaar_physicalTwoColor_sharperRatio
      H beta hbeta e
  refine ⟨m, M, hm, hM, hκ, hPos, hLower, ?_⟩
  rw [p4Q2ET_selectedColorCard_real H e] at hUpper
  exact hUpper

end ActualPhysicalCubicEnvelope
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2ET_actualMaxSixColorCard_exact
#print axioms MGAP4D.MathlibAnalytic.p4Q2ET_SU2_anyRelativeCoefficient_le_three_div_cube
#print axioms MGAP4D.MathlibAnalytic.p4Q2ET_SU2_anyRelativeCoefficient_mul_cube_le_three
#print axioms MGAP4D.MathlibAnalytic.p4Q2ET_SU2_originalEC_coefficient_le_three_div_cube
#print axioms MGAP4D.MathlibAnalytic.p4Q2ET_SU2_selectedHaar_physicalTwoColor_exactCubicRatio
