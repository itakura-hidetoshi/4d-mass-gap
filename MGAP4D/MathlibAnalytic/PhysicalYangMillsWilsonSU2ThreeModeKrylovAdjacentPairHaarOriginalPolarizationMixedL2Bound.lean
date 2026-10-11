import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCoreRepresentativeInvariance
import Mathlib.Tactic

/-!
# P4-Q2-BT: original Wilson Haar polarization mixed physical joint-L² bound

BS proves the LITERAL original Wilson twelve-color mass-weighted Haar reference
polarization is independent of concrete representatives on the image of the
bounded strongly measurable physical Wilson joint core.

This file establishes its sharp-in-our-conventions uniform two-input norm
estimate. Unlike the elementary one-input estimate
`Q(F) ≤ 12 * ‖T F‖²`, this is a genuine MIXED inequality:
`|B(F,G)| ≤ 12 * ‖T F‖ * ‖T G‖`.

The key proof uses positivity and BN's original Wilson parallelogram to
sharpen `|B(F,G)| ≤ (Q(F)+Q(G))/2`; then optimizes the two arguments
by scaling F with ‖T G‖ and G with ‖T F‖. The zero-norm cases are disposed
of using BS's proved annihilation of the physical L² kernel.

No independent links, Haar-mass floor, reverse reference Poincare,
additional beta cutoff, or continuum mass-gap result is assumed.
This is the exact bound needed for well-defined continuous descent.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1800000

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

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "Q" =>
  p4Q2BP_originalCoreReference H N hN beta hbeta
local notation "B" =>
  p4Q2BP_originalCorePolarization H N hN beta hbeta
local notation "T" =>
  p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta

/-- Improved elementary estimate on the exact ORIGINAL Wilson reference:
the positivity and parallelogram remove the factor two from BQ. -/
theorem p4Q2BT_originalCorePolarization_abs_le_half_energy
    (F G : Core) :
    |B F G| ≤ (Q F + Q G) / 2 := by
  have hp :=
    p4Q2BP_originalCoreReference_parallelogram
      H N hN beta hbeta F G
  have hplus : 0 ≤ Q (F + G) :=
    p4Q2BQ_originalCoreReference_nonneg H N hN beta hbeta (F + G)
  have hminus : 0 ≤ Q (F - G) :=
    p4Q2BQ_originalCoreReference_nonneg H N hN beta hbeta (F - G)
  change |(Q (F + G) - Q (F - G)) / 4| ≤ (Q F + Q G) / 2
  apply abs_le.mpr
  constructor <;> linarith

/-- Mixed original Wilson Haar polarization estimate in the ACTUAL
physical Wilson ground-state joint-L² norm, all β ≥ 0:
`|B(F,G)| ≤ 12 * ‖T F‖ * ‖T G‖`.
The constant 12 is inherited from the original all-color sum normalization,
and no coercivity or hidden L² representative assumption is introduced. -/
theorem p4Q2BT_originalCorePolarization_abs_le_physicalL2_norm_mul
    (F G : Core) :
    |B F G| ≤ (12 : ℝ) * (‖T F‖ * ‖T G‖) := by
  let u : ℝ := ‖T F‖
  let v : ℝ := ‖T G‖
  by_cases hFzero : T F = 0
  · have hb :=
      p4Q2BS_originalPolarization_zero_left_of_physicalL2_zero
        H N hN beta hbeta F G hFzero
    simp [hb, hFzero]
  by_cases hGzero : T G = 0
  · have hb :=
      p4Q2BS_originalPolarization_zero_right_of_physicalL2_zero
        H N hN beta hbeta F G hGzero
    simp [hb, hGzero]
  have huPos : 0 < u := by
    dsimp [u]
    exact norm_pos_iff.mpr hFzero
  have hvPos : 0 < v := by
    dsimp [v]
    exact norm_pos_iff.mpr hGzero
  have huNonneg : 0 ≤ u := huPos.le
  have hvNonneg : 0 ≤ v := hvPos.le
  have hQF : Q F ≤ (12 : ℝ) * u ^ 2 :=
    p4Q2BR_originalCoreReference_le_physicalL2_normSq
      H N hN beta hbeta F
  have hQG : Q G ≤ (12 : ℝ) * v ^ 2 :=
    p4Q2BR_originalCoreReference_le_physicalL2_normSq
      H N hN beta hbeta G
  have hscaled :=
    p4Q2BT_originalCorePolarization_abs_le_half_energy
      H N hN beta hbeta (v • F) (u • G)
  rw [
    p4Q2BQ_originalCorePolarization_smul_left
      H N hN beta hbeta v F (u • G),
    p4Q2BQ_originalCorePolarization_smul_right
      H N hN beta hbeta u F G,
    p4Q2BQ_originalCoreReference_smul
      H N hN beta hbeta v F,
    p4Q2BQ_originalCoreReference_smul
      H N hN beta hbeta u G] at hscaled
  have hscaledF :
      v ^ 2 * Q F ≤ (12 : ℝ) * (u * v) ^ 2 := by
    calc
      v ^ 2 * Q F ≤ v ^ 2 * ((12 : ℝ) * u ^ 2) :=
        mul_le_mul_of_nonneg_left hQF (sq_nonneg v)
      _ = (12 : ℝ) * (u * v) ^ 2 := by ring
  have hscaledG :
      u ^ 2 * Q G ≤ (12 : ℝ) * (u * v) ^ 2 := by
    calc
      u ^ 2 * Q G ≤ u ^ 2 * ((12 : ℝ) * v ^ 2) :=
        mul_le_mul_of_nonneg_left hQG (sq_nonneg u)
      _ = (12 : ℝ) * (u * v) ^ 2 := by ring
  have hAbs :
      |v * (u * B F G)| = (u * v) * |B F G| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hvNonneg,
      abs_of_nonneg huNonneg]
    ring
  rw [hAbs] at hscaled
  have hProduct :
      (u * v) * |B F G| ≤ (12 : ℝ) * (u * v) ^ 2 := by
    linarith [hscaledF, hscaledG]
  have hPos : 0 < u * v := mul_pos huPos hvPos
  have hMul :
      (u * v) * |B F G| ≤ (u * v) * ((12 : ℝ) * (u * v)) := by
    calc
      (u * v) * |B F G| ≤ (12 : ℝ) * (u * v) ^ 2 := hProduct
      _ = (u * v) * ((12 : ℝ) * (u * v)) := by ring
  have hFinal : |B F G| ≤ (12 : ℝ) * (u * v) :=
    (mul_le_mul_left hPos).mp hMul
  exact hFinal

/-- Norm version for the ACTUAL original Wilson real bilinear map, not
the distinct physical conditional-expectation twelve-color form. -/
theorem p4Q2BT_originalWilsonPolarBilin_norm_le_physicalL2_norm_mul
    (F G : Core) :
    ‖p4Q2BQ_originalWilsonPolarBilin H N hN beta hbeta F G‖ ≤
      (12 : ℝ) * (‖T F‖ * ‖T G‖) := by
  change ‖B F G‖ ≤ (12 : ℝ) * (‖T F‖ * ‖T G‖)
  rw [Real.norm_eq_abs]
  exact p4Q2BT_originalCorePolarization_abs_le_physicalL2_norm_mul
    H N hN beta hbeta F G

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
