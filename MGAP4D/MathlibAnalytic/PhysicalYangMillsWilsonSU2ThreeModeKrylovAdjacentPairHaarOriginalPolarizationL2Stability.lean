import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPolarizationMixedL2Bound
import Mathlib.Tactic

/-!
# P4-Q2-BU: quantitative physical joint-L² stability of ORIGINAL Wilson Haar polarization

BT proves the genuine original mass-weighted Wilson twelve-color Haar
polarization satisfies the MIXED bound with factor 12 in the physical
ground-state joint-L² norm.

This file proves a two-slot perturbation estimate with NO assumption that
the observable representatives are equal, and deduces the corresponding
quadratic-energy local Lipschitz stability:
  |B(F,G)-B(F',G')|
    ≤ 12*(‖T F - T F'‖*‖T G‖
             + ‖T F'‖*‖T G - T G'‖).
  |Q(F)-Q(F')|
    ≤ 12*‖T F - T F'‖*(‖T F‖+‖T F'‖).

The estimates hold for any beta ≥ 0 on the SAME original physical Wilson
joint L², with no new covariance model, altered Wilson fiber masses,
independence assumption, or continuum gap claim.

Combined with the density of bounded Wilson concrete observables, these
estimates are the analytic continuity receipts needed for a further
unique Hilbert-space extension. This file does not assert the extension.
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

/-- Algebraic two-slot telescoping identity for the genuine bilinear
polarization of the ORIGINAL Wilson Haar reference. -/
theorem p4Q2BU_originalPolarization_difference_decomposition
    (F G F' G' : Core) :
    B F G - B F' G' =
      B (F - F') G + B F' (G - G') := by
  have hFirst :
      B F G = B (F - F') G + B F' G := by
    have h :=
      p4Q2BP_originalCorePolarization_add_left
        H N hN beta hbeta (F - F') F' G
    have hf : (F - F') + F' = F := by abel
    rw [hf] at h
    exact h
  have hSecond :
      B F' G = B F' (G - G') + B F' G' := by
    have h :=
      p4Q2BP_originalCorePolarization_add_right
        H N hN beta hbeta F' (G - G') G'
    have hg : (G - G') + G' = G := by abel
    rw [hg] at h
    exact h
  linarith [hFirst, hSecond]

/-- Two-input physical L² continuity bound on the literal Wilson
polarization, retaining the exact unnormalized twelve-color factor 12. -/
theorem p4Q2BU_originalPolarization_two_slot_L2_difference_le
    (F G F' G' : Core) :
    |B F G - B F' G'| ≤ (12 : ℝ) *
      (‖T F - T F'‖ * ‖T G‖ +
        ‖T F'‖ * ‖T G - T G'‖) := by
  have h1 := p4Q2BT_originalCorePolarization_abs_le_physicalL2_norm_mul
    H N hN beta hbeta (F - F') G
  have h2 := p4Q2BT_originalCorePolarization_abs_le_physicalL2_norm_mul
    H N hN beta hbeta F' (G - G')
  calc
    |B F G - B F' G'| =
        |B (F - F') G + B F' (G - G')| := by
      rw [p4Q2BU_originalPolarization_difference_decomposition
        H N hN beta hbeta F G F' G']
    _ ≤ |B (F - F') G| + |B F' (G - G')| :=
      abs_add_le _ _
    _ ≤ (12 : ℝ) * (‖T (F - F')‖ * ‖T G‖) +
        (12 : ℝ) * (‖T F'‖ * ‖T (G - G')‖) :=
      add_le_add h1 h2
    _ = (12 : ℝ) *
        (‖T F - T F'‖ * ‖T G‖ +
          ‖T F'‖ * ‖T G - T G'‖) := by
      rw [map_sub, map_sub]
      ring

/-- Genuine Wilson twelve-color quadratic energy is locally Lipschitz
in the physical joint L² norm, on bounded concrete representatives.
This is a quantitative stronger version of BS's representative invariance. -/
theorem p4Q2BU_originalCoreReference_L2_difference_le
    (F G : Core) :
    |Q F - Q G| ≤ (12 : ℝ) *
      ‖T F - T G‖ * (‖T F‖ + ‖T G‖) := by
  have h :=
    p4Q2BU_originalPolarization_two_slot_L2_difference_le
      H N hN beta hbeta F F G G
  have hDiagF : B F F = Q F :=
    p4Q2BO_originalWilsonRealPolarization_self
      H N hN beta hbeta F.1
  have hDiagG : B G G = Q G :=
    p4Q2BO_originalWilsonRealPolarization_self
      H N hN beta hbeta G.1
  rw [hDiagF, hDiagG] at h
  calc
    |Q F - Q G| ≤ (12 : ℝ) *
      (‖T F - T G‖ * ‖T F‖ +
        ‖T G‖ * ‖T F - T G‖) := h
    _ = (12 : ℝ) * ‖T F - T G‖ *
      (‖T F‖ + ‖T G‖) := by ring

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
