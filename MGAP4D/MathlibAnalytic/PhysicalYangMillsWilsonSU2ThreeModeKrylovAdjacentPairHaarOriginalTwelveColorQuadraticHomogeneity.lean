import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalReferenceQuadraticHomogeneity
import Mathlib.Tactic

/-!
# P4-Q2-BI: full original Wilson two-sided twelve-color Haar reference scaling

BH establishes exact quadratic scaling of the LITERAL original Wilson
ground-state mass-weighted right-link Haar reference and each genuine
right spatial color. The ALREADY-PROVED endpoint swap is now used to
transport this result to the original physical LEFT six colors, on the
SAME Wilson joint law and with the same beta-dependent original fiber mass.

All twelve right/left color averages then inherit exact homogeneity:
H_orig(a F) = ofReal(a²) * H_orig(F) in ENNReal.

Both the normalized original physical twelve-color Haar reference and
the unnormalized finite real BD reference are included. No independent
links, surrogate probability law, or reverse reference Poincare is assumed.
This proves quadratic HOMOGENEITY, not full bilinear polarization or
continuity/extension to arbitrary original joint L² classes.
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

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "C12" =>
  PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor

/-- The genuine original LEFT six-color all-link Haar reference inherits
the right-side BH scaling through exact physical endpoint swap. -/
theorem p4Q2BI_originalLeftColorAllLinkReference_mul
    (c : Fin 6) (a : ℝ) (F : Joint → ℝ) :
    p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta c
        (fun z => a * F z) =
      ENNReal.ofReal (a ^ 2) *
        p4Q2BB_leftColorAllLinkHaarReferenceSum
          H N hN beta hbeta c F := by
  change
    p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c
        (p4Q2BB_swapConcrete H N (fun z => a * F z)) =
      ENNReal.ofReal (a ^ 2) *
        p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c
          (p4Q2BB_swapConcrete H N F)
  have hswap :
      p4Q2BB_swapConcrete H N (fun z => a * F z) =
        (fun z => a * p4Q2BB_swapConcrete H N F z) := by
    rfl
  rw [hswap]
  exact
    p4Q2BH_originalRightColorAllLinkReference_mul
      H N hN beta hbeta c a (p4Q2BB_swapConcrete H N F)

/-- The literal original Wilson mass-weighted per-color all-link average
has exactly the SAME scalar factor on both genuine physical boundaries. -/
theorem p4Q2BI_twelveColorOriginalHaarReferenceAverage_mul
    (c : C12) (a : ℝ) (F : Joint → ℝ) :
    p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c (fun z => a * F z) =
      ENNReal.ofReal (a ^ 2) *
        p4Q2BB_twelveColorOriginalHaarReferenceAverage
          H N hN beta hbeta c F := by
  cases c with
  | inl k =>
      change
        (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
          p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta k
            (fun z => a * F z) =
        ENNReal.ofReal (a ^ 2) *
          ((Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
            p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta k F)
      rw [p4Q2BH_originalRightColorAllLinkReference_mul
        H N hN beta hbeta k a F]
      ac_rfl
  | inr k =>
      change
        (Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
          p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta k
            (fun z => a * F z) =
        ENNReal.ofReal (a ^ 2) *
          ((Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
            p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta k F)
      rw [p4Q2BI_originalLeftColorAllLinkReference_mul
        H N hN beta hbeta k a F]
      ac_rfl

/-- Sum over the fixed twelve physical colors, without link count loss. -/
theorem p4Q2BI_originalTwelveColorReferenceSum_mul
    (a : ℝ) (F : Joint → ℝ) :
    (∑ c : C12,
      p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c (fun z => a * F z)) =
      ENNReal.ofReal (a ^ 2) *
        (∑ c : C12,
          p4Q2BB_twelveColorOriginalHaarReferenceAverage
            H N hN beta hbeta c F) := by
  simp_rw [
    p4Q2BI_twelveColorOriginalHaarReferenceAverage_mul
      H N hN beta hbeta]
  rw [Finset.mul_sum]

/-- The ACTUAL Wilson physical twelve-color Haar reference normalized by
1/12 is quadratically homogeneous for arbitrary concrete F, ENNReal-valued. -/
theorem p4Q2BI_originalPhysicalTwelveColorHaarReference_mul
    (a : ℝ) (F : Joint → ℝ) :
    p4Q2BC_originalPhysicalTwelveColorHaarReference
        H N hN beta hbeta (fun z => a * F z) =
      ENNReal.ofReal (a ^ 2) *
        p4Q2BC_originalPhysicalTwelveColorHaarReference
          H N hN beta hbeta F := by
  unfold p4Q2BC_originalPhysicalTwelveColorHaarReference
  rw [p4Q2BI_originalTwelveColorReferenceSum_mul
    H N hN beta hbeta a F]
  ac_rfl

/-- The concrete ORIGINAL Wilson twelve-color reference is quadratic even
after passing to its real normalized scalar. This uses the exact toReal
multiplication identity, not an unproved reference-frame coercivity. -/
theorem p4Q2BI_originalPhysicalTwelveColorHaarReference_toReal_mul
    (a : ℝ) (F : Joint → ℝ) :
    (p4Q2BC_originalPhysicalTwelveColorHaarReference
        H N hN beta hbeta (fun z => a * F z)).toReal =
      a ^ 2 *
        (p4Q2BC_originalPhysicalTwelveColorHaarReference
          H N hN beta hbeta F).toReal := by
  rw [p4Q2BI_originalPhysicalTwelveColorHaarReference_mul
    H N hN beta hbeta a F, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg a)]

/-- The prior BD unnormalized original Wilson real all-link twelve-color
reference is also exactly quadratic on concrete joint functions. -/
theorem p4Q2BI_originalWilsonTwelveColorHaarReferenceReal_mul
    (a : ℝ) (F : Joint → ℝ) :
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
        H N hN beta hbeta (fun z => a * F z) =
      a ^ 2 *
        p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
          H N hN beta hbeta F := by
  unfold p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
  rw [p4Q2BI_originalTwelveColorReferenceSum_mul
    H N hN beta hbeta a F, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg a)]

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
