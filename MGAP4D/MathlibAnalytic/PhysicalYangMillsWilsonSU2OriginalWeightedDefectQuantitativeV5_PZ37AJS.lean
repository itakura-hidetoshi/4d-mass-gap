import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalIndependentTopResidualDefectV5_PZ37AJR
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJS — original Wilson weighted one-step defect certificate

This append-only leaf combines the already certified AJQ POSITIVE source
reverse-Laplace average and AIG NEGATIVE ORIGINAL physical transfer
average with EXACTLY the same right Wilson halfweight. It does not replace
the centered signed ZW source, crossing kernel, physical measure or transfer.

The resulting real-valued weighted one-step defect integral has an
independent positive, H,beta-dependent lower bound, and a second lower
bound referring to AHN's true identity-centered Haar box.

The new quantity is a WEIGHTED L1 pairing, not yet a lower bound for the
physical Hilbert L2 norm of f0-S f0. A separate norm-duality estimate is
required before it can improve AJR's numerical extra-top residual bound.
No AJA small-budget witness, particular power, transferred excitation,
top rank-one property, uniform coercivity or continuum mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "GAJS" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AJS_group : IsTopologicalGroup GAJS :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AJS_compact : CompactSpace GAJS :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AJS_secondCountable : SecondCountableTopology GAJS :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AJS_measurable : MeasurableSpace GAJS :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AJS_borel : BorelSpace GAJS :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AJS_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "CfgS" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muS" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fS" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fcS" =>
  p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "WS" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "pS" =>
  p4Q2PZ37AFZ_plaquetteCount H
local notation "VS" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "PS" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num)
local notation "TS" => decomposableOneSliceTransferIntegral H 2
local notation "ZS" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "AvgS" => p4Q2PZ37AIF_originalRightWeightedTransferAverage H
local notation "JS" => p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral H

/-- AJQ's genuine positive halfweight source average is at least beta
times AHN's original strictly positive Haar source second moment. -/
theorem p4Q2PZ37AJS_originalWeightedSource_ge_betaVariance
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    beta * VS ≤ JS beta := by
  have hLap :=
    p4Q2PZ37AJQ_originalPositiveSourceLaplace_lower H beta hbeta
  have he : Real.exp (beta * (pS / 2)) *
      Real.exp (-(beta * (pS / 2))) = 1 := by
    rw [← Real.exp_add]
    have hz : beta * (pS / 2) + -(beta * (pS / 2)) = 0 := by ring
    rw [hz, Real.exp_zero]
  calc
    beta * VS =
        Real.exp (beta * (pS / 2)) *
          (beta * Real.exp (-(beta * (pS / 2))) * VS) := by
            calc
              beta * VS =
                  (Real.exp (beta * (pS / 2)) *
                    Real.exp (-(beta * (pS / 2)))) * (beta * VS) := by
                      rw [he, one_mul]
              _ = _ := by ring
    _ ≤ Real.exp (beta * (pS / 2)) *
          p4Q2PZ37AJQ_originalPositiveSourceLaplace H beta :=
        mul_le_mul_of_nonneg_left hLap (Real.exp_pos _).le
    _ = JS beta :=
      (p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral_eq H beta).symm

/-- The ACTUAL weighted one-step original-source minus normalized-transfer
integral, with the true source continuous Haar representative and actual
one-slab transfer integral. Neither is an arbitrary test surrogate. -/
def p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral
    (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  ∫ B : CfgS,
    Real.exp ((beta / 2) * WS B) *
      (fcS B - ‖PS beta hbeta‖⁻¹ * TS beta fS B) ∂muS

/-- The genuine weighted defect integral equals the AJQ positive source
average minus the AIF original transfer average divided by the ORIGINAL
positive physical operator norm. -/
theorem p4Q2PZ37AJS_originalWeightedDefect_eq_averageDifference
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral H beta hbeta =
      JS beta - ‖PS beta hbeta‖⁻¹ * AvgS beta := by
  have hw : Continuous (fun B : CfgS =>
      Real.exp ((beta / 2) * WS B)) :=
    Real.continuous_exp.comp
      (continuous_const.mul
        (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2))
  have hf : Continuous (fun B : CfgS => fcS B) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hJ : Integrable (fun B : CfgS =>
      Real.exp ((beta / 2) * WS B) * fcS B) muS :=
    (hw.mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAvg : Integrable (fun B : CfgS =>
      Real.exp ((beta / 2) * WS B) * TS beta fS B) muS :=
    p4Q2PZ37AIF_originalRightWeightedTransfer_integrable H beta
  unfold p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral
  calc
    (∫ B : CfgS,
      Real.exp ((beta / 2) * WS B) *
        (fcS B - ‖PS beta hbeta‖⁻¹ * TS beta fS B) ∂muS) =
        ∫ B : CfgS,
          Real.exp ((beta / 2) * WS B) * fcS B -
            ‖PS beta hbeta‖⁻¹ *
              (Real.exp ((beta / 2) * WS B) * TS beta fS B) ∂muS := by
          apply integral_congr_ae
          filter_upwards with B
          ring
    _ = (∫ B : CfgS, Real.exp ((beta / 2) * WS B) * fcS B ∂muS) -
          ‖PS beta hbeta‖⁻¹ *
            (∫ B : CfgS,
              Real.exp ((beta / 2) * WS B) * TS beta fS B ∂muS) := by
          rw [integral_sub hJ (hAvg.const_mul _), integral_const_mul]
    _ = JS beta - ‖PS beta hbeta‖⁻¹ * AvgS beta := rfl

/-- Exact AJS two-sided sign certificate: the true Wilson weighted
source/normalized-transfer defect is bounded below by a strictly positive
source variance term PLUS a second negative-transfer contribution.
Every right-hand quantity is from the original SU(2) Haar construction. -/
theorem p4Q2PZ37AJS_originalWeightedDefect_ge_explicitTwoSide
    (beta : ℝ) (hbeta : 0 < beta) :
    beta * VS +
      ‖PS beta hbeta.le‖⁻¹ *
        (beta * ZS beta * Real.exp (-(beta * pS)) * VS) ≤
      p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral H beta hbeta.le := by
  let P := PS beta hbeta.le
  have hSource :
      beta * VS ≤ JS beta :=
    p4Q2PZ37AJS_originalWeightedSource_ge_betaVariance H beta hbeta.le
  have hTransfer :
      AvgS beta ≤ -(beta * ZS beta * Real.exp (-(beta * pS)) * VS) :=
    p4Q2PZ37AIG_originalRightWeightedTransferAverage_le_negativeVariance
      H beta hbeta.le
  have hInv : 0 ≤ ‖P‖⁻¹ := inv_nonneg.mpr (norm_nonneg P)
  have hTransfer' :
      ‖P‖⁻¹ * AvgS beta ≤
        -(‖P‖⁻¹ * (beta * ZS beta * Real.exp (-(beta * pS)) * VS)) := by
    calc
      ‖P‖⁻¹ * AvgS beta ≤
          ‖P‖⁻¹ * (-(beta * ZS beta * Real.exp (-(beta * pS)) * VS)) :=
        mul_le_mul_of_nonneg_left hTransfer hInv
      _ = _ := by ring
  have hExact :=
    p4Q2PZ37AJS_originalWeightedDefect_eq_averageDifference
      H beta hbeta.le
  change
    p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral H beta hbeta.le =
      JS beta - ‖P‖⁻¹ * AvgS beta at hExact
  change
    beta * VS + ‖P‖⁻¹ *
      (beta * ZS beta * Real.exp (-(beta * pS)) * VS) ≤
      p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral H beta hbeta.le
  linarith only [hSource, hTransfer', hExact]

/-- Positive for each finite H and beta>0 WITHOUT an assumed AJA
finite-power witness or an assumed strict top residual estimate. -/
theorem p4Q2PZ37AJS_originalWeightedDefect_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral H beta hbeta.le := by
  let P := PS beta hbeta.le
  have hV : 0 < VS :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hZ : 0 < ZS beta :=
    p4Q2PZ37AIF_originalCrossingPartition_pos H beta
  have hP : 0 ≤ ‖P‖⁻¹ := inv_nonneg.mpr (norm_nonneg P)
  have hTerm :
      0 ≤ ‖P‖⁻¹ *
        (beta * ZS beta * Real.exp (-(beta * pS)) * VS) :=
    mul_nonneg hP
      (mul_pos (mul_pos (mul_pos hbeta hZ) (Real.exp_pos _)) hV).le
  have hBudget :=
    p4Q2PZ37AJS_originalWeightedDefect_ge_explicitTwoSide H beta hbeta
  change
    beta * VS + ‖P‖⁻¹ *
      (beta * ZS beta * Real.exp (-(beta * pS)) * VS) ≤
      p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral H beta hbeta.le
      at hBudget
  have hBetaV : 0 < beta * VS := mul_pos hbeta hV
  linarith only [hBudget, hTerm, hBetaV]

/-- AJS geometric lower estimate uses AHN's exact 1/96 identity-centered
Haar-box proof; the unevaluated genuine SU(2) sphere-radius fraction is
retained and is NOT replaced by a guessed decimal mass. -/
theorem p4Q2PZ37AJS_originalWeightedDefect_ge_identityBox
    (beta : ℝ) (hbeta : 0 < beta) :
    beta *
        ((3 * pS / 8) ^ 2 *
          p4Q2PZ37ADQ_sphereRadiusFraction (1 / 96) ^
            Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
      p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral H beta hbeta.le := by
  let P := PS beta hbeta.le
  have hFloor := p4Q2PZ37AHN_originalSource_HaarSecondMoment_explicitFloor H
  have hScaled :
      beta *
          ((3 * pS / 8) ^ 2 *
            p4Q2PZ37ADQ_sphereRadiusFraction (1 / 96) ^
              Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)) ≤
        beta * VS :=
    mul_le_mul_of_nonneg_left hFloor hbeta.le
  have hV : 0 < VS :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hZ : 0 < ZS beta :=
    p4Q2PZ37AIF_originalCrossingPartition_pos H beta
  have hP : 0 ≤ ‖P‖⁻¹ := inv_nonneg.mpr (norm_nonneg P)
  have hTerm :
      0 ≤ ‖P‖⁻¹ *
        (beta * ZS beta * Real.exp (-(beta * pS)) * VS) :=
    mul_nonneg hP
      (mul_pos (mul_pos (mul_pos hbeta hZ) (Real.exp_pos _)) hV).le
  have hBudget :=
    p4Q2PZ37AJS_originalWeightedDefect_ge_explicitTwoSide H beta hbeta
  change
    beta * VS + ‖P‖⁻¹ *
      (beta * ZS beta * Real.exp (-(beta * pS)) * VS) ≤
      p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral H beta hbeta.le
      at hBudget
  linarith only [hScaled, hTerm, hBudget]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Six candidate declarations, pending exact-source kernel CI and axiom audit. -/
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJS_originalWeightedSource_ge_betaVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJS_originalWeightedOneStepDefectIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJS_originalWeightedDefect_eq_averageDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJS_originalWeightedDefect_ge_explicitTwoSide
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJS_originalWeightedDefect_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJS_originalWeightedDefect_ge_identityBox
