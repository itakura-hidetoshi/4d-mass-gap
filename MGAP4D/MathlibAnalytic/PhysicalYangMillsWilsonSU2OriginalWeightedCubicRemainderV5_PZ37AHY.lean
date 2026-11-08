import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSecondOrderTaylorTransferV5_PZ37AHX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHY — weighted cubic remainder for the ORIGINAL full transfer

Keep the complete Wilson action S, both spatial halfweights, the original ZW
signed source f, the original product Haar, and AHX's actual remainder R3.
The original global action budget is C_H=4*p_H. Retaining the right boundary
gives S(A,B)<=C_B=3*p_H+W(B)/2<=C_H.

For f_+=(|f|+f)/2 and f_-=(|f|-f)/2, define genuine correlations
J_+(B)=integral f_+(A)*S(A,B)^3 and J_-(B)=integral f_-(A)*S(A,B)^3.
The quadratic kernel error is nonpositive. Consequently, for beta>=0,

  -(beta^3/6)*J_+(B) <= R3(beta,B) <= (beta^3/6)*J_-(B).

The unchanged source has Haar mean zero, so BOTH source-part Haar masses
equal Msrc/2. Each J_+ and J_- is bounded by C_B^3*Msrc/2. Thus

  |R3(beta,B)| <= ((beta*C_B)^3/12)*Msrc <= AHX.E3(beta)/2.

The absolute-source correlation integral |f|*S^3 is also retained explicitly.
No equality J_+=J_- or vanishing of integral f*S^3 is assumed.
The original transfer and its exact quadratic center remain unchanged.
Sign criteria are conditional, including at the original fixed coupling.
No fixed-beta sign shell, volume-uniform coercivity or spectral gap is claimed.
All previous files, definitions, typed histories, pins and roots are preserved.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A nonpositive error couples differently to the two parts of a signed
source. No sign assumption is imposed on the source itself. -/
theorem p4Q2PZ37AHY_real_signedNonpositiveError_interval
    (f r d : ℝ) (hr : -d ≤ r ∧ r ≤ 0) :
    -((|f| + f) / 2) * d ≤ f * r ∧
      f * r ≤ ((|f| - f) / 2) * d := by
  rcases le_total 0 f with hf | hf
  · rw [abs_of_nonneg hf]
    constructor
    · have h := mul_le_mul_of_nonneg_left hr.1 hf
      nlinarith only [h]
    · have h := mul_nonpos_of_nonneg_of_nonpos hf hr.2
      nlinarith only [h]
  · rw [abs_of_nonpos hf]
    constructor
    · have h := mul_nonneg_of_nonpos_of_nonpos hf hr.2
      nlinarith only [h]
    · have h := mul_le_mul_of_nonpos_left hr.1 hf
      nlinarith only [h]

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHY_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHY_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHY_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHY_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHY_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Cross" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "Cslab" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "Q" => p4Q2PZ37AHX_originalQuadraticApproximation H
local notation "R3" => p4Q2PZ37AHX_originalThirdOrderRemainder H
local notation "E3" => p4Q2PZ37AHX_originalCubicBudget H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AHY_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- AHQ's exact link/plaquette count evaluates the existing global budget. -/
theorem p4Q2PZ37AHY_originalGlobalActionBudget_eq_fourCount :
    Cslab = 4 * pH := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume
  rw [Nat.cast_add, p4Q2PZ37AHQ_crossingLinkCount_exact H]
  change 2 * (pH + pH) = 4 * pH
  ring

/-- Original right-boundary halfweight retained in a genuine action upper
bound. This is an upper bound, not a claim of an attained exact supremum. -/
def p4Q2PZ37AHY_originalBoundaryActionBudget (B : Cfg) : ℝ :=
  3 * pH + W B / 2

local notation "CB" => p4Q2PZ37AHY_originalBoundaryActionBudget H

theorem p4Q2PZ37AHY_originalBoundaryActionBudget_eq_globalCorrection
    (B : Cfg) : CB B = Cslab - pH + W B / 2 := by
  rw [p4Q2PZ37AHY_originalGlobalActionBudget_eq_fourCount H]
  unfold p4Q2PZ37AHY_originalBoundaryActionBudget
  ring

theorem p4Q2PZ37AHY_originalFullAction_le_boundaryBudget
    (A B : Cfg) : S A B ≤ CB B := by
  have hA : W A ≤ 2 * pH :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
      H 2 (by norm_num) A
  have hCross : Cross A B ≤ 2 * pH :=
    p4Q2PZ37AHQ_originalCrossing_le_twoCount H A B
  change (1 / 2 : ℝ) * W A + Cross A B + (1 / 2 : ℝ) * W B ≤
    3 * pH + W B / 2
  linarith only [hA, hCross]

theorem p4Q2PZ37AHY_originalBoundaryActionBudget_nonneg
    (B : Cfg) : 0 ≤ CB B :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
    H 2 (by norm_num) B B).trans
      (p4Q2PZ37AHY_originalFullAction_le_boundaryBudget H B B)

theorem p4Q2PZ37AHY_originalBoundaryActionBudget_le_global
    (B : Cfg) : CB B ≤ Cslab := by
  have hB : W B ≤ 2 * pH :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
      H 2 (by norm_num) B
  rw [p4Q2PZ37AHY_originalGlobalActionBudget_eq_fourCount H]
  unfold p4Q2PZ37AHY_originalBoundaryActionBudget
  linarith only [hB]

/-- The positive part is used only to bound an error against the SAME
original signed source; it does not replace the source of the transfer. -/
def p4Q2PZ37AHY_originalSourcePositivePart (A : Cfg) : ℝ :=
  (|fCont A| + fCont A) / 2

/-- The magnitude of the negative part of the original centered source. -/
def p4Q2PZ37AHY_originalSourceNegativePart (A : Cfg) : ℝ :=
  (|fCont A| - fCont A) / 2

local notation "fp" => p4Q2PZ37AHY_originalSourcePositivePart H
local notation "fm" => p4Q2PZ37AHY_originalSourceNegativePart H

theorem p4Q2PZ37AHY_originalSourceParts_continuous :
    Continuous fp ∧ Continuous fm := by
  have hf : Continuous (fun A : Cfg => fCont A) := (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  exact ⟨(hf.abs.add hf).div_const 2, (hf.abs.sub hf).div_const 2⟩

theorem p4Q2PZ37AHY_originalSourceParts_nonneg (A : Cfg) :
    0 ≤ fp A ∧ 0 ≤ fm A := by
  have h1 := neg_le_abs (fCont A)
  have h2 := le_abs_self (fCont A)
  change 0 ≤ (|fCont A| + fCont A) / 2 ∧
    0 ≤ (|fCont A| - fCont A) / 2
  constructor <;> linarith only [h1, h2]

/-- Genuine Haar centering gives equal UNWEIGHTED source-part masses.
It does not assert equality of their action-weighted cubic moments. -/
theorem p4Q2PZ37AHY_originalSourceParts_HaarMass :
    (∫ A : Cfg, fp A ∂muH) = Msrc / 2 ∧
      (∫ A : Cfg, fm A ∂muH) = Msrc / 2 := by
  have hf := p4Q2PZ37AHP_originalContinuousSource_integrable H
  constructor
  · change (∫ A : Cfg, (|fCont A| + fCont A) / 2 ∂muH) = Msrc / 2
    rw [integral_div, integral_add hf.abs hf,
      ← p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral H,
      p4Q2PZ37AHP_originalSource_mean_zero H]
    ring
  · change (∫ A : Cfg, (|fCont A| - fCont A) / 2 ∂muH) = Msrc / 2
    rw [integral_div, integral_sub hf.abs hf,
      ← p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral H,
      p4Q2PZ37AHP_originalSource_mean_zero H]
    ring

/-- Any continuous original-boundary weight times the full-action cube
is integrable under the unchanged finite product Haar measure. -/
theorem p4Q2PZ37AHY_originalWeightedActionCube_integrable
    (g : Cfg → ℝ) (hg : Continuous g) (B : Cfg) :
    Integrable (fun A : Cfg => g A * (S A B) ^ 3) muH :=
  (hg.mul ((p4Q2PZ37AHP_originalFullAction_continuous H B).pow 3)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Genuine absolute-source/full-action cubic correlation. -/
def p4Q2PZ37AHY_originalAbsoluteActionCubeMoment (B : Cfg) : ℝ :=
  ∫ A : Cfg, |fCont A| * (S A B) ^ 3 ∂muH

/-- Genuine positive-source/full-action cubic correlation. -/
def p4Q2PZ37AHY_originalPositiveActionCubeMoment (B : Cfg) : ℝ :=
  ∫ A : Cfg, fp A * (S A B) ^ 3 ∂muH

/-- Genuine negative-source/full-action cubic correlation. -/
def p4Q2PZ37AHY_originalNegativeActionCubeMoment (B : Cfg) : ℝ :=
  ∫ A : Cfg, fm A * (S A B) ^ 3 ∂muH

local notation "Jabs" => p4Q2PZ37AHY_originalAbsoluteActionCubeMoment H
local notation "Jp" => p4Q2PZ37AHY_originalPositiveActionCubeMoment H
local notation "Jm" => p4Q2PZ37AHY_originalNegativeActionCubeMoment H

theorem p4Q2PZ37AHY_originalActionCubeMoments_nonneg (B : Cfg) :
    0 ≤ Jabs B ∧ 0 ≤ Jp B ∧ 0 ≤ Jm B := by
  have hS (A : Cfg) : 0 ≤ (S A B) ^ 3 :=
    pow_nonneg
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
        H 2 (by norm_num) A B) 3
  refine ⟨?_, ?_, ?_⟩
  · exact integral_nonneg (fun A => mul_nonneg (abs_nonneg _) (hS A))
  · exact integral_nonneg (fun A =>
      mul_nonneg (p4Q2PZ37AHY_originalSourceParts_nonneg H A).1 (hS A))
  · exact integral_nonneg (fun A =>
      mul_nonneg (p4Q2PZ37AHY_originalSourceParts_nonneg H A).2 (hS A))

/-- Absolute weighting is the SUM, not generally twice either signed part. -/
theorem p4Q2PZ37AHY_originalActionCubeMoments_sum (B : Cfg) :
    Jp B + Jm B = Jabs B := by
  obtain ⟨hp, hm⟩ := p4Q2PZ37AHY_originalSourceParts_continuous H
  unfold p4Q2PZ37AHY_originalPositiveActionCubeMoment
    p4Q2PZ37AHY_originalNegativeActionCubeMoment
    p4Q2PZ37AHY_originalAbsoluteActionCubeMoment
  rw [← integral_add
    (p4Q2PZ37AHY_originalWeightedActionCube_integrable H fp hp B)
    (p4Q2PZ37AHY_originalWeightedActionCube_integrable H fm hm B)]
  apply integral_congr_ae
  filter_upwards with A
  change ((|fCont A| + fCont A) / 2) * (S A B) ^ 3 +
    ((|fCont A| - fCont A) / 2) * (S A B) ^ 3 =
      |fCont A| * (S A B) ^ 3
  ring

/-- A continuous nonnegative weight retains the right boundary in the cap. -/
theorem p4Q2PZ37AHY_originalWeightedActionCube_le_boundaryBudget
    (g : Cfg → ℝ) (hg : Continuous g) (hg0 : ∀ A, 0 ≤ g A) (B : Cfg) :
    (∫ A : Cfg, g A * (S A B) ^ 3 ∂muH) ≤
      (CB B) ^ 3 * (∫ A : Cfg, g A ∂muH) := by
  have hgInt : Integrable g muH :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    (∫ A : Cfg, g A * (S A B) ^ 3 ∂muH) ≤
        ∫ A : Cfg, (CB B) ^ 3 * g A ∂muH := by
      apply integral_mono
        (p4Q2PZ37AHY_originalWeightedActionCube_integrable H g hg B)
        (hgInt.const_mul _)
      intro A
      have hPow : (S A B) ^ 3 ≤ (CB B) ^ 3 :=
        pow_le_pow_left₀
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
            H 2 (by norm_num) A B)
          (p4Q2PZ37AHY_originalFullAction_le_boundaryBudget H A B) 3
      calc
        g A * (S A B) ^ 3 ≤ g A * (CB B) ^ 3 :=
          mul_le_mul_of_nonneg_left hPow (hg0 A)
        _ = (CB B) ^ 3 * g A := mul_comm _ _
    _ = (CB B) ^ 3 * (∫ A : Cfg, g A ∂muH) := by
      rw [integral_const_mul]

/-- Each genuine source-part cubic moment uses only half the source L1 mass. -/
theorem p4Q2PZ37AHY_originalSourcePartCubeMoments_le_halfMass
    (B : Cfg) :
    Jp B ≤ (CB B) ^ 3 * (Msrc / 2) ∧
      Jm B ≤ (CB B) ^ 3 * (Msrc / 2) := by
  obtain ⟨hp, hm⟩ := p4Q2PZ37AHY_originalSourceParts_continuous H
  have hP := p4Q2PZ37AHY_originalWeightedActionCube_le_boundaryBudget H fp hp
    (fun A => (p4Q2PZ37AHY_originalSourceParts_nonneg H A).1) B
  have hM := p4Q2PZ37AHY_originalWeightedActionCube_le_boundaryBudget H fm hm
    (fun A => (p4Q2PZ37AHY_originalSourceParts_nonneg H A).2) B
  rw [(p4Q2PZ37AHY_originalSourceParts_HaarMass H).1] at hP
  rw [(p4Q2PZ37AHY_originalSourceParts_HaarMass H).2] at hM
  exact ⟨hP, hM⟩

/-- The absolute weighted moment also has the genuine boundary-dependent cap. -/
theorem p4Q2PZ37AHY_originalAbsoluteActionCubeMoment_le_mass
    (B : Cfg) : Jabs B ≤ (CB B) ^ 3 * Msrc := by
  have h := p4Q2PZ37AHY_originalWeightedActionCube_le_boundaryBudget H
    (fun A : Cfg => |fCont A|) (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.abs (fun A => abs_nonneg _) B
  rw [← p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral H] at h
  exact h

/-- The original quadratic kernel error is NONPOSITIVE, and its lower
bound retains the actual complete action at each pair of boundaries. -/
theorem p4Q2PZ37AHY_originalKernel_secondOrder_signedInterval
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    -((beta * S A B) ^ 3 / 6) ≤
        K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2) ∧
      K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2) ≤ 0 := by
  have hS : 0 ≤ S A B :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) A B
  have h := p4Q2PZ37AHX_exp_neg_cubicRemainder
    (beta * S A B) (mul_nonneg hbeta hS)
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  simp only [neg_mul] at h ⊢
  constructor <;> linarith only [h.1, h.2]

/-- Integrability of AHX's unchanged genuine remainder integrand. -/
theorem p4Q2PZ37AHY_originalThirdOrderRemainder_integrable
    (beta : ℝ) (B : Cfg) :
    Integrable (fun A : Cfg => fCont A *
      (K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2))) muH := by
  simpa only [Pi.sub_apply, mul_sub] using
    (p4Q2PZ37AHP_originalKernelWeightedSource_integrable H beta B).sub
      (p4Q2PZ37AHX_originalQuadraticWeightedSource_integrable H beta B)

/-- Original source/action correlation preserved inside an absolute bound. -/
theorem p4Q2PZ37AHY_originalThirdOrderRemainder_abs_weightedBound
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |R3 beta B| ≤ (beta ^ 3 / 6) * Jabs B := by
  have hError := p4Q2PZ37AHY_originalThirdOrderRemainder_integrable H beta B
  have hAbsError : Integrable (fun A : Cfg => |fCont A *
      (K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2))|) muH := by
    simpa only [Real.norm_eq_abs] using hError.norm
  have hWeighted : Integrable (fun A : Cfg =>
      (beta ^ 3 / 6) * (|fCont A| * (S A B) ^ 3)) muH :=
    (p4Q2PZ37AHY_originalWeightedActionCube_integrable H
      (fun A : Cfg => |fCont A|) (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.abs B).const_mul _
  unfold p4Q2PZ37AHX_originalThirdOrderRemainder
    p4Q2PZ37AHY_originalAbsoluteActionCubeMoment
  calc
    |∫ A : Cfg, fCont A *
        (K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2)) ∂muH| ≤
        ∫ A : Cfg, |fCont A *
          (K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2))| ∂muH :=
      abs_integral_le_integral_abs
    _ ≤ ∫ A : Cfg, (beta ^ 3 / 6) * (|fCont A| * (S A B) ^ 3) ∂muH := by
      apply integral_mono hAbsError hWeighted
      intro A
      rw [abs_mul]
      calc
        |fCont A| *
            |K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2)| ≤
            |fCont A| * ((beta * S A B) ^ 3 / 6) :=
          mul_le_mul_of_nonneg_left
            (p4Q2PZ37AHX_originalKernel_secondOrder_pointwise H beta hbeta A B)
            (abs_nonneg _)
        _ = (beta ^ 3 / 6) * (|fCont A| * (S A B) ^ 3) := by ring
    _ = (beta ^ 3 / 6) * (∫ A : Cfg, |fCont A| * (S A B) ^ 3 ∂muH) := by
      rw [integral_const_mul]

/-- The two different source-part/full-action correlations control the two
different sides of the genuine signed remainder. -/
theorem p4Q2PZ37AHY_originalThirdOrderRemainder_weightedInterval
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    -((beta ^ 3 / 6) * Jp B) ≤ R3 beta B ∧
      R3 beta B ≤ (beta ^ 3 / 6) * Jm B := by
  obtain ⟨hp, hm⟩ := p4Q2PZ37AHY_originalSourceParts_continuous H
  have hpInt := p4Q2PZ37AHY_originalWeightedActionCube_integrable H fp hp B
  have hmInt := p4Q2PZ37AHY_originalWeightedActionCube_integrable H fm hm B
  have hrInt := p4Q2PZ37AHY_originalThirdOrderRemainder_integrable H beta B
  have hPoint (A : Cfg) := p4Q2PZ37AHY_real_signedNonpositiveError_interval
    (fCont A)
    (K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2))
    ((beta * S A B) ^ 3 / 6)
    (p4Q2PZ37AHY_originalKernel_secondOrder_signedInterval H beta hbeta A B)
  constructor
  · calc
      -((beta ^ 3 / 6) * Jp B) =
          ∫ A : Cfg, -(beta ^ 3 / 6) * (fp A * (S A B) ^ 3) ∂muH := by
        rw [integral_const_mul]
        unfold p4Q2PZ37AHY_originalPositiveActionCubeMoment
        ring
      _ ≤ R3 beta B := by
        unfold p4Q2PZ37AHX_originalThirdOrderRemainder
        apply integral_mono (hpInt.const_mul _) hrInt
        intro A
        calc
          -(beta ^ 3 / 6) * (fp A * (S A B) ^ 3) =
              -((|fCont A| + fCont A) / 2) * ((beta * S A B) ^ 3 / 6) := by
            unfold p4Q2PZ37AHY_originalSourcePositivePart
            ring
          _ ≤ fCont A *
              (K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2)) :=
            (hPoint A).1
  · calc
      R3 beta B ≤
          ∫ A : Cfg, (beta ^ 3 / 6) * (fm A * (S A B) ^ 3) ∂muH := by
        unfold p4Q2PZ37AHX_originalThirdOrderRemainder
        apply integral_mono hrInt (hmInt.const_mul _)
        intro A
        calc
          fCont A *
              (K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2)) ≤
              ((|fCont A| - fCont A) / 2) * ((beta * S A B) ^ 3 / 6) :=
            (hPoint A).2
          _ = (beta ^ 3 / 6) * (fm A * (S A B) ^ 3) := by
            unfold p4Q2PZ37AHY_originalSourceNegativePart
            ring
      _ = (beta ^ 3 / 6) * Jm B := integral_const_mul _ _

/-- The mean-zero source and nonpositive kernel error halve the cubic mass
factor; the right-boundary improvement remains in the same bound. -/
def p4Q2PZ37AHY_originalBoundaryHalfCubicBudget (beta : ℝ) (B : Cfg) : ℝ :=
  ((beta * CB B) ^ 3 / 12) * Msrc

local notation "EB" => p4Q2PZ37AHY_originalBoundaryHalfCubicBudget H

theorem p4Q2PZ37AHY_originalBoundaryHalfCubicBudget_nonneg
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) : 0 ≤ EB beta B := by
  exact mul_nonneg
    (div_nonneg (pow_nonneg
      (mul_nonneg hbeta (p4Q2PZ37AHY_originalBoundaryActionBudget_nonneg H B)) 3)
      (by norm_num))
    (p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg H)

theorem p4Q2PZ37AHY_originalBoundaryHalfCubicBudget_zero
    (B : Cfg) : EB 0 B = 0 := by
  simp [p4Q2PZ37AHY_originalBoundaryHalfCubicBudget]

/-- This improvement is no larger than HALF of AHX's previous width,
for every original right boundary and every nonnegative beta. -/
theorem p4Q2PZ37AHY_originalBoundaryHalfCubicBudget_le_halfAHX
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    EB beta B ≤ E3 beta / 2 := by
  have hPow : (beta * CB B) ^ 3 ≤ (beta * Cslab) ^ 3 :=
    pow_le_pow_left₀
      (mul_nonneg hbeta (p4Q2PZ37AHY_originalBoundaryActionBudget_nonneg H B))
      (mul_le_mul_of_nonneg_left
        (p4Q2PZ37AHY_originalBoundaryActionBudget_le_global H B) hbeta) 3
  calc
    EB beta B ≤ ((beta * Cslab) ^ 3 / 12) * Msrc :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hPow (by norm_num))
        (p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg H)
    _ = E3 beta / 2 := by
      unfold p4Q2PZ37AHX_originalCubicBudget
      ring

/-- Two independently controlled source parts yield the improved actual
remainder bound. No equality of their weighted moments is used. -/
theorem p4Q2PZ37AHY_originalThirdOrderRemainder_abs_boundaryHalfBound
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |R3 beta B| ≤ EB beta B := by
  have h := p4Q2PZ37AHY_originalThirdOrderRemainder_weightedInterval H beta hbeta B
  have hParts := p4Q2PZ37AHY_originalSourcePartCubeMoments_le_halfMass H B
  have hc : 0 ≤ beta ^ 3 / 6 :=
    div_nonneg (pow_nonneg hbeta 3) (by norm_num)
  have hP : (beta ^ 3 / 6) * Jp B ≤ EB beta B := by
    calc
      (beta ^ 3 / 6) * Jp B ≤ (beta ^ 3 / 6) * ((CB B) ^ 3 * (Msrc / 2)) :=
        mul_le_mul_of_nonneg_left hParts.1 hc
      _ = EB beta B := by
        unfold p4Q2PZ37AHY_originalBoundaryHalfCubicBudget
        ring
  have hM : (beta ^ 3 / 6) * Jm B ≤ EB beta B := by
    calc
      (beta ^ 3 / 6) * Jm B ≤ (beta ^ 3 / 6) * ((CB B) ^ 3 * (Msrc / 2)) :=
        mul_le_mul_of_nonneg_left hParts.2 hc
      _ = EB beta B := by
        unfold p4Q2PZ37AHY_originalBoundaryHalfCubicBudget
        ring
  exact abs_le.mpr ⟨by linarith only [h.1, hP], h.2.trans hM⟩

theorem p4Q2PZ37AHY_originalThirdOrderRemainder_abs_halfAHX
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |R3 beta B| ≤ E3 beta / 2 :=
  (p4Q2PZ37AHY_originalThirdOrderRemainder_abs_boundaryHalfBound H beta hbeta B).trans
    (p4Q2PZ37AHY_originalBoundaryHalfCubicBudget_le_halfAHX H beta hbeta B)

/-- A count-only corollary retains the original right-boundary cap. -/
theorem p4Q2PZ37AHY_originalThirdOrderRemainder_abs_halfCount
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |R3 beta B| ≤ ((beta * CB B) ^ 3 / 24) * pH := by
  have hCoef : 0 ≤ (beta * CB B) ^ 3 / 12 :=
    div_nonneg (pow_nonneg
      (mul_nonneg hbeta (p4Q2PZ37AHY_originalBoundaryActionBudget_nonneg H B)) 3)
      (by norm_num)
  calc
    |R3 beta B| ≤ EB beta B :=
      p4Q2PZ37AHY_originalThirdOrderRemainder_abs_boundaryHalfBound H beta hbeta B
    _ ≤ ((beta * CB B) ^ 3 / 12) * (pH / 2) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AHJ_originalCenteredSource_L1_le_halfCount H) hCoef
    _ = ((beta * CB B) ^ 3 / 24) * pH := by ring

/-- Asymmetric enclosure retains the two actual cubic correlations around
AHX's exactly evaluated quadratic center for the unchanged transfer. -/
theorem p4Q2PZ37AHY_originalTransfer_weightedCubicInterval
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Q beta B - (beta ^ 3 / 6) * Jp B ≤ T beta f0 B ∧
      T beta f0 B ≤ Q beta B + (beta ^ 3 / 6) * Jm B := by
  have h := p4Q2PZ37AHY_originalThirdOrderRemainder_weightedInterval H beta hbeta B
  rw [p4Q2PZ37AHX_originalThirdOrderRemainder_eq_sub H beta B] at h
  constructor <;> linarith only [h.1, h.2]

/-- Symmetric enclosure with the mean-zero and right-boundary improvements. -/
theorem p4Q2PZ37AHY_originalTransfer_boundaryHalfCubicInterval
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Q beta B - EB beta B ≤ T beta f0 B ∧
      T beta f0 B ≤ Q beta B + EB beta B := by
  have h := abs_le.mp
    (p4Q2PZ37AHY_originalThirdOrderRemainder_abs_boundaryHalfBound H beta hbeta B)
  rw [p4Q2PZ37AHX_originalThirdOrderRemainder_eq_sub H beta B] at h
  constructor <;> linarith only [h.1, h.2]

/-- A negative transfer certificate uses J_- because only the negative
source part can produce a positive contribution to the kernel error. -/
theorem p4Q2PZ37AHY_originalTransfer_negative_of_weightedCubicMargin
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg)
    (hMargin : (beta ^ 2 / 2) * ((3 * pH + W B) * Vsrc) +
      (beta ^ 3 / 6) * Jm B < beta * Vsrc) :
    T beta f0 B < 0 := by
  have h := (p4Q2PZ37AHY_originalTransfer_weightedCubicInterval H beta hbeta B).2
  unfold p4Q2PZ37AHX_originalQuadraticApproximation at h
  linarith only [h, hMargin]

/-- The positive branch instead needs the actual positive-source cubic
correlation; its margin is not presumed satisfied at the fixed coupling. -/
theorem p4Q2PZ37AHY_originalTransfer_positive_of_weightedCubicMargin
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg)
    (hMargin : beta * Vsrc + (beta ^ 3 / 6) * Jp B <
      (beta ^ 2 / 2) * ((3 * pH + W B) * Vsrc)) :
    0 < T beta f0 B := by
  have h := (p4Q2PZ37AHY_originalTransfer_weightedCubicInterval H beta hbeta B).1
  unfold p4Q2PZ37AHX_originalQuadraticApproximation at h
  linarith only [h, hMargin]

/-- The improved interval holds at the ORIGINAL fixed coupling without
a smallness hypothesis; it alone does not settle either strict sign. -/
theorem p4Q2PZ37AHY_originalFixedTransfer_boundaryHalfCubicInterval
    (B : Cfg) :
    Q beta0 B - EB beta0 B ≤ T beta0 f0 B ∧
      T beta0 f0 B ≤ Q beta0 B + EB beta0 B :=
  p4Q2PZ37AHY_originalTransfer_boundaryHalfCubicInterval
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le B

theorem p4Q2PZ37AHY_originalFixedTransfer_negative_of_weightedCubicMargin
    (B : Cfg)
    (hMargin : (beta0 ^ 2 / 2) * ((3 * pH + W B) * Vsrc) +
      (beta0 ^ 3 / 6) * Jm B < beta0 * Vsrc) :
    T beta0 f0 B < 0 :=
  p4Q2PZ37AHY_originalTransfer_negative_of_weightedCubicMargin
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le B hMargin

theorem p4Q2PZ37AHY_originalFixedTransfer_positive_of_weightedCubicMargin
    (B : Cfg)
    (hMargin : beta0 * Vsrc + (beta0 ^ 3 / 6) * Jp B <
      (beta0 ^ 2 / 2) * ((3 * pH + W B) * Vsrc)) :
    0 < T beta0 f0 B :=
  p4Q2PZ37AHY_originalTransfer_positive_of_weightedCubicMargin
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le B hMargin

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHY_real_signedNonpositiveError_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalGlobalActionBudget_eq_fourCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalBoundaryActionBudget_eq_globalCorrection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalFullAction_le_boundaryBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalBoundaryActionBudget_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalBoundaryActionBudget_le_global
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalSourceParts_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalSourceParts_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalSourceParts_HaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalWeightedActionCube_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalActionCubeMoments_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalActionCubeMoments_sum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalWeightedActionCube_le_boundaryBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalSourcePartCubeMoments_le_halfMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalAbsoluteActionCubeMoment_le_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalKernel_secondOrder_signedInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalThirdOrderRemainder_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalThirdOrderRemainder_abs_weightedBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalThirdOrderRemainder_weightedInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalBoundaryHalfCubicBudget_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalBoundaryHalfCubicBudget_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalBoundaryHalfCubicBudget_le_halfAHX
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalThirdOrderRemainder_abs_boundaryHalfBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalThirdOrderRemainder_abs_halfAHX
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalThirdOrderRemainder_abs_halfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalTransfer_weightedCubicInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalTransfer_boundaryHalfCubicInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalTransfer_negative_of_weightedCubicMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalTransfer_positive_of_weightedCubicMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalFixedTransfer_boundaryHalfCubicInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalFixedTransfer_negative_of_weightedCubicMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHY_originalFixedTransfer_positive_of_weightedCubicMargin

