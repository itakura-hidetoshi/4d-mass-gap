import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalEvenTorusCenterSourceOddV5_PZ37AHW2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHX — second-order Taylor control of the ORIGINAL full transfer

Keep the original complete one-slab Wilson action, both spatial halfweights,
the original centered ZW physical source and the original spatial product Haar.
AHR and AHW give the exact first and second source-weighted action moments.
The quadratic approximation to the actual signed physical transfer is

  Q_beta(B) = -beta*V_H + (beta^2/2)*(3*p_H+W_H(B))*V_H.

The remainder below is the genuine signed Haar integral of the difference
between the original Boltzmann kernel and its quadratic polynomial.
For every beta >= 0, a global scalar derivative comparison gives

  |T_beta(B)-Q_beta(B)| <= ((beta*C_H)^3/6)*Msrc_H,

using the previously proved original action budget C_H and source Haar L1
mass. No beta*C_H <= 1 assumption or exponential loss is introduced.
Both strict-sign certificates remain CONDITIONAL on a quantitative margin,
including their specialization to the original fixed beta0.
No fixed-beta sign shell, H-uniform coercivity or spectral gap is asserted.
All existing physical definitions, files, pins, roots and workflows are kept.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The genuine scalar quadratic Taylor polynomial exceeds exp(-x),
and its error is at most x^3/6 on the entire nonnegative half-line. -/
theorem p4Q2PZ37AHX_exp_neg_cubicRemainder
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 1 - x + x ^ 2 / 2 - Real.exp (-x) ∧
      1 - x + x ^ 2 / 2 - Real.exp (-x) ≤ x ^ 3 / 6 := by
  have hLow : 0 ≤ 1 - x + x ^ 2 / 2 - Real.exp (-x) := by
    have h := (p4Q2PZ37AHP_exp_neg_quadraticRemainder x hx).2
    linarith only [h]
  have hDeriv (t : ℝ) :
      HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2 - Real.exp (-y))
        (Real.exp (-t) - 1 + t) t := by
    convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
      (((hasDerivAt_id t).pow 2).div_const (2 : ℝ))).sub
        ((hasDerivAt_id t).neg.exp) using 1
    simp
    ring
  have hPoly (t : ℝ) :
      HasDerivAt (fun y : ℝ => y ^ 3 / 6) (t ^ 2 / 2) t := by
    convert ((hasDerivAt_id t).pow 3).div_const (6 : ℝ) using 1
    simp
    ring
  have hCont : Continuous
      (fun y : ℝ => 1 - y + y ^ 2 / 2 - Real.exp (-y)) := by
    fun_prop
  have hUpper : 1 - x + x ^ 2 / 2 - Real.exp (-x) ≤ x ^ 3 / 6 := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (a := (0 : ℝ)) (b := x)
      (B := fun y : ℝ => y ^ 3 / 6) (B' := fun y : ℝ => y ^ 2 / 2)
      hCont.continuousOn
      (fun t _ => (hDeriv t).hasDerivWithinAt)
      (by norm_num)
      (by fun_prop)
      (fun t _ => (hPoly t).hasDerivWithinAt)
      (fun t ht => ?_)
      ⟨hx, le_rfl⟩
    exact (p4Q2PZ37AHP_exp_neg_quadraticRemainder t ht.1).2
  exact ⟨hLow, hUpper⟩

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHX_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHX_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHX_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHX_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHX_borel : BorelSpace G :=
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
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "M2" => p4Q2PZ37AHS_originalSecondFullActionHaarMoment H
local notation "Cslab" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AHX_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The exact original second-order polynomial after Haar integration.
The boundary Wilson term and both original halfweights are retained. -/
def p4Q2PZ37AHX_originalQuadraticApproximation (beta : ℝ) (B : Cfg) : ℝ :=
  -(beta * Vsrc) + (beta ^ 2 / 2) * ((3 * pH + W B) * Vsrc)

local notation "Q" => p4Q2PZ37AHX_originalQuadraticApproximation H

/-- Actual original kernel error, with the full action still inside
the cubic upper bound, valid at all nonnegative couplings. -/
theorem p4Q2PZ37AHX_originalKernel_secondOrder_pointwise
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    |K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2)| ≤
      (beta * S A B) ^ 3 / 6 := by
  have hS : 0 ≤ S A B :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) A B
  obtain ⟨hLo, hHi⟩ :=
    p4Q2PZ37AHX_exp_neg_cubicRemainder (beta * S A B) (mul_nonneg hbeta hS)
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  have hEq :
      Real.exp (-beta * S A B) -
          (1 - beta * S A B + (beta * S A B) ^ 2 / 2) =
        -(1 - beta * S A B + (beta * S A B) ^ 2 / 2 -
          Real.exp (-(beta * S A B))) := by
    rw [neg_mul]
    ring
  rw [hEq, abs_neg, abs_of_nonneg hLo]
  exact hHi

/-- The pre-existing genuine slab-action budget makes the cubic
kernel bound uniform in both original boundaries. -/
theorem p4Q2PZ37AHX_originalKernel_secondOrder_bound
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    |K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2)| ≤
      (beta * Cslab) ^ 3 / 6 := by
  have hS : 0 ≤ S A B :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) A B
  have hCap : S A B ≤ Cslab :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H 2 (by norm_num) A B
  have hPow : (beta * S A B) ^ 3 ≤ (beta * Cslab) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg hbeta hS)
      (mul_le_mul_of_nonneg_left hCap hbeta) 3
  exact (p4Q2PZ37AHX_originalKernel_secondOrder_pointwise H beta hbeta A B).trans
    (div_le_div_of_nonneg_right hPow (by norm_num))

/-- The quadratic full-action integrand is integrable under the
same original product Haar, including arbitrary real beta. -/
theorem p4Q2PZ37AHX_originalQuadraticWeightedSource_integrable
    (beta : ℝ) (B : Cfg) :
    Integrable (fun A : Cfg =>
      fCont A * (1 - beta * S A B + (beta * S A B) ^ 2 / 2)) muH := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hS : Continuous (fun A : Cfg => S A B) :=
    p4Q2PZ37AHP_originalFullAction_continuous H B
  have hPoly : Continuous
      (fun A : Cfg => 1 - beta * S A B + (beta * S A B) ^ 2 / 2) :=
    (continuous_const.sub (continuous_const.mul hS)).add
      (((continuous_const.mul hS).pow 2).div_const 2)
  exact (hf.mul hPoly).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Integrate the real quadratic full-action polynomial first,
then substitute AHR's first moment and AHW's exact second moment. -/
theorem p4Q2PZ37AHX_originalQuadraticHaar_exact
    (beta : ℝ) (B : Cfg) :
    (∫ A : Cfg,
      fCont A * (1 - beta * S A B + (beta * S A B) ^ 2 / 2) ∂muH) =
      Q beta B := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hS : Continuous (fun A : Cfg => S A B) :=
    p4Q2PZ37AHP_originalFullAction_continuous H B
  have hSq : Integrable (fun A : Cfg => fCont A * (S A B) ^ 2) muH :=
    (hf.mul (hS.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLin := p4Q2PZ37AHP_originalLinearizedWeightedSource_integrable H beta B
  calc
    (∫ A : Cfg,
        fCont A * (1 - beta * S A B + (beta * S A B) ^ 2 / 2) ∂muH) =
        ∫ A : Cfg, fCont A * (1 - beta * S A B) +
          (beta ^ 2 / 2) * (fCont A * (S A B) ^ 2) ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      ring
    _ = (∫ A : Cfg, fCont A * (1 - beta * S A B) ∂muH) +
        (beta ^ 2 / 2) * (∫ A : Cfg, fCont A * (S A B) ^ 2 ∂muH) := by
      rw [integral_add hLin (hSq.const_mul (beta ^ 2 / 2)), integral_const_mul]
    _ = -(beta * Vsrc) + (beta ^ 2 / 2) * M2 B := by
      rw [p4Q2PZ37AHP_originalLinearizedHaar_eq_negFirstMoment H beta B,
        p4Q2PZ37AHR_originalFirstActionMoment_eq_variance H B]
      rfl
    _ = Q beta B := by
      rw [p4Q2PZ37AHW2_originalSecondFullActionMoment_exact H B]
      rfl

/-- The original source Haar L1 mass multiplies the genuine global
third-order kernel remainder. -/
def p4Q2PZ37AHX_originalCubicBudget (beta : ℝ) : ℝ :=
  ((beta * Cslab) ^ 3 / 6) * Msrc

local notation "E3" => p4Q2PZ37AHX_originalCubicBudget H

theorem p4Q2PZ37AHX_originalCubicBudget_nonneg
    (beta : ℝ) (hbeta : 0 ≤ beta) : 0 ≤ E3 beta := by
  have hC : 0 ≤ Cslab :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  exact mul_nonneg
    (div_nonneg (pow_nonneg (mul_nonneg hbeta hC) 3) (by norm_num))
    (p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg H)

theorem p4Q2PZ37AHX_originalCubicBudget_zero : E3 0 = 0 := by
  simp [p4Q2PZ37AHX_originalCubicBudget]

/-- Exact relation between the OLD error width and the NEW cubic
error width. Their approximation centers are different. -/
theorem p4Q2PZ37AHX_originalCubicBudget_eq_scaledQuadratic
    (beta : ℝ) :
    E3 beta = (beta * Cslab / 3) *
      p4Q2PZ37AHP_originalQuadraticBudget H beta := by
  unfold p4Q2PZ37AHX_originalCubicBudget p4Q2PZ37AHP_originalQuadraticBudget
  ring

/-- True signed Haar variation, preserving the signed source while
using its absolute Haar mass only to control the error. -/
theorem p4Q2PZ37AHX_originalSignedTaylorHaarError
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |(∫ A : Cfg, fCont A * K beta A B ∂muH) -
      (∫ A : Cfg,
        fCont A * (1 - beta * S A B + (beta * S A B) ^ 2 / 2) ∂muH)| ≤
      E3 beta := by
  have h := p4Q2PZ37AEV_real_signedWeightedIntegral_absVariation
    muH (fun A : Cfg => fCont A) (fun A : Cfg => K beta A B)
    (fun A : Cfg => 1 - beta * S A B + (beta * S A B) ^ 2 / 2)
    ((beta * Cslab) ^ 3 / 6)
    (p4Q2PZ37AHP_originalContinuousSource_integrable H)
    (p4Q2PZ37AHP_originalKernelWeightedSource_integrable H beta B)
    (p4Q2PZ37AHX_originalQuadraticWeightedSource_integrable H beta B)
    (fun A => p4Q2PZ37AHX_originalKernel_secondOrder_bound H beta hbeta A B)
  rw [← p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral H] at h
  exact h

/-- The remainder is an ACTUAL integral of the original Boltzmann
kernel error against the unchanged signed continuous physical source. -/
def p4Q2PZ37AHX_originalThirdOrderRemainder (beta : ℝ) (B : Cfg) : ℝ :=
  ∫ A : Cfg, fCont A *
    (K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2)) ∂muH

local notation "R3" => p4Q2PZ37AHX_originalThirdOrderRemainder H

/-- The integral remainder is exactly the error of the ORIGINAL
physical L2 transfer, using the proven Haar-a.e. source bridge. -/
theorem p4Q2PZ37AHX_originalThirdOrderRemainder_eq_sub
    (beta : ℝ) (B : Cfg) :
    R3 beta B = T beta f0 B - Q beta B := by
  unfold p4Q2PZ37AHX_originalThirdOrderRemainder
  calc
    (∫ A : Cfg, fCont A *
        (K beta A B - (1 - beta * S A B + (beta * S A B) ^ 2 / 2)) ∂muH) =
        ∫ A : Cfg, fCont A * K beta A B -
          fCont A * (1 - beta * S A B + (beta * S A B) ^ 2 / 2) ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      ring
    _ = (∫ A : Cfg, fCont A * K beta A B ∂muH) -
        (∫ A : Cfg,
          fCont A * (1 - beta * S A B + (beta * S A B) ^ 2 / 2) ∂muH) := by
      rw [integral_sub
        (p4Q2PZ37AHP_originalKernelWeightedSource_integrable H beta B)
        (p4Q2PZ37AHX_originalQuadraticWeightedSource_integrable H beta B)]
    _ = T beta f0 B - Q beta B := by
      rw [← p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral H beta B,
        p4Q2PZ37AHX_originalQuadraticHaar_exact H beta B]

/-- Exact second-order expansion of the genuine complete Wilson
transfer. The first coefficient is -V_H, with no missing halfweight. -/
theorem p4Q2PZ37AHX_originalTransfer_secondOrder_expansion
    (beta : ℝ) (B : Cfg) :
    T beta f0 B = -(beta * Vsrc) +
      (beta ^ 2 / 2) * ((3 * pH + W B) * Vsrc) + R3 beta B := by
  rw [p4Q2PZ37AHX_originalThirdOrderRemainder_eq_sub H beta B]
  unfold p4Q2PZ37AHX_originalQuadraticApproximation
  ring

/-- Uniform genuine third-order remainder at every nonnegative beta. -/
theorem p4Q2PZ37AHX_originalThirdOrderRemainder_abs_bound
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |R3 beta B| ≤ E3 beta := by
  rw [p4Q2PZ37AHX_originalThirdOrderRemainder_eq_sub H beta B,
    p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral H beta B,
    ← p4Q2PZ37AHX_originalQuadraticHaar_exact H beta B]
  exact p4Q2PZ37AHX_originalSignedTaylorHaarError H beta hbeta B

/-- The same remainder has a fully explicit original plaquette-count
bound, without assuming that the signed source is nonnegative. -/
theorem p4Q2PZ37AHX_originalThirdOrderRemainder_abs_halfCount
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |R3 beta B| ≤ ((beta * Cslab) ^ 3 / 6) * (pH / 2) := by
  have hC : 0 ≤ Cslab :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  calc
    |R3 beta B| ≤ E3 beta :=
      p4Q2PZ37AHX_originalThirdOrderRemainder_abs_bound H beta hbeta B
    _ ≤ ((beta * Cslab) ^ 3 / 6) * (pH / 2) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AHJ_originalCenteredSource_L1_le_halfCount H)
        (div_nonneg (pow_nonneg (mul_nonneg hbeta hC) 3) (by norm_num))

/-- Two-sided enclosure about the exactly evaluated quadratic center. -/
theorem p4Q2PZ37AHX_originalTransfer_secondOrder_interval
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Q beta B - E3 beta ≤ T beta f0 B ∧
      T beta f0 B ≤ Q beta B + E3 beta := by
  have h := abs_le.mp
    (p4Q2PZ37AHX_originalThirdOrderRemainder_abs_bound H beta hbeta B)
  rw [p4Q2PZ37AHX_originalThirdOrderRemainder_eq_sub H beta B] at h
  constructor <;> linarith only [h.1, h.2]

/-- A quantitative NEGATIVE sign criterion for the actual transfer.
The hypothesis is a real error-margin condition, not a declared sign. -/
theorem p4Q2PZ37AHX_originalTransfer_negative_of_cubicBudget
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg)
    (hMargin : (beta ^ 2 / 2) * ((3 * pH + W B) * Vsrc) + E3 beta <
      beta * Vsrc) :
    T beta f0 B < 0 := by
  have h := (p4Q2PZ37AHX_originalTransfer_secondOrder_interval H beta hbeta B).2
  unfold p4Q2PZ37AHX_originalQuadraticApproximation at h
  linarith only [h, hMargin]

/-- A quantitative POSITIVE sign criterion, kept independent from
the negative branch and not presumed to hold at the fixed coupling. -/
theorem p4Q2PZ37AHX_originalTransfer_positive_of_cubicBudget
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg)
    (hMargin : beta * Vsrc + E3 beta <
      (beta ^ 2 / 2) * ((3 * pH + W B) * Vsrc)) :
    0 < T beta f0 B := by
  have h := (p4Q2PZ37AHX_originalTransfer_secondOrder_interval H beta hbeta B).1
  unfold p4Q2PZ37AHX_originalQuadraticApproximation at h
  linarith only [h, hMargin]

/-- The ORIGINAL fixed beta0 is substituted into the genuine
two-sided enclosure without any small-coupling hypothesis. -/
theorem p4Q2PZ37AHX_originalFixedTransfer_secondOrder_interval
    (B : Cfg) :
    Q beta0 B - E3 beta0 ≤ T beta0 f0 B ∧
      T beta0 f0 B ≤ Q beta0 B + E3 beta0 :=
  p4Q2PZ37AHX_originalTransfer_secondOrder_interval
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le B

/-- Explicit conditional fixed-coupling negative branch. No claim
that its genuine numerical margin has already been certified. -/
theorem p4Q2PZ37AHX_originalFixedTransfer_negative_of_cubicBudget
    (B : Cfg)
    (hMargin : (beta0 ^ 2 / 2) * ((3 * pH + W B) * Vsrc) + E3 beta0 <
      beta0 * Vsrc) :
    T beta0 f0 B < 0 :=
  p4Q2PZ37AHX_originalTransfer_negative_of_cubicBudget
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le B hMargin

/-- Explicit conditional fixed-coupling positive branch on the
same original source and complete Boltzmann transfer. -/
theorem p4Q2PZ37AHX_originalFixedTransfer_positive_of_cubicBudget
    (B : Cfg)
    (hMargin : beta0 * Vsrc + E3 beta0 <
      (beta0 ^ 2 / 2) * ((3 * pH + W B) * Vsrc)) :
    0 < T beta0 f0 B :=
  p4Q2PZ37AHX_originalTransfer_positive_of_cubicBudget
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le B hMargin

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHX_exp_neg_cubicRemainder
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalKernel_secondOrder_pointwise
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalKernel_secondOrder_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalQuadraticWeightedSource_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalQuadraticHaar_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalCubicBudget_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalCubicBudget_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalCubicBudget_eq_scaledQuadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalSignedTaylorHaarError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalThirdOrderRemainder_eq_sub
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalTransfer_secondOrder_expansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalThirdOrderRemainder_abs_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalThirdOrderRemainder_abs_halfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalTransfer_secondOrder_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalTransfer_negative_of_cubicBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalTransfer_positive_of_cubicBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalFixedTransfer_secondOrder_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalFixedTransfer_negative_of_cubicBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHX_originalFixedTransfer_positive_of_cubicBudget
