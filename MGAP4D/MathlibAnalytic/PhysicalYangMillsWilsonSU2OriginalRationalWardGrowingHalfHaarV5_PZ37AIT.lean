import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalWardCrossingHalfHaarUnitCouplingV5_PZ37AIS
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIT — rational Ward improvement and volume-growing half-Haar range

Retain the ORIGINAL complete SU(2) Wilson action, both spatial halfweights,
signed ZW physical L2 source and continuous representative, genuine normalized
Haar, AIG's unchanged full negative margin and strict negative region,
all earlier assumptions/results/roots, and the fixed Lean/mathlib budgets.

For BOTH signs of the bounded original source, strengthen the scalar
quadratic correction from beta*exp(-beta*p_H/2) to beta/(1+beta*p_H/2).
With AIS's genuine Ward crossing estimate and BOTH original halfweights,
  T_beta f0(B) <= -Dhat_H(beta) whenever beta>0 and f_H(B)<=0,
  Dhat_H(beta) = beta/(1+beta*p_H/2)*exp(-2*beta*p_H)*V_H.
This floor strictly exceeds AIS's floor at every positive coupling.
The ORIGINAL margin obeys
  2*epsilon_H = ((1+beta*p_H/2)*Zcross_H(beta))*Dhat_H
for beta>=0. The genuine partition is antitone. Its unit-coupling Gaussian
certificate and the quadratic exponential bound give comparison factor<=1
through the CLOSED endpoint b_H=1+p_H/4=1+6*(H+1)^3>=7.
Thus the same original full-margin region has Haar mass>=1/2 for
EVERY finite H and 0<beta<=b_H, in particular 0<beta<=7 uniformly in H.
Every FIXED beta>0 is also covered at all sufficiently large original volumes.

For each FIXED beta>0, Dhat_H(beta) tends to zero as H tends to infinity.
There is no positive volume-uniform lower bound for THIS scalar certificate.
This is not an upper bound on the actual negative-transfer magnitude, and
it does not rule out a different certificate with a uniform positive floor.
No common configuration-space/operator limit, all-positive-coupling claim
at each fixed H, coercivity, negative eigenvalue, Hamiltonian spectral gap,
or continuum four-dimensional Yang-Mills mass gap is inferred.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The rational signed-source coefficient is nonnegative on the same
nonnegative coupling and source-radius domain. -/
theorem p4Q2PZ37AIT_real_rationalCoefficient_nonneg
    (beta c : ℝ) (hbeta : 0 ≤ beta) (hc : 0 ≤ c) :
    0 ≤ beta / (1 + beta * c) := by
  have hDen : 0 < 1 + beta * c := by positivity
  exact div_nonneg hbeta hDen.le

theorem p4Q2PZ37AIT_real_rationalCoefficient_pos
    (beta c : ℝ) (hbeta : 0 < beta) (hc : 0 ≤ c) :
    0 < beta / (1 + beta * c) := by
  have hDen : 0 < 1 + beta * c := by positivity
  exact div_pos hbeta hDen

theorem p4Q2PZ37AIT_real_rationalCoefficient_le_beta
    (beta c : ℝ) (hbeta : 0 ≤ beta) (hc : 0 ≤ c) :
    beta / (1 + beta * c) ≤ beta := by
  have hDen : 0 < 1 + beta * c := by positivity
  apply (div_le_iff₀ hDen).mpr
  have hExtra : 0 ≤ beta * (beta * c) :=
    mul_nonneg hbeta (mul_nonneg hbeta hc)
  nlinarith only [hExtra]

/-- Strict improvement over AIE/AIN's existing coefficient. Strictness
requires positive coupling and a positive source radius. -/
theorem p4Q2PZ37AIT_real_previousCoefficient_lt_rational
    (beta c : ℝ) (hbeta : 0 < beta) (hc : 0 < c) :
    beta * Real.exp (-(beta * c)) < beta / (1 + beta * c) := by
  have hArg : 0 < beta * c := mul_pos hbeta hc
  have hDen : 0 < 1 + beta * c := by positivity
  have hCancel : Real.exp (beta * c) * Real.exp (-(beta * c)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hDeficit : (1 + beta * c) * Real.exp (-(beta * c)) < 1 := by
    calc
      (1 + beta * c) * Real.exp (-(beta * c)) =
          (beta * c + 1) * Real.exp (-(beta * c)) := by ring
      _ < Real.exp (beta * c) * Real.exp (-(beta * c)) :=
        mul_lt_mul_of_pos_right
          (Real.add_one_lt_exp (ne_of_gt hArg)) (Real.exp_pos _)
      _ = 1 := hCancel
  apply (lt_div_iff₀ hDen).mpr
  calc
    (beta * Real.exp (-(beta * c))) * (1 + beta * c) =
        beta * ((1 + beta * c) * Real.exp (-(beta * c))) := by ring
    _ < beta * 1 := mul_lt_mul_of_pos_left hDeficit hbeta
    _ = beta := mul_one beta

/-- Rational quantitative negative exponential covariance. The proof
retains BOTH signs of x and uses only its original symmetric range. -/
theorem p4Q2PZ37AIT_real_centeredLaplace_rationalQuadraticUpper
    (beta c x : ℝ) (hbeta : 0 ≤ beta) (hc : 0 ≤ c)
    (hx : |x| ≤ c) :
    x * (Real.exp (-(beta * x)) - 1) ≤
      -((beta / (1 + beta * c)) * x ^ 2) := by
  have hDen : 0 < 1 + beta * c := by positivity
  rcases le_total (0 : ℝ) x with hx0 | hx0
  · have hEx : beta * x + 1 ≤ Real.exp (beta * x) :=
      Real.add_one_le_exp (beta * x)
    have hCancel :
        Real.exp (beta * x) * Real.exp (-(beta * x)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hProd :
        (beta * x + 1) * Real.exp (-(beta * x)) ≤ 1 := by
      calc
        (beta * x + 1) * Real.exp (-(beta * x)) ≤
            Real.exp (beta * x) * Real.exp (-(beta * x)) :=
          mul_le_mul_of_nonneg_right hEx (Real.exp_pos _).le
        _ = 1 := hCancel
    have hOneMinus : 0 ≤ 1 - Real.exp (-(beta * x)) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (mul_nonneg hbeta hx0)))
    have hGap : 0 ≤ beta * (c - x) * (1 - Real.exp (-(beta * x))) :=
      mul_nonneg
        (mul_nonneg hbeta (sub_nonneg.mpr (abs_le.mp hx).2)) hOneMinus
    have hIncrement :
        beta * x ≤ (1 + beta * c) * (1 - Real.exp (-(beta * x))) := by
      nlinarith only [hProd, hGap]
    have hScaled := mul_le_mul_of_nonneg_right hIncrement hx0
    have hNumerator :
        beta * x ^ 2 ≤
          (x * (1 - Real.exp (-(beta * x)))) * (1 + beta * c) := by
      calc
        beta * x ^ 2 = (beta * x) * x := by ring
        _ ≤ ((1 + beta * c) * (1 - Real.exp (-(beta * x)))) * x := hScaled
        _ = (x * (1 - Real.exp (-(beta * x)))) * (1 + beta * c) := by ring
    have hQuotient :
        beta * x ^ 2 / (1 + beta * c) ≤
          x * (1 - Real.exp (-(beta * x))) :=
      (div_le_iff₀ hDen).mpr hNumerator
    calc
      x * (Real.exp (-(beta * x)) - 1) =
          -(x * (1 - Real.exp (-(beta * x)))) := by ring
      _ ≤ -(beta * x ^ 2 / (1 + beta * c)) := neg_le_neg hQuotient
      _ = -((beta / (1 + beta * c)) * x ^ 2) := by ring
  · have hEx : -(beta * x) + 1 ≤ Real.exp (-(beta * x)) :=
      Real.add_one_le_exp (-(beta * x))
    have hMult := mul_le_mul_of_nonpos_left hEx hx0
    have hCore :
        x * (Real.exp (-(beta * x)) - 1) ≤ -(beta * x ^ 2) := by
      nlinarith only [hMult]
    have hCorrection :
        (beta / (1 + beta * c)) * x ^ 2 ≤ beta * x ^ 2 :=
      mul_le_mul_of_nonneg_right
        (p4Q2PZ37AIT_real_rationalCoefficient_le_beta beta c hbeta hc)
        (sq_nonneg x)
    exact hCore.trans (neg_le_neg hCorrection)

/-- The same signed inequality in the form used by the physical
crossing integral. No positivity condition on x is inserted. -/
theorem p4Q2PZ37AIT_real_signedLaplace_rationalUpper
    (beta c x : ℝ) (hbeta : 0 ≤ beta) (hc : 0 ≤ c)
    (hx : |x| ≤ c) :
    x * Real.exp (-(beta * x)) ≤
      x - (beta / (1 + beta * c)) * x ^ 2 := by
  have h := p4Q2PZ37AIT_real_centeredLaplace_rationalQuadraticUpper
    beta c x hbeta hc hx
  nlinarith only [h]

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIT_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIT_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIT_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIT_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIT_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "KC" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "r" => p4Q2PZ37ABN_originalTemporalWilsonCoefficient
local notation "margin" => p4Q2PZ37AIG_originalNegativeTransferMargin H

local instance p4Q2PZ37AIT_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- A coefficient for a strengthened estimate, not a replacement source,
kernel, action or physical transfer. -/
def p4Q2PZ37AIT_rationalSourceCoefficient (beta : ℝ) : ℝ :=
  beta / (1 + beta * pH / 2)

local notation "coeff" => p4Q2PZ37AIT_rationalSourceCoefficient H

theorem p4Q2PZ37AIT_rationalSourceCoefficient_nonneg
    (beta : ℝ) (hbeta : 0 ≤ beta) : 0 ≤ coeff beta := by
  simpa only [p4Q2PZ37AIT_rationalSourceCoefficient, mul_div_assoc] using
    p4Q2PZ37AIT_real_rationalCoefficient_nonneg beta (pH / 2) hbeta
      (div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num))

theorem p4Q2PZ37AIT_rationalSourceCoefficient_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < coeff beta := by
  simpa only [p4Q2PZ37AIT_rationalSourceCoefficient, mul_div_assoc] using
    p4Q2PZ37AIT_real_rationalCoefficient_pos beta (pH / 2) hbeta
      (div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num))

theorem p4Q2PZ37AIT_rationalSourceCoefficient_le_beta
    (beta : ℝ) (hbeta : 0 ≤ beta) : coeff beta ≤ beta := by
  simpa only [p4Q2PZ37AIT_rationalSourceCoefficient, mul_div_assoc] using
    p4Q2PZ37AIT_real_rationalCoefficient_le_beta beta (pH / 2) hbeta
      (div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num))

theorem p4Q2PZ37AIT_previousCoefficient_lt_rationalSourceCoefficient
    (beta : ℝ) (hbeta : 0 < beta) :
    beta * Real.exp (-(beta * pH / 2)) < coeff beta := by
  simpa only [p4Q2PZ37AIT_rationalSourceCoefficient, mul_div_assoc] using
    p4Q2PZ37AIT_real_previousCoefficient_lt_rational beta (pH / 2) hbeta
      (div_pos (p4Q2PZ37AHN_count_pos H) (by norm_num))

theorem p4Q2PZ37AIT_originalRightWeightedTransfer_rationalQuadraticUpper
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Real.exp ((beta / 2) * W B) * T beta f0 B ≤
      Real.exp (-(beta * (pH / 2))) *
        (Zcross beta * r beta ^ 4 * fCont B -
          coeff beta *
            (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH)) := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hk := p4Q2PZ37AIN_originalCrossingKernel_leftContinuous H beta B
  have hSource : Integrable (fun A : Cfg => KC beta A B * fCont A) muH :=
    (hk.mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSq : Integrable (fun A : Cfg => KC beta A B * (fCont A) ^ 2) muH :=
    (hk.mul (hf.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hExp : Integrable
      (fun A : Cfg => KC beta A B * (fCont A * Real.exp (-(beta * fCont A)))) muH := by
    have hArg : Continuous (fun A : Cfg => -(beta * fCont A)) :=
      (continuous_const.mul hf).neg
    exact (hk.mul (hf.mul (Real.continuous_exp.comp hArg))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCorrection : Integrable
      (fun A : Cfg => coeff beta *
        (KC beta A B * (fCont A) ^ 2)) muH := hSq.const_mul _
  have hPoint (A : Cfg) :
      KC beta A B * (fCont A * Real.exp (-(beta * fCont A))) ≤
        KC beta A B * fCont A -
          coeff beta *
            (KC beta A B * (fCont A) ^ 2) := by
    have hScalar := p4Q2PZ37AIT_real_signedLaplace_rationalUpper
      beta (pH / 2) (fCont A) hbeta
      (div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num))
      (p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A)
    have hScalar' : fCont A * Real.exp (-(beta * fCont A)) ≤
        fCont A - coeff beta * (fCont A) ^ 2 := by
      simpa only [p4Q2PZ37AIT_rationalSourceCoefficient, mul_div_assoc] using hScalar
    have hScaled := mul_le_mul_of_nonneg_left hScalar'
      (p4Q2PZ37AIN_originalCrossingKernel_pos H beta A B).le
    nlinarith only [hScaled]
  rw [p4Q2PZ37AIF_originalRightWeightedTransfer_eq_crossingIntegral H beta B]
  calc
    (∫ A : Cfg, (fCont A * Real.exp (-(beta / 2) * W A)) * KC beta A B ∂muH) =
        Real.exp (-(beta * (pH / 2))) *
          (∫ A : Cfg, KC beta A B * (fCont A * Real.exp (-(beta * fCont A))) ∂muH) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PZ37AIN_originalLeftHalfweight_factor H beta A]
      ring
    _ ≤ Real.exp (-(beta * (pH / 2))) *
          (∫ A : Cfg, KC beta A B * fCont A -
            coeff beta *
              (KC beta A B * (fCont A) ^ 2) ∂muH) :=
      mul_le_mul_of_nonneg_left
        (integral_mono hExp (hSource.sub hCorrection) hPoint) (Real.exp_pos _).le
    _ = Real.exp (-(beta * (pH / 2))) *
        (Zcross beta * r beta ^ 4 * fCont B -
          coeff beta *
            (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH)) := by
      rw [integral_sub hSource hCorrection, integral_const_mul,
        p4Q2PZ37AIN_originalCrossingSource_convolution H beta B]

/-- New auxiliary lower amplitude, with the SAME source variance and
complete physical transfer. This definition does not alter AIG's margin. -/
def p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor (beta : ℝ) : ℝ :=
  coeff beta * Real.exp (-(2 * beta * pH)) * Vsrc

local notation "rationalFloor" => p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor H

theorem p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < rationalFloor beta := by
  exact mul_pos
    (mul_pos (p4Q2PZ37AIT_rationalSourceCoefficient_pos H beta hbeta) (Real.exp_pos _))
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2

/-- A strict strengthening of AIS at every positive coupling and finite
volume, proved by comparing the signed scalar coefficients. -/
theorem p4Q2PZ37AIT_previousWardFloor_lt_rationalWardFloor
    (beta : ℝ) (hbeta : 0 < beta) :
    p4Q2PZ37AIS_sourceNonpositiveWardFloor H beta < rationalFloor beta := by
  have hCoefficient :=
    p4Q2PZ37AIT_previousCoefficient_lt_rationalSourceCoefficient H beta hbeta
  have hPositive : 0 < Real.exp (-(2 * beta * pH)) * Vsrc :=
    mul_pos (Real.exp_pos _)
      (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hExp : Real.exp (-(beta * pH / 2)) * Real.exp (-(2 * beta * pH)) =
      Real.exp (-(5 * beta * pH / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    p4Q2PZ37AIS_sourceNonpositiveWardFloor H beta =
        (beta * Real.exp (-(beta * pH / 2))) *
          (Real.exp (-(2 * beta * pH)) * Vsrc) := by
      unfold p4Q2PZ37AIS_sourceNonpositiveWardFloor
      rw [← hExp]
      ring
    _ < coeff beta * (Real.exp (-(2 * beta * pH)) * Vsrc) :=
      mul_lt_mul_of_pos_right hCoefficient hPositive
    _ = rationalFloor beta := by
      unfold p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor
      ring

/-- Insert AIS's exact Ward crossing estimate into the stronger signed
quadratic envelope, retaining the original right-weighted transfer. -/
theorem p4Q2PZ37AIT_originalRightWeightedTransfer_le_negativeRationalWardVariance
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) (hB : fCont B ≤ 0) :
    Real.exp ((beta / 2) * W B) * T beta f0 B ≤
      -(coeff beta * Real.exp (-(3 * beta * pH / 2)) * Vsrc) := by
  have hSource : Zcross beta * r beta ^ 4 * fCont B ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_pos (p4Q2PZ37AIF_originalCrossingPartition_pos H beta)
        (pow_pos (p4Q2PZ37ABN_originalTemporalWilsonCoefficient_pos beta hbeta) 4)).le hB
  have hSourceScaled := mul_nonpos_of_nonneg_of_nonpos
    (Real.exp_pos (-(beta * (pH / 2)))).le hSource
  have hCoefficient : 0 ≤ Real.exp (-(beta * (pH / 2))) * coeff beta :=
    mul_nonneg (Real.exp_pos _).le
      (p4Q2PZ37AIT_rationalSourceCoefficient_nonneg H beta hbeta.le)
  have hSecond := mul_le_mul_of_nonneg_left
    (p4Q2PZ37AIS_originalCrossingSecondMoment_wardLower H beta B) hCoefficient
  have hExp : Real.exp (-(beta * (pH / 2))) * Real.exp (-(beta * pH)) =
      Real.exp (-(3 * beta * pH / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hFloor : Real.exp (-(beta * (pH / 2))) * coeff beta *
        (Real.exp (-(beta * pH)) * Vsrc) =
      coeff beta * Real.exp (-(3 * beta * pH / 2)) * Vsrc := by
    calc
      _ = coeff beta *
          (Real.exp (-(beta * (pH / 2))) * Real.exp (-(beta * pH))) * Vsrc := by ring
      _ = _ := by rw [hExp]
  calc
    _ ≤ Real.exp (-(beta * (pH / 2))) *
        (Zcross beta * r beta ^ 4 * fCont B -
          coeff beta * (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH)) :=
      p4Q2PZ37AIT_originalRightWeightedTransfer_rationalQuadraticUpper H beta hbeta.le B
    _ ≤ -(Real.exp (-(beta * (pH / 2))) * coeff beta *
        (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH)) := by
      nlinarith only [hSourceScaled]
    _ ≤ -(Real.exp (-(beta * (pH / 2))) * coeff beta *
        (Real.exp (-(beta * pH)) * Vsrc)) := neg_le_neg hSecond
    _ = _ := by rw [hFloor]

/-- Restore the SAME original right halfweight using W(B)<=p_H.
The two spatial halfweights and Ward crossing estimate total 2*beta*p_H. -/
theorem p4Q2PZ37AIT_originalTransfer_le_negativeRationalWardFloor
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) (hB : fCont B ≤ 0) :
    T beta f0 B ≤ -(rationalFloor beta) := by
  have hW := p4Q2PZ37AIO_originalAction_le_count_of_source_nonpos H B hB
  have hInverse : Real.exp (-(beta * pH / 2)) ≤ Real.exp (-(beta / 2) * W B) := by
    apply Real.exp_le_exp.mpr
    have hMul := mul_le_mul_of_nonneg_left hW hbeta.le
    nlinarith only [hMul]
  have hNonpos : -(coeff beta * Real.exp (-(3 * beta * pH / 2)) * Vsrc) ≤ 0 :=
    neg_nonpos.mpr (mul_pos
      (mul_pos (p4Q2PZ37AIT_rationalSourceCoefficient_pos H beta hbeta) (Real.exp_pos _))
      (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2).le
  have hCancel : Real.exp (-(beta / 2) * W B) *
      Real.exp ((beta / 2) * W B) = 1 := by
    have hArg : -(beta / 2) * W B + (beta / 2) * W B = 0 := by ring
    rw [← Real.exp_add, hArg, Real.exp_zero]
  have hExp : Real.exp (-(beta * pH / 2)) * Real.exp (-(3 * beta * pH / 2)) =
      Real.exp (-(2 * beta * pH)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    T beta f0 B = Real.exp (-(beta / 2) * W B) *
        (Real.exp ((beta / 2) * W B) * T beta f0 B) := by
      rw [← mul_assoc, hCancel, one_mul]
    _ ≤ Real.exp (-(beta / 2) * W B) *
        (-(coeff beta * Real.exp (-(3 * beta * pH / 2)) * Vsrc)) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AIT_originalRightWeightedTransfer_le_negativeRationalWardVariance
          H beta hbeta B hB) (Real.exp_pos _).le
    _ ≤ Real.exp (-(beta * pH / 2)) *
        (-(coeff beta * Real.exp (-(3 * beta * pH / 2)) * Vsrc)) :=
      mul_le_mul_of_nonpos_right hInverse hNonpos
    _ = -(coeff beta * (Real.exp (-(beta * pH / 2)) *
        Real.exp (-(3 * beta * pH / 2))) * Vsrc) := by ring
    _ = -(rationalFloor beta) := by rw [hExp]; rfl

/-- Exact cancellation with AIG's UNCHANGED epsilon. Nonnegative coupling
ensures the auxiliary rational denominator is nonzero; no physical object
or partition is normalized or substituted. -/
theorem p4Q2PZ37AIT_originalNegativeMargin_rationalWardRatio_identity
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    2 * margin beta =
      ((1 + beta * pH / 2) * Zcross beta) * rationalFloor beta := by
  have hp := (p4Q2PZ37AHN_count_pos H).le
  have hDen : 1 + beta * pH / 2 ≠ 0 := ne_of_gt (by positivity)
  have hCancel : (1 + beta * pH / 2) * coeff beta = beta := by
    unfold p4Q2PZ37AIT_rationalSourceCoefficient
    field_simp [hDen]
  unfold p4Q2PZ37AIG_originalNegativeTransferMargin
    p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor
  calc
    2 * (beta * Zcross beta * Real.exp (-(2 * beta * pH)) * Vsrc / 2) =
        Zcross beta * beta * Real.exp (-(2 * beta * pH)) * Vsrc := by ring
    _ = Zcross beta * ((1 + beta * pH / 2) * coeff beta) *
        Real.exp (-(2 * beta * pH)) * Vsrc := by rw [hCancel]
    _ = ((1 + beta * pH / 2) * Zcross beta) *
        (coeff beta * Real.exp (-(2 * beta * pH)) * Vsrc) := by ring

local notation "nu" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "z" => p4Q2PZ37AIF_originalSingleLinkPartition

/-- Antitone dependence of the actual original Haar integral on beta.
This uses nonnegativity of the original Wilson link energy. -/
theorem p4Q2PZ37AIT_originalSingleLinkPartition_antitone : Antitone z := by
  intro beta gamma hOrder
  unfold p4Q2PZ37AIF_originalSingleLinkPartition
  apply integral_mono
    (p4Q2PZ37AIF_originalSingleLinkPartition_integrable gamma)
    (p4Q2PZ37AIF_originalSingleLinkPartition_integrable beta)
  intro g
  apply Real.exp_le_exp.mpr
  have hEnergy : 0 ≤ E g :=
    specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num : 0 < (2 : ℕ)) g
  have hProduct := mul_le_mul_of_nonneg_right hOrder hEnergy
  nlinarith only [hProduct]


/-- Lift antitonicity through AIF's exact original finite Haar product.
No independence of overlapping spatial plaquettes is assumed. -/
theorem p4Q2PZ37AIT_originalCrossingPartition_antitone : Antitone Zcross := by
  intro beta gamma hOrder
  unfold p4Q2PZ37AIF_originalCrossingPartition
  exact pow_le_pow_left₀ (p4Q2PZ37AIF_originalSingleLinkPartition_pos gamma).le
    (p4Q2PZ37AIT_originalSingleLinkPartition_antitone hOrder) _

/-- Above unit coupling, the unchanged partition remains below its genuine
unit-coupling Gaussian certificate. -/
theorem p4Q2PZ37AIT_originalCrossingPartition_le_unitGaussian
    (beta : ℝ) (hOne : 1 ≤ beta) :
    Zcross beta ≤ Real.exp (-(pH / 2)) := by
  calc
    Zcross beta ≤ Zcross 1 :=
      p4Q2PZ37AIT_originalCrossingPartition_antitone H hOne
    _ ≤ Real.exp (pH * (-(1 : ℝ) + (1 : ℝ) ^ 2 / 2)) :=
      p4Q2PZ37AIQ_originalCrossingPartition_le_gaussian H 1
    _ = Real.exp (-(pH / 2)) := by
      congr 1
      ring

/-- A new auxiliary sufficient endpoint; the physical coupling, original
negative margin, and all previous cutoffs retain their definitions. -/
def p4Q2PZ37AIT_volumeGrowingCouplingCutoff : ℝ := 1 + pH / 4

local notation "cutoff" => p4Q2PZ37AIT_volumeGrowingCouplingCutoff H

theorem p4Q2PZ37AIT_volumeGrowingCutoff_eq_cubic :
    cutoff = 1 + 6 * ((H : ℝ) + 1) ^ 3 := by
  unfold p4Q2PZ37AIT_volumeGrowingCouplingCutoff
  rw [p4Q2PZ37AIB_plaquetteCount_exact H]
  ring

theorem p4Q2PZ37AIT_volumeGrowingCutoff_ge_seven : (7 : ℝ) ≤ cutoff := by
  rw [p4Q2PZ37AIT_volumeGrowingCutoff_eq_cubic H]
  have hOne : (1 : ℝ) ≤ (H : ℝ) + 1 := by
    have hZero : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    linarith only [hZero]
  have hCube : (1 : ℝ) ≤ ((H : ℝ) + 1) ^ 3 := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hOne 3
  nlinarith only [hCube]

theorem p4Q2PZ37AIT_volumeGrowingCouplingCutoff_pos : 0 < cutoff :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7)
    (p4Q2PZ37AIT_volumeGrowingCutoff_ge_seven H)

theorem p4Q2PZ37AIT_volumeGrowingCutoff_zero :
    p4Q2PZ37AIT_volumeGrowingCouplingCutoff 0 = 7 := by
  rw [p4Q2PZ37AIT_volumeGrowingCutoff_eq_cubic]
  norm_num

/-- An elementary growth witness, sufficient to obtain an eventual-volume
statement for each fixed coupling without using an asymptotic exp theorem. -/
theorem p4Q2PZ37AIT_volumeGrowingCutoff_ge_cast : (H : ℝ) ≤ cutoff := by
  rw [p4Q2PZ37AIT_volumeGrowingCutoff_eq_cubic H]
  have hZero : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hSquare := sq_nonneg (H : ℝ)
  have hCube : (0 : ℝ) ≤ (H : ℝ) ^ 2 * (H : ℝ) :=
    mul_nonneg hSquare hZero
  nlinarith only [hZero, hSquare, hCube]

theorem p4Q2PZ37AIT_eventually_le_volumeGrowingCutoff (beta : ℝ) :
    ∃ N : ℕ, ∀ K : ℕ, N ≤ K →
      beta ≤ p4Q2PZ37AIT_volumeGrowingCouplingCutoff K := by
  obtain ⟨N, hN⟩ := exists_nat_ge beta
  refine ⟨N, ?_⟩
  intro K hK
  have hCast : (N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  exact hN.trans (hCast.trans (p4Q2PZ37AIT_volumeGrowingCutoff_ge_cast K))

/-- Pinned Real.quadratic_le_exp_of_nonneg gives the quadratic budget
which determines the new volume-growing endpoint. -/
theorem p4Q2PZ37AIT_rationalBudget_le_expHalf_of_le_cutoff
    (beta : ℝ) (hEnd : beta ≤ cutoff) :
    1 + beta * pH / 2 ≤ Real.exp (pH / 2) := by
  have hCount := (p4Q2PZ37AHN_count_pos H).le
  have hExp := Real.quadratic_le_exp_of_nonneg
    (div_nonneg hCount (by norm_num : (0 : ℝ) ≤ 2))
  have hScaled := mul_le_mul_of_nonneg_right hEnd hCount
  change beta * pH ≤ (1 + pH / 4) * pH at hScaled
  nlinarith only [hExp, hScaled]

/-- Below unit coupling, the original AIS comparison directly controls
the new rational factor by the elementary exponential tangent. -/
theorem p4Q2PZ37AIT_originalRationalMarginFactor_le_one_of_le_one
    (beta : ℝ) (hbeta : 0 ≤ beta) (hOne : beta ≤ 1) :
    (1 + beta * pH / 2) * Zcross beta ≤ 1 := by
  have hTangent : 1 + beta * pH / 2 ≤ Real.exp (beta * pH / 2) := by
    simpa only [add_comm] using Real.add_one_le_exp (beta * pH / 2)
  calc
    _ ≤ Real.exp (beta * pH / 2) * Zcross beta :=
      mul_le_mul_of_nonneg_right hTangent
        (p4Q2PZ37AIF_originalCrossingPartition_pos H beta).le
    _ = Zcross beta * Real.exp (beta * pH / 2) := mul_comm _ _
    _ ≤ 1 := p4Q2PZ37AIS_originalWardMarginFactor_le_one H beta hbeta hOne

/-- Above unit coupling, combine the actual antitone partition with its
fixed unit-coupling certificate and the new polynomial volume budget. -/
theorem p4Q2PZ37AIT_originalRationalMarginFactor_le_one_of_one_le
    (beta : ℝ) (hOne : 1 ≤ beta) (hEnd : beta ≤ cutoff) :
    (1 + beta * pH / 2) * Zcross beta ≤ 1 := by
  have hbeta : 0 ≤ beta := le_trans (by norm_num : (0 : ℝ) ≤ 1) hOne
  have hFactor : 0 ≤ 1 + beta * pH / 2 := by
    have hp := (p4Q2PZ37AHN_count_pos H).le
    positivity
  calc
    _ ≤ (1 + beta * pH / 2) * Real.exp (-(pH / 2)) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AIT_originalCrossingPartition_le_unitGaussian H beta hOne) hFactor
    _ ≤ Real.exp (pH / 2) * Real.exp (-(pH / 2)) :=
      mul_le_mul_of_nonneg_right
        (p4Q2PZ37AIT_rationalBudget_le_expHalf_of_le_cutoff H beta hEnd)
        (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- Full closed sufficient interval for the new rational Ward comparison.
The endpoint is included; no physical critical-coupling interpretation. -/
theorem p4Q2PZ37AIT_originalRationalMarginFactor_le_one
    (beta : ℝ) (hbeta : 0 ≤ beta) (hEnd : beta ≤ cutoff) :
    (1 + beta * pH / 2) * Zcross beta ≤ 1 := by
  rcases le_total beta 1 with hOne | hOne
  · exact p4Q2PZ37AIT_originalRationalMarginFactor_le_one_of_le_one H beta hbeta hOne
  · exact p4Q2PZ37AIT_originalRationalMarginFactor_le_one_of_one_le H beta hOne hEnd

theorem p4Q2PZ37AIT_originalRationalMarginFactor_le_one_of_le_seven
    (beta : ℝ) (hbeta : 0 ≤ beta) (hSeven : beta ≤ 7) :
    (1 + beta * pH / 2) * Zcross beta ≤ 1 :=
  p4Q2PZ37AIT_originalRationalMarginFactor_le_one H beta hbeta
    (hSeven.trans (p4Q2PZ37AIT_volumeGrowingCutoff_ge_seven H))

local notation "Region" => p4Q2PZ37AIG_originalNegativeTransferRegion H

/-- Factor-two comparison with the UNCHANGED original AIG margin, including
the new volume-growing endpoint. -/
theorem p4Q2PZ37AIT_twice_originalNegativeMargin_le_rationalWardFloor
    (beta : ℝ) (hbeta : 0 < beta) (hEnd : beta ≤ cutoff) :
    2 * margin beta ≤ rationalFloor beta := by
  rw [p4Q2PZ37AIT_originalNegativeMargin_rationalWardRatio_identity H beta hbeta.le]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (p4Q2PZ37AIT_originalRationalMarginFactor_le_one H beta hbeta.le hEnd)
    (p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor_pos H beta hbeta).le

theorem p4Q2PZ37AIT_originalNegativeMargin_lt_rationalWardFloor
    (beta : ℝ) (hbeta : 0 < beta) (hEnd : beta ≤ cutoff) :
    margin beta < rationalFloor beta := by
  have hComparison :=
    p4Q2PZ37AIT_twice_originalNegativeMargin_le_rationalWardFloor H beta hbeta hEnd
  have hPositive := p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor_pos H beta hbeta
  linarith only [hComparison, hPositive]

/-- The source zero set is included; no assumption that it is Haar null. -/
theorem p4Q2PZ37AIT_originalSource_nonpos_subset_fullNegativeRegion
    (beta : ℝ) (hbeta : 0 < beta) (hEnd : beta ≤ cutoff) :
    {B : Cfg | fCont B ≤ 0} ⊆ Region beta := by
  intro B hB
  exact (p4Q2PZ37AIT_originalTransfer_le_negativeRationalWardFloor
    H beta hbeta B hB).trans_lt
      (neg_lt_neg (p4Q2PZ37AIT_originalNegativeMargin_lt_rationalWardFloor
        H beta hbeta hEnd))

/-- The SAME original full-margin negative region has genuine Haar mass
at least one half throughout 0<beta<=1+p_H/4. -/
theorem p4Q2PZ37AIT_originalFullNegativeRegion_Haar_half
    (beta : ℝ) (hbeta : 0 < beta) (hEnd : beta ≤ cutoff) :
    (1 / 2 : ℝ≥0∞) ≤ muH (Region beta) :=
  (p4Q2PZ37AIN_originalSource_nonpos_Haar_half H).trans
    (measure_mono
      (p4Q2PZ37AIT_originalSource_nonpos_subset_fullNegativeRegion H beta hbeta hEnd))

theorem p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half
    (beta : ℝ) (hbeta : 0 < beta) (hEnd : beta ≤ cutoff) :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region beta) := by
  have h := ENNReal.toReal_mono (measure_ne_top muH (Region beta))
    (p4Q2PZ37AIT_originalFullNegativeRegion_Haar_half H beta hbeta hEnd)
  simpa [Measure.real] using h

/-- A closed coupling interval shared by EVERY original finite volume. -/
theorem p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half_of_le_seven
    (beta : ℝ) (hbeta : 0 < beta) (hSeven : beta ≤ 7) :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region beta) :=
  p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half H beta hbeta
    (hSeven.trans (p4Q2PZ37AIT_volumeGrowingCutoff_ge_seven H))

/-- The actual volume-growing endpoint belongs to the certified interval. -/
theorem p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half_at_cutoff :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region cutoff) :=
  p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half H cutoff
    (p4Q2PZ37AIT_volumeGrowingCouplingCutoff_pos H) le_rfl

/-- Fix beta FIRST. Sufficiently large original finite volumes then satisfy
the same full-margin half-Haar property. The quantifiers are not reversed. -/
theorem p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half_eventually
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ N : ℕ, ∀ K : ℕ, N ≤ K →
      (1 / 2 : ℝ) ≤ Measure.real
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure K 2)
        (p4Q2PZ37AIG_originalNegativeTransferRegion K beta) := by
  obtain ⟨N, hN⟩ := p4Q2PZ37AIT_eventually_le_volumeGrowingCutoff beta
  exact ⟨N, fun K hK =>
    p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half K beta hbeta (hN K hK)⟩

/-- Exact volume dependence of the stronger auxiliary certificate. -/
theorem p4Q2PZ37AIT_rationalWardFloor_exactVolume (beta : ℝ) :
    rationalFloor beta =
      (beta / (1 + 12 * beta * ((H : ℝ) + 1) ^ 3)) *
        Real.exp (-(48 * beta * ((H : ℝ) + 1) ^ 3)) * Vsrc := by
  unfold p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor
    p4Q2PZ37AIT_rationalSourceCoefficient
  rw [p4Q2PZ37AIB_plaquetteCount_exact H]
  have hDen : 1 + beta * (24 * ((H : ℝ) + 1) ^ 3) / 2 =
      1 + 12 * beta * ((H : ℝ) + 1) ^ 3 := by ring
  have hArg : -(2 * beta * (24 * ((H : ℝ) + 1) ^ 3)) =
      -(48 * beta * ((H : ℝ) + 1) ^ 3) := by ring
  rw [hDen, hArg]

section PZ37AITVolumeDecay

open Filter
open scoped Topology

local notation "pAIT" => p4Q2PZ37AFZ_plaquetteCount
local notation "VAIT" => p4Q2PZ37AHN_originalSource_HaarSecondMoment
local notation "DAIT" => p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor

/-- The exact original plaquette count diverges with the original volume
index. No rescaled sequence of physical models is introduced. -/
theorem p4Q2PZ37AIT_originalCount_tendsto_atTop :
    Tendsto (fun H : ℕ => pAIT H) atTop atTop := by
  have hDom (H : ℕ) : (H : ℝ) ≤ pAIT H := by
    rw [p4Q2PZ37AIB_plaquetteCount_exact H]
    have hH : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    have hCube : (0 : ℝ) ≤ (H : ℝ) ^ 3 := pow_nonneg hH 3
    nlinarith only [hH, hCube, sq_nonneg (H : ℝ)]
  exact tendsto_atTop_mono hDom
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun H : ℕ => (H : ℝ)) atTop atTop)

/-- The genuine count-squared envelope is dominated by any fixed positive
exponential rate. This helper also applies to the previous AIS floor. -/
theorem p4Q2PZ37AIT_originalCountSquareExp_tendsto_zero
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun H : ℕ => (pAIT H) ^ 2 * Real.exp (-(a * pAIT H)))
      atTop (𝓝 0) := by
  have hArg : Tendsto (fun H : ℕ => a * pAIT H) atTop atTop :=
    (p4Q2PZ37AIT_originalCount_tendsto_atTop).const_mul_atTop ha
  have hKernel :
      Tendsto (fun H : ℕ => (a * pAIT H) ^ 2 * Real.exp (-(a * pAIT H)))
        atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hArg
  have hScaled :
      Tendsto (fun H : ℕ => (1 / a ^ 2) *
        ((a * pAIT H) ^ 2 * Real.exp (-(a * pAIT H)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hKernel.const_mul (1 / a ^ 2)
  have hShape (H : ℕ) :
      (1 / a ^ 2) * ((a * pAIT H) ^ 2 * Real.exp (-(a * pAIT H))) =
        (pAIT H) ^ 2 * Real.exp (-(a * pAIT H)) := by
    field_simp [ne_of_gt ha]
  simpa only [hShape] using hScaled

/-- Only THIS rational Ward certificate is bounded by the volume envelope.
The coefficient bound and source-square bound both concern original objects. -/
theorem p4Q2PZ37AIT_rationalWardFloor_le_explicitVolumeBound
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    DAIT H beta ≤ (beta / 4) *
      ((pAIT H) ^ 2 * Real.exp (-(2 * beta * pAIT H))) := by
  have hCoefficient := p4Q2PZ37AIT_rationalSourceCoefficient_le_beta H beta hbeta
  have hVariance := p4Q2PZ37AIS_originalSourceSecondMoment_le_countSquare H
  have hVarianceNonneg : 0 ≤ VAIT H :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2.le
  unfold p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor
  calc
    _ ≤ beta * Real.exp (-(2 * beta * pAIT H)) * ((pAIT H) ^ 2 / 4) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right hCoefficient (Real.exp_pos _).le)
        hVariance hVarianceNonneg (mul_nonneg hbeta (Real.exp_pos _).le)
    _ = _ := by ring

/-- Each fixed positive ORIGINAL coupling has a rational Ward certificate
whose amplitude tends to zero as H tends to infinity. This is a statement
about this certificate, not an upper bound on the actual negative transfer. -/
theorem p4Q2PZ37AIT_rationalWardFloor_tendsto_zero
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto (fun H : ℕ => DAIT H beta) atTop (𝓝 0) := by
  have hEnvelope :
      Tendsto (fun H : ℕ => (beta / 4) *
        ((pAIT H) ^ 2 * Real.exp (-(2 * beta * pAIT H)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (p4Q2PZ37AIT_originalCountSquareExp_tendsto_zero
        (2 * beta) (mul_pos (by norm_num) hbeta)).const_mul (beta / 4)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hEnvelope
    (fun H => (p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor_pos H beta hbeta).le)
    (fun H => p4Q2PZ37AIT_rationalWardFloor_le_explicitVolumeBound H beta hbeta.le)

/-- No positive number is a volume-uniform lower bound for THIS certificate.
No impossibility of another transfer estimate or certificate is asserted. -/
theorem p4Q2PZ37AIT_rationalWardFloor_no_uniformPositiveFloor
    (beta : ℝ) (hbeta : 0 < beta) :
    ¬ ∃ eta : ℝ, 0 < eta ∧ ∀ H : ℕ, eta ≤ DAIT H beta := by
  rintro ⟨eta, heta, hUniform⟩
  have hEventually : ∀ᶠ H : ℕ in atTop, DAIT H beta < eta :=
    (p4Q2PZ37AIT_rationalWardFloor_tendsto_zero beta hbeta).eventually
      (gt_mem_nhds heta)
  obtain ⟨H, hH⟩ := hEventually.exists
  exact (not_lt_of_ge (hUniform H)) hH

/-- At the unchanged original beta0, positivity holds separately at each
finite volume while this certificate has no volume-uniform positive floor. -/
theorem p4Q2PZ37AIT_fixedRationalWardFloor_vanishing_certificate :
    (∀ H : ℕ, 0 < DAIT H p4Q2PZ37ADC_fixedCoupling) ∧
      Tendsto (fun H : ℕ => DAIT H p4Q2PZ37ADC_fixedCoupling) atTop (𝓝 0) ∧
      ¬ ∃ eta : ℝ, 0 < eta ∧
        ∀ H : ℕ, eta ≤ DAIT H p4Q2PZ37ADC_fixedCoupling := by
  exact ⟨(fun H => p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor_pos H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos),
    p4Q2PZ37AIT_rationalWardFloor_tendsto_zero
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos,
    p4Q2PZ37AIT_rationalWardFloor_no_uniformPositiveFloor
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos⟩

end PZ37AITVolumeDecay


/-- Eventual half Haar for each fixed positive coupling coexists with a
vanishing scalar certificate. Neither a common configuration-space limit
nor a spectral or coercivity conclusion is part of this statement. -/
theorem p4Q2PZ37AIT_eventualHalfHaar_vanishingFloor_certificate
    (beta : ℝ) (hbeta : 0 < beta) :
    (∃ N : ℕ, ∀ K : ℕ, N ≤ K →
      (1 / 2 : ℝ) ≤ Measure.real
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure K 2)
        (p4Q2PZ37AIG_originalNegativeTransferRegion K beta)) ∧
      Filter.Tendsto
        (fun K : ℕ => p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor K beta)
        Filter.atTop (𝓝 0) ∧
      ¬ ∃ eta : ℝ, 0 < eta ∧ ∀ K : ℕ,
        eta ≤ p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor K beta :=
  ⟨p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half_eventually beta hbeta,
    p4Q2PZ37AIT_rationalWardFloor_tendsto_zero beta hbeta,
    p4Q2PZ37AIT_rationalWardFloor_no_uniformPositiveFloor beta hbeta⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIT_real_rationalCoefficient_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIT_real_rationalCoefficient_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIT_real_rationalCoefficient_le_beta
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIT_real_previousCoefficient_lt_rational
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIT_real_centeredLaplace_rationalQuadraticUpper
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIT_real_signedLaplace_rationalUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_rationalSourceCoefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_rationalSourceCoefficient_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_rationalSourceCoefficient_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_rationalSourceCoefficient_le_beta
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_previousCoefficient_lt_rationalSourceCoefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalRightWeightedTransfer_rationalQuadraticUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_sourceNonpositiveRationalWardFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_previousWardFloor_lt_rationalWardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalRightWeightedTransfer_le_negativeRationalWardVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalTransfer_le_negativeRationalWardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalNegativeMargin_rationalWardRatio_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalSingleLinkPartition_antitone
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalCrossingPartition_antitone
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalCrossingPartition_le_unitGaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_volumeGrowingCouplingCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_volumeGrowingCutoff_eq_cubic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_volumeGrowingCutoff_ge_seven
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_volumeGrowingCouplingCutoff_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_volumeGrowingCutoff_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_volumeGrowingCutoff_ge_cast
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_eventually_le_volumeGrowingCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_rationalBudget_le_expHalf_of_le_cutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalRationalMarginFactor_le_one_of_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalRationalMarginFactor_le_one_of_one_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalRationalMarginFactor_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalRationalMarginFactor_le_one_of_le_seven
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_twice_originalNegativeMargin_le_rationalWardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalNegativeMargin_lt_rationalWardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalSource_nonpos_subset_fullNegativeRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalFullNegativeRegion_Haar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half_of_le_seven
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half_at_cutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalFullNegativeRegion_realHaar_half_eventually
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_rationalWardFloor_exactVolume
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalCount_tendsto_atTop
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_originalCountSquareExp_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_rationalWardFloor_le_explicitVolumeBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_rationalWardFloor_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_rationalWardFloor_no_uniformPositiveFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_fixedRationalWardFloor_vanishing_certificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIT_eventualHalfHaar_vanishingFloor_certificate
