import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalConvexChordQuarticRemainderV5_PZ37AID
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIE — original source Haar-Laplace quantitative anticorrelation

The full original spatial product Haar, continuous representative of the
physical centered ZW source, and its proven strictly positive second moment
are retained. This leaf proves the genuine signed Haar source Laplace integral
is negative at every positive coupling, with an explicit nonzero quantitative
variance floor, including the unchanged original beta0.

The next crossing/Haar convolution step is NOT assumed or asserted. No claim
about the actual physical one-slab transfer sign follows without that step.
All physical definitions, original halfweights, typed histories, canonical
root, fixed Lean/mathlib and CI workflows remain unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Quantitative scalar negative exponential covariance, on a bounded interval.
Neither the source nor the exponential argument is assumed nonnegative. -/
theorem p4Q2PZ37AIE_real_centeredLaplace_quadraticUpper
    (beta c x : ℝ) (hbeta : 0 ≤ beta) (hc : 0 ≤ c)
    (hx : |x| ≤ c) :
    x * (Real.exp (-(beta * x)) - 1) ≤
      -(beta * Real.exp (-(beta * c)) * x ^ 2) := by
  have hbetaC : 0 ≤ beta * c := mul_nonneg hbeta hc
  have hDisc : Real.exp (-(beta * c)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hbetaC)
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
    have hMult := mul_le_mul_of_nonneg_left hProd hx0
    have hCore :
        x * (Real.exp (-(beta * x)) - 1) ≤
          -(beta * x ^ 2 * Real.exp (-(beta * x))) := by
      nlinarith only [hMult]
    have hBetaX : beta * x ≤ beta * c :=
      mul_le_mul_of_nonneg_left (abs_le.mp hx).2 hbeta
    have hExp : Real.exp (-(beta * c)) ≤ Real.exp (-(beta * x)) :=
      Real.exp_le_exp.mpr (by linarith only [hBetaX])
    have hScaled : beta * x ^ 2 * Real.exp (-(beta * c)) ≤
        beta * x ^ 2 * Real.exp (-(beta * x)) :=
      mul_le_mul_of_nonneg_left hExp (by positivity)
    calc
      x * (Real.exp (-(beta * x)) - 1) ≤
          -(beta * x ^ 2 * Real.exp (-(beta * x))) := hCore
      _ ≤ -(beta * x ^ 2 * Real.exp (-(beta * c))) := neg_le_neg hScaled
      _ = -(beta * Real.exp (-(beta * c)) * x ^ 2) := by ring
  · have hEx : -(beta * x) + 1 ≤ Real.exp (-(beta * x)) :=
      Real.add_one_le_exp (-(beta * x))
    have hMult := mul_le_mul_of_nonpos_left hEx hx0
    have hCore :
        x * (Real.exp (-(beta * x)) - 1) ≤ -(beta * x ^ 2) := by
      nlinarith only [hMult]
    have hScaled :
        beta * x ^ 2 * Real.exp (-(beta * c)) ≤ beta * x ^ 2 := by
      calc
        beta * x ^ 2 * Real.exp (-(beta * c)) ≤ beta * x ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hDisc (by positivity)
        _ = beta * x ^ 2 := by ring
    calc
      x * (Real.exp (-(beta * x)) - 1) ≤ -(beta * x ^ 2) := hCore
      _ ≤ -(beta * x ^ 2 * Real.exp (-(beta * c))) := neg_le_neg hScaled
      _ = -(beta * Real.exp (-(beta * c)) * x ^ 2) := by ring

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIE_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIE_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIE_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIE_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIE_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AIE_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Genuine Haar-Laplace transform of the SAME physical source's continuous
representative. No alternative measure, source, or independent approximation. -/
def p4Q2PZ37AIE_originalCenteredSourceLaplace (beta : ℝ) : ℝ :=
  ∫ A : Cfg, fCont A * Real.exp (-(beta * fCont A)) ∂muH

local notation "LaplaceSrc" => p4Q2PZ37AIE_originalCenteredSourceLaplace H

theorem p4Q2PZ37AIE_originalCenteredSourceLaplace_integrable
    (beta : ℝ) :
    Integrable (fun A : Cfg => fCont A * Real.exp (-(beta * fCont A))) muH := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hArg : Continuous (fun A : Cfg => -(beta * fCont A)) :=
    (continuous_const.mul hf).neg
  exact (hf.mul (Real.continuous_exp.comp hArg)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Subtracting the source Haar mean changes no signed Laplace integral.
The already proved original source has exactly zero Haar mean. -/
theorem p4Q2PZ37AIE_originalCenteredSourceLaplace_eq_centeredDifference
    (beta : ℝ) :
    LaplaceSrc beta =
      ∫ A : Cfg, fCont A * (Real.exp (-(beta * fCont A)) - 1) ∂muH := by
  have hf : Integrable (fun A : Cfg => fCont A) muH :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hExp := p4Q2PZ37AIE_originalCenteredSourceLaplace_integrable H beta
  have hSubtract :
      (∫ A : Cfg, fCont A * (Real.exp (-(beta * fCont A)) - 1) ∂muH) =
        (∫ A : Cfg, fCont A * Real.exp (-(beta * fCont A)) ∂muH) -
          (∫ A : Cfg, fCont A ∂muH) := by
    calc
      (∫ A : Cfg, fCont A * (Real.exp (-(beta * fCont A)) - 1) ∂muH) =
          ∫ A : Cfg,
            fCont A * Real.exp (-(beta * fCont A)) - fCont A ∂muH := by
        apply integral_congr_ae
        filter_upwards with A
        ring
      _ = (∫ A : Cfg, fCont A * Real.exp (-(beta * fCont A)) ∂muH) -
          (∫ A : Cfg, fCont A ∂muH) := integral_sub hExp hf
  rw [hSubtract, p4Q2PZ37AHP_originalSource_mean_zero H, sub_zero]
  rfl

/-- Non-asymptotic negative variance certificate for the genuine original
source's Haar Laplace transform, for every nonnegative coupling. -/
theorem p4Q2PZ37AIE_originalCenteredSourceLaplace_le_negativeVariance
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    LaplaceSrc beta ≤
      -(beta * Real.exp (-(beta * (pH / 2))) * Vsrc) := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hDiff : Integrable
      (fun A : Cfg => fCont A * (Real.exp (-(beta * fCont A)) - 1)) muH := by
    have hArg : Continuous (fun A : Cfg => -(beta * fCont A)) :=
      (continuous_const.mul hf).neg
    exact (hf.mul ((Real.continuous_exp.comp hArg).sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSq : Integrable (fun A : Cfg => (fCont A) ^ 2) muH :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCount : 0 ≤ pH / 2 := div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num)
  calc
    LaplaceSrc beta =
        ∫ A : Cfg, fCont A * (Real.exp (-(beta * fCont A)) - 1) ∂muH :=
      p4Q2PZ37AIE_originalCenteredSourceLaplace_eq_centeredDifference H beta
    _ ≤ ∫ A : Cfg,
          (-(beta * Real.exp (-(beta * (pH / 2))))) * (fCont A) ^ 2 ∂muH := by
      apply integral_mono hDiff (hSq.const_mul _)
      intro A
      convert p4Q2PZ37AIE_real_centeredLaplace_quadraticUpper
        beta (pH / 2) (fCont A) hbeta hCount
          (p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A) using 1 <;> ring
    _ = -(beta * Real.exp (-(beta * (pH / 2))) * Vsrc) := by
      rw [integral_const_mul]
      unfold p4Q2PZ37AHN_originalSource_HaarSecondMoment
      ring

/-- Strictly negative signed Haar Laplace transform for every positive
coupling. Strictness comes from the EXISTING true positive Haar variance. -/
theorem p4Q2PZ37AIE_originalCenteredSourceLaplace_neg
    (beta : ℝ) (hbeta : 0 < beta) : LaplaceSrc beta < 0 := by
  have hVariance := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hProduct : 0 < beta * Real.exp (-(beta * (pH / 2))) * Vsrc :=
    mul_pos (mul_pos hbeta (Real.exp_pos _)) hVariance
  exact (p4Q2PZ37AIE_originalCenteredSourceLaplace_le_negativeVariance
    H beta hbeta.le).trans_lt (neg_neg_of_pos hProduct)

/-- The unchanged original beta0 has a strict certified negative genuine
source-only Laplace Haar correlation, with the exact finite-volume variance. -/
theorem p4Q2PZ37AIE_originalFixedCenteredSourceLaplace_neg :
    LaplaceSrc beta0 < 0 :=
  p4Q2PZ37AIE_originalCenteredSourceLaplace_neg
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos

/-- Fixed-beta quantitative negative bound, without numerical source values. -/
theorem p4Q2PZ37AIE_originalFixedCenteredSourceLaplace_le_negativeVariance :
    LaplaceSrc beta0 ≤
      -(beta0 * Real.exp (-(beta0 * (pH / 2))) * Vsrc) :=
  p4Q2PZ37AIE_originalCenteredSourceLaplace_le_negativeVariance
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIE_real_centeredLaplace_quadraticUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIE_originalCenteredSourceLaplace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIE_originalCenteredSourceLaplace_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIE_originalCenteredSourceLaplace_eq_centeredDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIE_originalCenteredSourceLaplace_le_negativeVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIE_originalCenteredSourceLaplace_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIE_originalFixedCenteredSourceLaplace_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIE_originalFixedCenteredSourceLaplace_le_negativeVariance
