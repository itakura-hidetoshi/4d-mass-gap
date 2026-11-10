import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTwoStepAsymptoticBudgetV5_PZ37AJP
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJQ — genuine original Wilson reverse-Laplace top obstruction

AIE supplies a strictly negative centered SOURCE Haar Laplace moment with
negative exponent. Reflect its scalar inequality to control the positive
exponent *of the SAME original signed centered ZW source*. The genuine
halfweight Wilson transfer has the opposite weighted Haar average (AIF).

This is a logically independent route to show, for every finite H and
EVERY beta>0, that the ORIGINAL centered source does not lie in the complete
fixed top eigenspace of the SAME normalized SU(2) one-slab transfer.

All physical inputs, the full-top space, and the Haar L2/continuous
representative bridges remain unchanged. No numerical AJA finite-power
witness, nonzero transferred excitation, top simplicity, zero extra-top
residual, H-uniform gap, Hamiltonian gap, or continuum mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Reflect AIE's already proven negative-exponent scalar estimate,
without changing the source, its distribution, or the coupling sign. -/
theorem realHilbert_centered_reverseLaplace_scalar_lower_ajq
    (beta c x : ℝ) (hbeta : 0 ≤ beta) (hc : 0 ≤ c)
    (hx : |x| ≤ c) :
    beta * Real.exp (-(beta * c)) * x ^ 2 ≤
      x * (Real.exp (beta * x) - 1) := by
  have h :=
    p4Q2PZ37AIE_real_centeredLaplace_quadraticUpper
      beta c (-x) hbeta hc (by simpa only [abs_neg] using hx)
  simp only [mul_neg, neg_neg, even_two, Even.neg_pow] at h
  nlinarith only [h]

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysQ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgQ" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muQ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fQ" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fcQ" =>
  p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "WQ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "pQ" =>
  p4Q2PZ37AFZ_plaquetteCount H
local notation "VQ" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "TQ" =>
  decomposableOneSliceTransferIntegral H 2
local notation "PQ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "SQ" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "FQ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)

local instance p4Q2PZ37AJQ_probability : IsProbabilityMeasure muQ := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

local instance p4Q2PZ37AJQ_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJQ_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- Positive-exponent Haar Laplace moment of the EXACT original continuous
ZW source representative. Not a replacement vacuum expectation. -/
def p4Q2PZ37AJQ_originalPositiveSourceLaplace (beta : ℝ) : ℝ :=
  ∫ A : CfgQ, fcQ A * Real.exp (beta * fcQ A) ∂muQ

/-- Quantitative strict positive reverse-Laplace correlation for all
beta>0, using the unchanged genuine strictly positive Haar variance. -/
theorem p4Q2PZ37AJQ_originalPositiveSourceLaplace_lower
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    beta * Real.exp (-(beta * (pQ / 2))) * VQ ≤
      p4Q2PZ37AJQ_originalPositiveSourceLaplace H beta := by
  have hf : Continuous (fun A : CfgQ => fcQ A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hSq : Integrable (fun A : CfgQ => (fcQ A) ^ 2) muQ :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDiff : Integrable
      (fun A : CfgQ => fcQ A * (Real.exp (beta * fcQ A) - 1)) muQ := by
    have hArg : Continuous (fun A : CfgQ => beta * fcQ A) :=
      continuous_const.mul hf
    exact (hf.mul ((Real.continuous_exp.comp hArg).sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCentered :=
    p4Q2PZ37AIE_originalCenteredSourceLaplace_eq_centeredDifference H (-beta)
  have hCentered' :
      p4Q2PZ37AJQ_originalPositiveSourceLaplace H beta =
        ∫ A : CfgQ, fcQ A * (Real.exp (beta * fcQ A) - 1) ∂muQ := by
    simpa only [p4Q2PZ37AJQ_originalPositiveSourceLaplace,
      p4Q2PZ37AIE_originalCenteredSourceLaplace, neg_mul, neg_neg] using hCentered
  have hcount : 0 ≤ pQ / 2 := by
    exact div_nonneg (p4Q2PZ37AHN_count_pos H).le (by norm_num)
  calc
    beta * Real.exp (-(beta * (pQ / 2))) * VQ =
        ∫ A : CfgQ,
          (beta * Real.exp (-(beta * (pQ / 2)))) * (fcQ A) ^ 2 ∂muQ := by
          rw [integral_const_mul]
          rfl
    _ ≤ ∫ A : CfgQ,
          fcQ A * (Real.exp (beta * fcQ A) - 1) ∂muQ := by
          apply integral_mono (hSq.const_mul _) hDiff
          intro A
          exact realHilbert_centered_reverseLaplace_scalar_lower_ajq
            beta (pQ / 2) (fcQ A) hbeta hcount
            (p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A)
    _ = p4Q2PZ37AJQ_originalPositiveSourceLaplace H beta := hCentered'.symm

theorem p4Q2PZ37AJQ_originalPositiveSourceLaplace_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < p4Q2PZ37AJQ_originalPositiveSourceLaplace H beta := by
  have hV := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hprod : 0 < beta * Real.exp (-(beta * (pQ / 2))) * VQ :=
    mul_pos (mul_pos hbeta (Real.exp_pos _)) hV
  exact hprod.trans_le
    (p4Q2PZ37AJQ_originalPositiveSourceLaplace_lower H beta hbeta.le)

/-- AIF uses the original RIGHT halfweight; this is its same positive
weight multiplied by the unchanged centered ZW source on that boundary. -/
def p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral (beta : ℝ) : ℝ :=
  ∫ B : CfgQ, Real.exp ((beta / 2) * WQ B) * fcQ B ∂muQ

theorem p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral_eq
    (beta : ℝ) :
    p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral H beta =
      Real.exp (beta * (pQ / 2)) *
        p4Q2PZ37AJQ_originalPositiveSourceLaplace H beta := by
  have hFactor (B : CfgQ) :
      Real.exp ((beta / 2) * WQ B) =
        Real.exp (beta * (pQ / 2)) * Real.exp (beta * fcQ B) := by
    rw [← Real.exp_add]
    congr 1
    rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H B]
    ring
  unfold p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with B
  rw [hFactor B]
  ring

theorem p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral H beta := by
  rw [p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral_eq]
  exact mul_pos (Real.exp_pos _)
    (p4Q2PZ37AJQ_originalPositiveSourceLaplace_pos H beta hbeta)

/-- ORIGINAL normalized one-slab transfer cannot fix its OWN original
centered ZW source: the source has positive halfweight Haar correlation,
whereas its genuine Wilson transfer has strictly negative correlation. -/
theorem p4Q2PZ37AJQ_originalSource_not_fixed_all_positive
    (beta : ℝ) (hbeta : 0 < beta) :
    SQ beta hbeta.le fQ ≠ fQ := by
  let P : PhysQ →L[ℝ] PhysQ := PQ beta hbeta.le
  let S : PhysQ →L[ℝ] PhysQ := SQ beta hbeta.le
  have hNorm : 0 < ‖P‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le
  have hNormNe : ‖P‖ ≠ 0 := ne_of_gt hNorm
  intro hFix
  have hRaw : P fQ = ‖P‖ • fQ := by
    change ‖P‖⁻¹ • P fQ = fQ at hFix
    have h := congrArg (fun x : PhysQ => ‖P‖ • x) hFix
    rw [smul_smul, mul_inv_cancel₀ hNormNe, one_smul] at h
    exact h
  have hRep :
      (fun B : CfgQ => ((P fQ : PhysQ) : Lp ℝ 2 muQ) B) =ᵐ[muQ]
        (fun B : CfgQ => TQ beta fQ B) :=
    p4Q2PZ37AIW_originalPhysicalTransfer_coeFn H beta hbeta.le fQ
  have hSourceRep :
      (fun B : CfgQ => (fQ : Lp ℝ 2 muQ) B) =ᵐ[muQ] fcQ := by
    rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (μ := muQ) fcQ
  have hSmul :
      (fun B : CfgQ => ((‖P‖ • fQ : PhysQ) : Lp ℝ 2 muQ) B) =ᵐ[muQ]
        (fun B : CfgQ => ‖P‖ * (fQ : Lp ℝ 2 muQ) B) := by
    change (fun B : CfgQ => (‖P‖ • (fQ : Lp ℝ 2 muQ)) B) =ᵐ[muQ]
      (fun B : CfgQ => ‖P‖ * (fQ : Lp ℝ 2 muQ) B)
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (Lp.coeFn_smul ‖P‖ (fQ : Lp ℝ 2 muQ))
  rw [hRaw] at hRep
  have hFinal :
      (fun B : CfgQ => TQ beta fQ B) =ᵐ[muQ]
        (fun B : CfgQ => ‖P‖ * fcQ B) := by
    filter_upwards [hRep, hSmul, hSourceRep] with B hT hS hF
    calc
      TQ beta fQ B = ((‖P‖ • fQ : PhysQ) : Lp ℝ 2 muQ) B := hT.symm
      _ = ‖P‖ * (fQ : Lp ℝ 2 muQ) B := hS
      _ = ‖P‖ * fcQ B := by rw [hF]
  have hAvg :
      p4Q2PZ37AIF_originalRightWeightedTransferAverage H beta =
        ‖P‖ * p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral H beta := by
    unfold p4Q2PZ37AIF_originalRightWeightedTransferAverage
      p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral
    calc
      (∫ B : CfgQ, Real.exp ((beta / 2) * WQ B) * TQ beta fQ B ∂muQ) =
        ∫ B : CfgQ, Real.exp ((beta / 2) * WQ B) * (‖P‖ * fcQ B) ∂muQ := by
          apply integral_congr_ae
          filter_upwards [hFinal] with B hB
          rw [hB]
      _ = ∫ B : CfgQ,
          ‖P‖ * (Real.exp ((beta / 2) * WQ B) * fcQ B) ∂muQ := by
            apply integral_congr_ae
            filter_upwards with B
            ring
      _ = ‖P‖ * ∫ B : CfgQ,
          Real.exp ((beta / 2) * WQ B) * fcQ B ∂muQ := by
            rw [integral_const_mul]
  have hNeg := p4Q2PZ37AIF_originalRightWeightedTransferAverage_neg
    H beta hbeta
  have hPos := p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral_pos
    H beta hbeta
  rw [hAvg] at hNeg
  exact (not_lt_of_ge (mul_nonneg hNorm.le hPos.le)) hNeg

/-- The complete original top eigenspace, rather than a chosen vacuum
line, fails to contain the same original centered SU(2) Wilson source at
every beta>0. No AJA numerical small-budget certificate is assumed. -/
theorem p4Q2PZ37AJQ_originalSource_not_in_fullTop
    (beta : ℝ) (hbeta : 0 < beta) :
    fQ ∉ FQ beta hbeta.le := by
  intro hf
  exact (p4Q2PZ37AJQ_originalSource_not_fixed_all_positive H beta hbeta)
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
      H 2 (by norm_num) beta hbeta.le fQ).mp hf)

/-- A genuine all-positive-beta nontrivial source excited component:
the ORIGINAL untransferred source has nonzero full-top orthogonal
projection even though its existing AJA finite-power budget is not known. -/
theorem p4Q2PZ37AJQ_originalSource_orthogonal_ne_zero
    (beta : ℝ) (hbeta : 0 < beta) :
    ((FQ beta hbeta.le)ᗮ).starProjection fQ ≠ 0 := by
  let F : Submodule ℝ PhysQ := FQ beta hbeta.le
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed
    (SQ beta hbeta.le)).completeSpace_coe
  intro hzero
  have hsum : F.starProjection fQ + (Fᗮ).starProjection fQ = fQ :=
    F.starProjection_add_starProjection_orthogonal fQ
  have hproj : F.starProjection fQ = fQ := by
    rw [hzero, add_zero] at hsum
    exact hsum
  have hf : fQ ∈ F := by
    have hmem := F.starProjection_apply_mem fQ
    rw [hproj] at hmem
    exact hmem
  exact (p4Q2PZ37AJQ_originalSource_not_in_fullTop H beta hbeta) hf

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Audit the reflected scalar bound and all genuine physical declarations. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_centered_reverseLaplace_scalar_lower_ajq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJQ_originalPositiveSourceLaplace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJQ_originalPositiveSourceLaplace_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJQ_originalPositiveSourceLaplace_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJQ_originalPositiveWeightedSourceIntegral_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJQ_originalSource_not_fixed_all_positive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJQ_originalSource_not_in_fullTop
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJQ_originalSource_orthogonal_ne_zero
