import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullKernelPairLaplaceNormV5_PZ37ALD
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALE — genuine original pair-Haar second moment positive floor

The original SU(2) Wilson temporal crossing ACTION C_H(A,B) has the
pinned proven pointwise bound C_H(A,B) <= 2*ell_H (ell_H true link count).
For beta>=0 this gives, for the ACTUAL exponential crossing KERNEL,
 Kcross_H(beta,A,B) >= exp(-2*beta*ell_H) > 0.

Independently, the ORIGINAL continuous centered Gauss-law source has
true normalized spatial Haar mean zero, and product Haar Fubini gives
 ∫ (f_H(A)+f_H(B))² d(mu_H×mu_H) = 2*V_H,
where V_H is the original AHN genuine Haar second moment > 0.

A genuine kernel-weighted integral comparison then proves
 M2pair_H(beta) >= 2*exp(-2*beta*ell_H)*V_H > 0
for every finite H and beta>=0. No exponential-crossing orthogonality
is falsely inferred from AHR's *linear crossing ACTION* identity.
Using ALD, the previously conditional strictly-improved ORIGINAL
physical Wilson transfer operator norm lower bound becomes unconditional
at beta>0, and the correction has an explicit positive finite-H floor.

No original model, Wilson kernel or source, Haar law, full-top projection,
negative event, AJA budget, pin, root, existing theorem or existing file
is altered. This finite-H floor decays with volume; it is NOT H-uniform
coercivity, a Hamiltonian or continuum mass gap, the original H22 r22
upper mass, nor proof of an original AJA witness or its nonexistence.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ALE_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ALE_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ALE_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ALE_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ALE_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ALE_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pairH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "KC" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "M2pair" => p4Q2PZ37ALC_originalPairCrossingSecondMoment H
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "PW" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2
    (by norm_num)

local instance p4Q2PZ37ALE_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- A named bound for the unchanged exponential crossing KERNEL, not
a modified original operator or probability distribution. -/
def p4Q2PZ37ALE_originalCrossingKernelFloor (beta : ℝ) : ℝ :=
  Real.exp (-(2 * beta * ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ)))

local notation "kFloor" => p4Q2PZ37ALE_originalCrossingKernelFloor H

theorem p4Q2PZ37ALE_originalCrossingKernelFloor_pos (beta : ℝ) :
    0 < kFloor beta := by
  unfold p4Q2PZ37ALE_originalCrossingKernelFloor
  exact Real.exp_pos _

/-- True original crossing-action upper bound becomes a pointwise
lower bound for the true exponential crossing kernel at beta>=0. -/
theorem p4Q2PZ37ALE_originalCrossingKernel_ge_floor
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    kFloor beta ≤ KC beta A B := by
  unfold p4Q2PZ37ALE_originalCrossingKernelFloor
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann]
  apply Real.exp_le_exp.mpr
  have hAction :
      Cross A B ≤ 2 * ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_le_two_mul_length
      H 2 (by norm_num) A B
  have hScale := mul_le_mul_of_nonneg_left hAction hbeta
  nlinarith only [hScale]

/-- ACTUAL continuous centered ZW source has zero original Haar mean.
This follows from AGN's pointwise centering and AIW's original exact
Haar Wilson mean, rather than assuming a representative of an L² class. -/
theorem p4Q2PZ37ALE_originalCenteredSource_realHaarMean_zero :
    (∫ A : Cfg, fCont A ∂muH) = 0 := by
  have hW : Integrable (fun A : Cfg => W A) muH :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous
      H 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  calc
    (∫ A : Cfg, fCont A ∂muH) =
      ∫ A : Cfg, (W A - pH) / 2 ∂muH := by
        apply integral_congr_ae
        filter_upwards with A
        exact p4Q2PZ37AGN_originalCenteredContinuous_eq H A
    _ = ((∫ A : Cfg, W A ∂muH) - pH) / 2 := by
      rw [integral_div, integral_sub hW (integrable_const _)]
      simp
    _ = 0 := by
      rw [p4Q2PZ37AIW_originalSpatialWilsonAction_haarMean H]
      ring

/-- Integrability of the original two-boundary unweighted source
square before all product-Haar Fubini expansions. -/
theorem p4Q2PZ37ALE_originalPairSourceSquare_integrable :
    Integrable (fun P : Cfg × Cfg =>
      (fCont P.1 + fCont P.2) ^ 2) pairH := by
  have hf1 : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hf2 : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  exact ((hf1.add hf2).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Product-Haar integral of the first endpoint source square is the
unchanged one-boundary physical source variance. -/
theorem p4Q2PZ37ALE_originalPair_leftSourceSquare_eq_variance :
    (∫ P : Cfg × Cfg, (fCont P.1) ^ 2 ∂pairH) = Vsrc := by
  have hLeft : Integrable (fun P : Cfg × Cfg => (fCont P.1) ^ 2) pairH :=
    (((p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp
      continuous_fst).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  change (∫ P : Cfg × Cfg, (fCont P.1) ^ 2 ∂(Measure.prod muH muH)) = _
  rw [integral_prod _ hLeft]
  simp [p4Q2PZ37AHN_originalSource_HaarSecondMoment]

/-- Symmetric second-endpoint original Haar marginal. -/
theorem p4Q2PZ37ALE_originalPair_rightSourceSquare_eq_variance :
    (∫ P : Cfg × Cfg, (fCont P.2) ^ 2 ∂pairH) = Vsrc := by
  have hRight : Integrable (fun P : Cfg × Cfg => (fCont P.2) ^ 2) pairH :=
    (((p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp
      continuous_snd).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  change (∫ P : Cfg × Cfg, (fCont P.2) ^ 2 ∂(Measure.prod muH muH)) = _
  rw [integral_prod_symm _ hRight]
  simp [p4Q2PZ37AHN_originalSource_HaarSecondMoment]

/-- The unweighted cross term is ZERO for the actual two independent
original Haar boundaries; this is NOT a crossed-kernel orthogonality. -/
theorem p4Q2PZ37ALE_originalPair_unweightedSourceMixed_zero :
    (∫ P : Cfg × Cfg, fCont P.1 * fCont P.2 ∂pairH) = 0 := by
  have hf1 : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hf2 : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  have hMixed : Integrable (fun P : Cfg × Cfg =>
      fCont P.1 * fCont P.2) pairH :=
    (hf1.mul hf2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ P : Cfg × Cfg, fCont P.1 * fCont P.2 ∂(Measure.prod muH muH)) = 0
  rw [integral_prod _ hMixed]
  simp_rw [integral_const_mul]
  rw [p4Q2PZ37ALE_originalCenteredSource_realHaarMean_zero H]
  simp

/-- Original unweighted pair-Haar source-square is exactly twice the
genuine one-boundary physical source variance. Only the two endpoint
Haar random variables are independent; NOT the crossed Wilson kernel. -/
theorem p4Q2PZ37ALE_originalUnweightedPairSourceSquare_eq_twiceVariance :
    (∫ P : Cfg × Cfg,
      (fCont P.1 + fCont P.2) ^ 2 ∂pairH) = 2 * Vsrc := by
  have hf1 : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hf2 : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  have hLeft : Integrable (fun P : Cfg × Cfg => (fCont P.1) ^ 2) pairH :=
    (hf1.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRight : Integrable (fun P : Cfg × Cfg => (fCont P.2) ^ 2) pairH :=
    (hf2.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hMixed : Integrable (fun P : Cfg × Cfg =>
      fCont P.1 * fCont P.2) pairH :=
    (hf1.mul hf2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    (∫ P : Cfg × Cfg,
      (fCont P.1 + fCont P.2) ^ 2 ∂pairH) =
      ∫ P : Cfg × Cfg,
        ((fCont P.1) ^ 2 + (fCont P.2) ^ 2 +
          2 * (fCont P.1 * fCont P.2)) ∂pairH := by
        apply integral_congr_ae
        filter_upwards with P
        ring
    _ = (∫ P : Cfg × Cfg, (fCont P.1) ^ 2 ∂pairH) +
          (∫ P : Cfg × Cfg, (fCont P.2) ^ 2 ∂pairH) +
            2 * (∫ P : Cfg × Cfg, fCont P.1 * fCont P.2 ∂pairH) := by
      change
        (∫ P : Cfg × Cfg,
          (((fun Q : Cfg × Cfg => (fCont Q.1) ^ 2) +
            (fun Q : Cfg × Cfg => (fCont Q.2) ^ 2)) +
            (fun Q : Cfg × Cfg => 2 * (fCont Q.1 * fCont Q.2))) P ∂pairH) = _
      rw [integral_add (hLeft.add hRight) (hMixed.const_mul 2),
        integral_add hLeft hRight, integral_const_mul]
    _ = 2 * Vsrc := by
      rw [p4Q2PZ37ALE_originalPair_leftSourceSquare_eq_variance H,
        p4Q2PZ37ALE_originalPair_rightSourceSquare_eq_variance H,
        p4Q2PZ37ALE_originalPair_unweightedSourceMixed_zero H]
      ring

/-- Compare the genuine crossing-weighted second Haar moment to
the actual unweighted pair variance using the pointwise kernel floor. -/
theorem p4Q2PZ37ALE_originalPairSecondMoment_ge_floor_times_unweighted
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    kFloor beta *
      (∫ P : Cfg × Cfg,
        (fCont P.1 + fCont P.2) ^ 2 ∂pairH) ≤ M2pair beta := by
  have hS : Integrable (fun P : Cfg × Cfg =>
      (fCont P.1 + fCont P.2) ^ 2) pairH :=
    p4Q2PZ37ALE_originalPairSourceSquare_integrable H
  have hWeighted :
      Integrable (fun P : Cfg × Cfg =>
        KC beta P.1 P.2 *
          (fCont P.1 + fCont P.2) ^ 2) pairH :=
    p4Q2PZ37ALC_originalPairCrossingSecondMoment_integrable H beta
  have hBound (P : Cfg × Cfg) :
      kFloor beta * (fCont P.1 + fCont P.2) ^ 2 ≤
        KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2 :=
    mul_le_mul_of_nonneg_right
      (p4Q2PZ37ALE_originalCrossingKernel_ge_floor H beta hbeta P.1 P.2)
      (sq_nonneg _)
  have hInt :=
    integral_mono (hS.const_mul (kFloor beta)) hWeighted hBound
  rw [integral_const_mul] at hInt
  exact hInt

/-- Quantified genuine SU(2) crossing-weighted pair-Haar source-square
lower bound, entirely in ORIGINAL Wilson/Haar/source quantities. -/
theorem p4Q2PZ37ALE_originalPairSecondMoment_ge_explicitPositiveFloor
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    2 * kFloor beta * Vsrc ≤ M2pair beta := by
  have h := p4Q2PZ37ALE_originalPairSecondMoment_ge_floor_times_unweighted
    H beta hbeta
  rw [p4Q2PZ37ALE_originalUnweightedPairSourceSquare_eq_twiceVariance H] at h
  nlinarith only [h]

/-- Strictly positive TRUE crossing-weighted pair-Haar physical source
second moment at EVERY finite H and every nonnegative beta. -/
theorem p4Q2PZ37ALE_originalPairSecondMoment_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < M2pair beta := by
  have hf := p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta
  have hV := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hLower :=
    p4Q2PZ37ALE_originalPairSecondMoment_ge_explicitPositiveFloor H beta hbeta
  exact (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hf) hV).trans_le hLower

/-- New explicit quantitative TRUE physical Wilson norm floor using a
positive, verified finite-volume original source Haar variance. -/
theorem p4Q2PZ37ALE_originalPhysicalNorm_ge_explicitSourceVariance
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pH)) *
      (Zcross beta +
        (beta ^ 2 / 4) * (2 * kFloor beta * Vsrc)) ≤
      ‖PW beta hbeta‖ := by
  have hMoment :=
    p4Q2PZ37ALE_originalPairSecondMoment_ge_explicitPositiveFloor H beta hbeta
  have hFactor : 0 ≤ (beta ^ 2 / 4 : ℝ) := by positivity
  have hInner :
      Zcross beta +
        (beta ^ 2 / 4) * (2 * kFloor beta * Vsrc) ≤
      Zcross beta + (beta ^ 2 / 4) * M2pair beta := by
    exact add_le_add_left (mul_le_mul_of_nonneg_left hMoment hFactor) _
  exact (mul_le_mul_of_nonneg_left hInner
    (Real.exp_pos (-(beta * pH))).le).trans
      (p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_quadraticMoment
        H beta hbeta)

/-- ALD's former conditional strict gain over the AIW original physical
norm floor is now UNCONDITIONAL for every beta>0, at each finite H. -/
theorem p4Q2PZ37ALE_originalPhysicalNorm_strictly_gt_spatialMean
    (beta : ℝ) (hbeta : 0 < beta) :
    Real.exp (-(beta * pH)) * Zcross beta <
      ‖PW beta hbeta.le‖ :=
  p4Q2PZ37ALD_originalPhysicalNorm_strictly_gt_spatialMean_of_M2_pos
    H beta hbeta
    (p4Q2PZ37ALE_originalPairSecondMoment_pos H beta hbeta.le)

/-- Specialize the new unconditional physical norm strict gain to
original H22 and its unaltered fixed beta0 coupling. -/
theorem p4Q2PZ37ALE_originalH22_fixedCoupling_physicalNorm_strictGain :
    Real.exp (-(p4Q2PZ37ADC_fixedCoupling * (292008 : ℝ))) *
      p4Q2PZ37AIF_originalCrossingPartition 22
        p4Q2PZ37ADC_fixedCoupling <
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        22 2 (by norm_num) p4Q2PZ37ADC_fixedCoupling
          p4Q2PZ37ADC_fixedCoupling_pos.le‖ := by
  have h :=
    p4Q2PZ37ALE_originalPhysicalNorm_strictly_gt_spatialMean
      22 p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos
  rw [p4Q2PZ37AKX_originalH22_plaquetteCount_exact] at h
  exact h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalCrossingKernelFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalCrossingKernelFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalCrossingKernel_ge_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalCenteredSource_realHaarMean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalPairSourceSquare_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalPair_leftSourceSquare_eq_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalPair_rightSourceSquare_eq_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalPair_unweightedSourceMixed_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalUnweightedPairSourceSquare_eq_twiceVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalPairSecondMoment_ge_floor_times_unweighted
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalPairSecondMoment_ge_explicitPositiveFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalPairSecondMoment_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalPhysicalNorm_ge_explicitSourceVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalPhysicalNorm_strictly_gt_spatialMean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALE_originalH22_fixedCoupling_physicalNorm_strictGain
