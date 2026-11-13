import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGenuineFourthMomentFloorV5_PZ37ALH
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALI — sharp iid original Haar fourth moment, no crossing independence

ALH proves E_(mu_H x mu_H) [(f(A)+f(B))^4] >= 4 V_H^2
by the probability-Jensen square identity. The TWO original independent
normalized boundary Haar variables, together with the already-certified
zero Haar mean of the unchanged centered ZW source, improve this to
  E[(f(A)+f(B))^4]
    = 2 E[f^4] + 6 (E[f^2])^2 >= 8 V_H^2.

The mixed cubic terms vanish by Fubini and E[f]=0; no vanishing of the
crossing-KERNEL-weighted mixed terms is asserted. The unchanged original
crossing exponential kernel has the genuinely certified uniform finite-H
floor k_H(beta) > 0. Therefore the actual crossing-weighted fourth source
moment satisfies M4pair_H(beta) >= 8 k_H(beta) V_H^2.

This sharpens ALH's previous k_H(beta)*(2 V_H)^2 = 4 k_H(beta)V_H^2.
The ALF true identity box further gives M4pair >= 8 k_H vBox_H^2.
Those original measurements tighten the *unchanged* full physical SU(2)
Wilson one-slab norm via ALH's exact fourth-Laplace bound and true operator
norm comparison, including the original H=22 beta0 specialization.

Finite-volume norm floors do NOT give H-uniform excited coercivity,
H22 negative Haar upper r22, AJA classification or continuum YM gap.
No physical definitions, existing Lean modules, imports, mathematical
assumptions, pinned toolchain, public roots or workflows are modified.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ALI_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ALI_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ALI_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ALI_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ALI_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ALI_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pairH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "KC" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "M4pair" => p4Q2PZ37ALH_originalPairCrossingFourthMoment H
local notation "M2pair" => p4Q2PZ37ALC_originalPairCrossingSecondMoment H
local notation "kFloor" => p4Q2PZ37ALE_originalCrossingKernelFloor H
local notation "vBox" => p4Q2PZ37ALF_originalIdentityBoxVarianceFloor H
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "PW" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num)

local instance p4Q2PZ37ALI_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The original one-boundary true Haar fourth source moment, derived
from the unchanged continuous signed ZW source and normalized Haar. -/
def p4Q2PZ37ALI_originalSourceFourthHaarMoment : ℝ :=
  ∫ A : Cfg, (fCont A) ^ 4 ∂muH

local notation "U4" => p4Q2PZ37ALI_originalSourceFourthHaarMoment H

theorem p4Q2PZ37ALI_originalSourceFourth_integrable :
    Integrable (fun A : Cfg => (fCont A) ^ 4) muH := by
  exact ((p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.pow 4).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Ordinary Jensen/Cauchy variance-square estimate for the ORIGINAL
single Haar boundary. This uses no Gaussian moment hypothesis. -/
theorem p4Q2PZ37ALI_originalSourceFourth_ge_varianceSq :
    Vsrc ^ 2 ≤ U4 := by
  have hSecond : Integrable (fun A : Cfg => (fCont A) ^ 2) muH :=
    ((p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFourth := p4Q2PZ37ALI_originalSourceFourth_integrable H
  have hLower :
      Integrable (fun A : Cfg => (2 * Vsrc) * (fCont A) ^ 2 - Vsrc ^ 2) muH :=
    (hSecond.const_mul (2 * Vsrc)).sub (integrable_const _)
  have hPoint (A : Cfg) :
      (2 * Vsrc) * (fCont A) ^ 2 - Vsrc ^ 2 ≤
        (fCont A) ^ 4 := by
    nlinarith only [sq_nonneg ((fCont A) ^ 2 - Vsrc)]
  have hCmp := integral_mono hLower hFourth hPoint
  have hMean : (∫ A : Cfg, (fCont A) ^ 2 ∂muH) = Vsrc := by
    rfl
  have hLowerValue :
      (∫ A : Cfg, (2 * Vsrc) * (fCont A) ^ 2 - Vsrc ^ 2 ∂muH) =
        Vsrc ^ 2 := by
    rw [integral_sub (hSecond.const_mul (2 * Vsrc))
      (integrable_const _), integral_const_mul, hMean]
    simp
    ring
  rw [hLowerValue] at hCmp
  exact hCmp

/-- The genuine left Haar fourth marginal on the original pair
probability equals the single original fourth moment. -/
theorem p4Q2PZ37ALI_originalPairLeftFourth_eq_sourceFourth :
    (∫ P : Cfg × Cfg, (fCont P.1) ^ 4 ∂pairH) = U4 := by
  have hLeft : Integrable (fun P : Cfg × Cfg => (fCont P.1) ^ 4) pairH :=
    (((p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp
      continuous_fst).pow 4).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  change (∫ P : Cfg × Cfg, (fCont P.1) ^ 4 ∂(Measure.prod muH muH)) = _
  rw [integral_prod _ hLeft]
  simp [p4Q2PZ37ALI_originalSourceFourthHaarMoment]

/-- The true right Haar fourth marginal, with the original measure. -/
theorem p4Q2PZ37ALI_originalPairRightFourth_eq_sourceFourth :
    (∫ P : Cfg × Cfg, (fCont P.2) ^ 4 ∂pairH) = U4 := by
  have hRight : Integrable (fun P : Cfg × Cfg => (fCont P.2) ^ 4) pairH :=
    (((p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp
      continuous_snd).pow 4).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  change (∫ P : Cfg × Cfg, (fCont P.2) ^ 4 ∂(Measure.prod muH muH)) = _
  rw [integral_prod_symm _ hRight]
  simp [p4Q2PZ37ALI_originalSourceFourthHaarMoment]

/-- Both original boundary Haar variables are independent in PRODUCT
HAAR, so their two squares have expected product V_H^2. This is not
independence under the crossing kernel. -/
theorem p4Q2PZ37ALI_originalPairSquaresMixed_eq_varianceSq :
    (∫ P : Cfg × Cfg, (fCont P.1) ^ 2 * (fCont P.2) ^ 2 ∂pairH) =
      Vsrc ^ 2 := by
  have hf1 : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hf2 : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  have hMixed : Integrable (fun P : Cfg × Cfg =>
      (fCont P.1) ^ 2 * (fCont P.2) ^ 2) pairH :=
    ((hf1.pow 2).mul (hf2.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ P : Cfg × Cfg, (fCont P.1) ^ 2 * (fCont P.2) ^ 2
    ∂(Measure.prod muH muH)) = Vsrc ^ 2
  rw [integral_prod _ hMixed]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]
  change (∫ A : Cfg, (fCont A) ^ 2 ∂muH) *
    (∫ B : Cfg, (fCont B) ^ 2 ∂muH) = Vsrc ^ 2
  change Vsrc * Vsrc = Vsrc ^ 2
  ring

/-- Left-cubic/right-linear unweighted mixed Haar term is zero.
Only the right boundary's actual centered Haar mean is used. -/
theorem p4Q2PZ37ALI_originalPairCubeLeftRight_zero :
    (∫ P : Cfg × Cfg, (fCont P.1) ^ 3 * fCont P.2 ∂pairH) = 0 := by
  have hf1 : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hf2 : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  have hMixed : Integrable (fun P : Cfg × Cfg =>
      (fCont P.1) ^ 3 * fCont P.2) pairH :=
    ((hf1.pow 3).mul hf2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ P : Cfg × Cfg, (fCont P.1) ^ 3 * fCont P.2
    ∂(Measure.prod muH muH)) = 0
  rw [integral_prod _ hMixed]
  simp_rw [integral_const_mul]
  rw [p4Q2PZ37ALE_originalCenteredSource_realHaarMean_zero H]
  simp

/-- Left-linear/right-cubic unweighted mixed Haar term vanishes.
Here the original left Haar mean is zero, not the third moment. -/
theorem p4Q2PZ37ALI_originalPairLeftCubeRight_zero :
    (∫ P : Cfg × Cfg, fCont P.1 * (fCont P.2) ^ 3 ∂pairH) = 0 := by
  have hf1 : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hf2 : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  have hMixed : Integrable (fun P : Cfg × Cfg =>
      fCont P.1 * (fCont P.2) ^ 3) pairH :=
    (hf1.mul (hf2.pow 3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ P : Cfg × Cfg, fCont P.1 * (fCont P.2) ^ 3
    ∂(Measure.prod muH muH)) = 0
  rw [integral_prod_symm _ hMixed]
  simp_rw [integral_mul_const]
  rw [p4Q2PZ37ALE_originalCenteredSource_realHaarMean_zero H]
  simp

/-- TRUE product-Haar iid fourth-convolution identity. The integrands
are expanded only inside the UNWEIGHTED original pair Haar integral.
This identity is deliberately not promoted to a crossing-weighted
mixed-term identity, where such factorization has not been proved. -/
theorem p4Q2PZ37ALI_originalUnweightedPairFourth_eq_twoU4_plus_sixV2 :
    (∫ P : Cfg × Cfg,
      (fCont P.1 + fCont P.2) ^ 4 ∂pairH) =
      2 * U4 + 6 * Vsrc ^ 2 := by
  let F4 : Cfg × Cfg → ℝ := fun P => (fCont P.1) ^ 4
  let F31 : Cfg × Cfg → ℝ := fun P => 4 * ((fCont P.1) ^ 3 * fCont P.2)
  let F22 : Cfg × Cfg → ℝ := fun P => 6 * ((fCont P.1) ^ 2 * (fCont P.2) ^ 2)
  let F13 : Cfg × Cfg → ℝ := fun P => 4 * (fCont P.1 * (fCont P.2) ^ 3)
  let F04 : Cfg × Cfg → ℝ := fun P => (fCont P.2) ^ 4
  have hf1 : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hf2 : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  have hF4 : Integrable F4 pairH :=
    (hf1.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hF31 : Integrable F31 pairH :=
    (((hf1.pow 3).mul hf2).const_mul 4).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hF22 : Integrable F22 pairH :=
    (((hf1.pow 2).mul (hf2.pow 2)).const_mul 6).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hF13 : Integrable F13 pairH :=
    ((hf1.mul (hf2.pow 3)).const_mul 4).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hF04 : Integrable F04 pairH :=
    (hf2.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hF41 : Integrable (fun P => F4 P + F31 P) pairH := hF4.add hF31
  have hF42 : Integrable (fun P => F4 P + F31 P + F22 P) pairH :=
    hF41.add hF22
  have hF43 : Integrable (fun P => F4 P + F31 P + F22 P + F13 P) pairH :=
    hF42.add hF13
  have hEq1 :
      (∫ P : Cfg × Cfg, F4 P + F31 P ∂pairH) =
      (∫ P : Cfg × Cfg, F4 P ∂pairH) +
      (∫ P : Cfg × Cfg, F31 P ∂pairH) := by
    simpa only [Pi.add_apply] using (integral_add hF4 hF31)
  have hEq2 :
      (∫ P : Cfg × Cfg, F4 P + F31 P + F22 P ∂pairH) =
      (∫ P : Cfg × Cfg, F4 P + F31 P ∂pairH) +
      (∫ P : Cfg × Cfg, F22 P ∂pairH) := by
    simpa only [Pi.add_apply] using (integral_add hF41 hF22)
  have hEq3 :
      (∫ P : Cfg × Cfg, F4 P + F31 P + F22 P + F13 P ∂pairH) =
      (∫ P : Cfg × Cfg, F4 P + F31 P + F22 P ∂pairH) +
      (∫ P : Cfg × Cfg, F13 P ∂pairH) := by
    simpa only [Pi.add_apply] using (integral_add hF42 hF13)
  have hEq4 :
      (∫ P : Cfg × Cfg,
        F4 P + F31 P + F22 P + F13 P + F04 P ∂pairH) =
      (∫ P : Cfg × Cfg, F4 P + F31 P + F22 P + F13 P ∂pairH) +
      (∫ P : Cfg × Cfg, F04 P ∂pairH) := by
    simpa only [Pi.add_apply] using (integral_add hF43 hF04)
  have hF4Val : (∫ P : Cfg × Cfg, F4 P ∂pairH) = U4 :=
    p4Q2PZ37ALI_originalPairLeftFourth_eq_sourceFourth H
  have hF31Val : (∫ P : Cfg × Cfg, F31 P ∂pairH) = 0 := by
    dsimp [F31]
    rw [integral_const_mul,
      p4Q2PZ37ALI_originalPairCubeLeftRight_zero H]
    ring
  have hF22Val : (∫ P : Cfg × Cfg, F22 P ∂pairH) = 6 * Vsrc ^ 2 := by
    dsimp [F22]
    rw [integral_const_mul,
      p4Q2PZ37ALI_originalPairSquaresMixed_eq_varianceSq H]
  have hF13Val : (∫ P : Cfg × Cfg, F13 P ∂pairH) = 0 := by
    dsimp [F13]
    rw [integral_const_mul,
      p4Q2PZ37ALI_originalPairLeftCubeRight_zero H]
    ring
  have hF04Val : (∫ P : Cfg × Cfg, F04 P ∂pairH) = U4 :=
    p4Q2PZ37ALI_originalPairRightFourth_eq_sourceFourth H
  calc
    (∫ P : Cfg × Cfg, (fCont P.1 + fCont P.2) ^ 4 ∂pairH) =
      (∫ P : Cfg × Cfg,
        F4 P + F31 P + F22 P + F13 P + F04 P ∂pairH) := by
        apply integral_congr_ae
        filter_upwards with P
        dsimp [F4, F31, F22, F13, F04]
        ring
    _ = (∫ P : Cfg × Cfg, F4 P ∂pairH) +
        (∫ P : Cfg × Cfg, F31 P ∂pairH) +
        (∫ P : Cfg × Cfg, F22 P ∂pairH) +
        (∫ P : Cfg × Cfg, F13 P ∂pairH) +
        (∫ P : Cfg × Cfg, F04 P ∂pairH) := by
          rw [hEq4, hEq3, hEq2, hEq1]
    _ = 2 * U4 + 6 * Vsrc ^ 2 := by
          rw [hF4Val, hF31Val, hF22Val, hF13Val, hF04Val]
          ring

/-- The sharper iid zero-mean TRUE original Haar convolution moment:
E[(f(A)+f(B))^4] >= 8 V_H² (rather than ALH's Jensen 4 V_H²).
This makes essential use of the original independent pair Haar. -/
theorem p4Q2PZ37ALI_originalUnweightedPairFourth_ge_eightVarianceSq :
    8 * Vsrc ^ 2 ≤
      (∫ P : Cfg × Cfg,
        (fCont P.1 + fCont P.2) ^ 4 ∂pairH) := by
  have hJensen := p4Q2PZ37ALI_originalSourceFourth_ge_varianceSq H
  have hExact :=
    p4Q2PZ37ALI_originalUnweightedPairFourth_eq_twoU4_plus_sixV2 H
  nlinarith only [hJensen, hExact]

/-- Under the original exponential crossing kernel, **do not**
factor weighted terms. Use its genuine pointwise floor and the
unweighted independent pair Haar to obtain twice ALH's fourth floor. -/
theorem p4Q2PZ37ALI_originalPairFourth_ge_eightVarianceSq
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    kFloor beta * (8 * Vsrc ^ 2) ≤ M4pair beta := by
  have hFourth :=
    p4Q2PZ37ALH_originalPairSourceFourth_integrable H
  have hWeighted :=
    p4Q2PZ37ALH_originalPairCrossingFourth_integrable H beta
  have hPoint (P : Cfg × Cfg) :
      kFloor beta * (fCont P.1 + fCont P.2) ^ 4 ≤
        KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 4 :=
    mul_le_mul_of_nonneg_right
      (p4Q2PZ37ALE_originalCrossingKernel_ge_floor H beta hbeta P.1 P.2)
      (by positivity)
  have hIntegrals :=
    integral_mono (hFourth.const_mul (kFloor beta)) hWeighted hPoint
  rw [integral_const_mul] at hIntegrals
  exact (mul_le_mul_of_nonneg_left
    (p4Q2PZ37ALI_originalUnweightedPairFourth_ge_eightVarianceSq H)
    (p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta).le).trans
      hIntegrals

/-- The same physical original Haar identity box gives an explicit
genuinely positive, doubled crossing-weighted fourth-moment floor. -/
theorem p4Q2PZ37ALI_originalPairFourth_ge_eightBoxSq
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    kFloor beta * (8 * vBox ^ 2) ≤ M4pair beta := by
  have hvPos := p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_pos H
  have hVPos := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hVar := p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_le_sourceVariance H
  have hFactor :
      0 ≤ (Vsrc - vBox) * (Vsrc + vBox) :=
    mul_nonneg (sub_nonneg.mpr hVar) (by linarith only [hvPos, hVPos])
  have hSq : 8 * vBox ^ 2 ≤ 8 * Vsrc ^ 2 := by
    nlinarith only [hFactor]
  exact (mul_le_mul_of_nonneg_left hSq
    (p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta).le).trans
      (p4Q2PZ37ALI_originalPairFourth_ge_eightVarianceSq H beta hbeta)

/-- Sharper explicit true Wilson physical one-slab norm.
The fourth correction improves ALH by a factor TWO while both
original spatial halfweights, original pair-Haar and ZW source remain. -/
theorem p4Q2PZ37ALI_originalPhysicalNorm_ge_enhancedFourthBox
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pH)) *
      (Zcross beta +
        (beta ^ 2 / 2) * (2 * kFloor beta * vBox) +
        (beta ^ 4 / 32) * (kFloor beta * (8 * vBox ^ 2))) ≤
      ‖PW beta hbeta‖ := by
  have hM2 :=
    p4Q2PZ37ALF_originalPairSecondMoment_ge_identityBoxFloor H beta hbeta
  have hM4 :=
    p4Q2PZ37ALI_originalPairFourth_ge_eightBoxSq H beta hbeta
  have hScaled2 :=
    mul_le_mul_of_nonneg_left hM2
      (show 0 ≤ (beta ^ 2 / 2 : ℝ) by positivity)
  have hScaled4 :=
    mul_le_mul_of_nonneg_left hM4
      (show 0 ≤ (beta ^ 4 / 32 : ℝ) by positivity)
  have hInner :
      Zcross beta +
        (beta ^ 2 / 2) * (2 * kFloor beta * vBox) +
        (beta ^ 4 / 32) * (kFloor beta * (8 * vBox ^ 2)) ≤
      Zcross beta +
        (beta ^ 2 / 2) * M2pair beta +
        (beta ^ 4 / 32) * M4pair beta := by
    linarith only [hScaled2, hScaled4]
  exact (mul_le_mul_of_nonneg_left hInner
    (Real.exp_pos (-(beta * pH))).le).trans
      (p4Q2PZ37ALH_originalPhysicalNorm_ge_genuineFourthMoment
        H beta hbeta)

/-- For beta>0 the new certified explicit lower bound is STRICTLY
stronger than ALH's earlier identity-box physical norm floor. -/
theorem p4Q2PZ37ALI_originalPhysicalNorm_strictly_gt_ALH_boxFloor
    (beta : ℝ) (hbeta : 0 < beta) :
    Real.exp (-(beta * pH)) *
      (Zcross beta +
        (beta ^ 2 / 2) * (2 * kFloor beta * vBox) +
        (beta ^ 4 / 32) * (kFloor beta * (2 * vBox) ^ 2)) <
      ‖PW beta hbeta.le‖ := by
  have hK := p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta
  have hV := p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_pos H
  have hBeta4 : 0 < (beta ^ 4 / 32 : ℝ) := by positivity
  have hDiff :
      0 < (beta ^ 4 / 32) * (kFloor beta * (4 * vBox ^ 2)) := by
    have hSq : 0 < (vBox : ℝ) ^ 2 := by positivity
    exact mul_pos hBeta4 (mul_pos hK (mul_pos (by norm_num) hSq))
  have hInner :
      Zcross beta +
        (beta ^ 2 / 2) * (2 * kFloor beta * vBox) +
        (beta ^ 4 / 32) * (kFloor beta * (2 * vBox) ^ 2) <
      Zcross beta +
        (beta ^ 2 / 2) * (2 * kFloor beta * vBox) +
        (beta ^ 4 / 32) * (kFloor beta * (8 * vBox ^ 2)) := by
    nlinarith only [hDiff]
  have hScale :=
    mul_lt_mul_of_pos_left hInner (Real.exp_pos (-(beta * pH)))
  exact hScale.trans_le
    (p4Q2PZ37ALI_originalPhysicalNorm_ge_enhancedFourthBox
      H beta hbeta.le)

/-- Exact ORIGINAL H=22, beta0 and 292008 plaquettes, with a
twofold stronger genuine fourth-Haar Wilson norm correction. -/
theorem p4Q2PZ37ALI_originalH22_fixedCoupling_physicalNorm_enhancedFourthBox :
    Real.exp (-(p4Q2PZ37ADC_fixedCoupling * (292008 : ℝ))) *
      (p4Q2PZ37AIF_originalCrossingPartition 22
          p4Q2PZ37ADC_fixedCoupling +
        (p4Q2PZ37ADC_fixedCoupling ^ 2 / 2) *
          (2 * p4Q2PZ37ALE_originalCrossingKernelFloor 22
            p4Q2PZ37ADC_fixedCoupling *
            p4Q2PZ37ALF_originalIdentityBoxVarianceFloor 22) +
        (p4Q2PZ37ADC_fixedCoupling ^ 4 / 32) *
          (p4Q2PZ37ALE_originalCrossingKernelFloor 22
            p4Q2PZ37ADC_fixedCoupling *
            (8 * p4Q2PZ37ALF_originalIdentityBoxVarianceFloor 22 ^ 2))) ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          22 2 (by norm_num) p4Q2PZ37ADC_fixedCoupling
            p4Q2PZ37ADC_fixedCoupling_pos.le‖ := by
  have h :=
    p4Q2PZ37ALI_originalPhysicalNorm_ge_enhancedFourthBox
      22 p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
  rw [p4Q2PZ37AKX_originalH22_plaquetteCount_exact] at h
  exact h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalSourceFourthHaarMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalSourceFourth_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalSourceFourth_ge_varianceSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalPairLeftFourth_eq_sourceFourth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalPairRightFourth_eq_sourceFourth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalPairSquaresMixed_eq_varianceSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalPairCubeLeftRight_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalPairLeftCubeRight_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalUnweightedPairFourth_eq_twoU4_plus_sixV2
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalUnweightedPairFourth_ge_eightVarianceSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalPairFourth_ge_eightVarianceSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalPairFourth_ge_eightBoxSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalPhysicalNorm_ge_enhancedFourthBox
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalPhysicalNorm_strictly_gt_ALH_boxFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALI_originalH22_fixedCoupling_physicalNorm_enhancedFourthBox
