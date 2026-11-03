import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPerronOneLinkChordModulusV5_PZ37AEN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEN — sharpened Perron bound from the TRUE Haar L² normalization

The previous AEN module used the AEK global pointwise ceiling
to certify ∫ V_H ≤ k_H⁻¹, and obtained the explicit fixed-H
Perron chord variation 13*beta0*k_H⁻².

The actual spatial-slice Haar law is a probability measure, the
original physical Perron top vector V_H has Haar L² norm exactly one,
and the canonical L² constant-one vector also has norm one.
Consequently Cauchy–Schwarz gives the SHARPER ∫ V_H ≤ 1.

This improves the genuine original Perron variation to
  |Omega_H(B[e↦g]) - Omega_H(B[e↦h])|
    ≤ 13*beta0*k_H⁻¹ * d_J(g,h)
for every finite H, with no new assumptions. The exact original
D_H second-boundary single-link equality carries this coefficient
unchanged to the physical two-boundary metric.

The coefficient remains H-dependent through the genuinely original
Wilson kernel floor k_H; no H-uniform coercivity or continuum gap
is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance

local instance p4Q2PZ37AENsharp_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AENsharp_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AENsharp_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AENsharp_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AENsharp_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "Replace" =>
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) b0 hb0
local notation "lambda" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖
local notation "k" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0

local instance p4Q2PZ37AENsharp_links : Fintype Link := Fintype.ofFinite _

/-- The normalized TRUE nonnegative Perron Haar L² vector obeys
the sharp probability-Haar Cauchy–Schwarz mass ceiling ∫ V_H ≤ 1.
No normalized posterior or alternate density is substituted. -/
theorem p4Q2PZ37AEN_originalNonnegativeVacuum_HaarIntegral_le_one :
    (∫ A : Cfg,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) b0 hb0).1 A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) ≤ 1 := by
  let μ : Measure Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) b0 hb0
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  have hMass : μ.real Set.univ = 1 := by
    simp [measureReal_def]
  have hConst :
      ‖Lp.const 2 μ (1 : ℝ)‖ = 1 := by
    have hNorm :=
      Lp.norm_const' (μ := μ) (p := (2 : ENNReal)) (c := (1 : ℝ))
        (by norm_num) (by norm_num)
    simpa [hMass, Real.norm_eq_abs] using hNorm
  have hVNorm :
      ‖(V.1 : Lp ℝ 2 μ)‖ = 1 := by
    change ‖V‖ = 1
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
        H 2 (by norm_num) b0 hb0
  have hIntegral :
      (∫ A : Cfg, V.1 A ∂μ) =
        inner ℝ (Lp.const 2 μ (1 : ℝ)) (V.1 : Lp ℝ 2 μ) := by
    exact (realL2_inner_const_one_eq_integral (V.1 : Lp ℝ 2 μ)).symm
  calc
    (∫ A : Cfg, V.1 A ∂μ) =
        inner ℝ (Lp.const 2 μ (1 : ℝ)) (V.1 : Lp ℝ 2 μ) := hIntegral
    _ ≤ ‖Lp.const 2 μ (1 : ℝ)‖ * ‖(V.1 : Lp ℝ 2 μ)‖ :=
      real_inner_le_norm _ _
    _ = 1 := by rw [hConst, hVNorm]; ring

/-- SHARPENED unconditional genuine physical Perron one-link
Lipschitz theorem: 13*beta0/k_H rather than 13*beta0/k_H².
Uses only the already proved AEM kernel chord bound, the true
Haar L² normalization and AEJ's genuine λ_H≥k_H floor. -/
theorem p4Q2PZ37AEN_originalContinuousVacuum_oneLinkSharpLipschitz
    (B : Cfg) (e : Link) (g h : G) :
    |Omega (Replace B e g) - Omega (Replace B e h)| ≤
      (13 * b0 * k⁻¹) * dJ g h := by
  let μ : Measure Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) b0 hb0
  let Bg := Replace B e g
  let Bh := Replace B e h
  have hk : 0 < k :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H b0
  have hLge : k ≤ lambda :=
    p4Q2PZ37AEJ_originalPhysicalTransfer_norm_ge_WilsonActionFloor
      H 2 (by norm_num) b0 hb0
  have hLpos : 0 < lambda := lt_of_lt_of_le hk hLge
  have hfInt : Integrable (fun A : Cfg => V.1 A) μ :=
    (Lp.memLp (V.1 : Lp ℝ 2 μ)).integrable (by norm_num)
  have hf0 : ∀ᵐ A ∂μ, 0 ≤ V.1 A := by
    simpa only [V, μ] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H 2 (by norm_num) b0 hb0)
  have hInt (D : Cfg) :
      Integrable (fun A : Cfg => V.1 A * K A D) μ := by
    simpa only [V, μ, K] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
        H 2 (by norm_num) b0 hb0
        ((V : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
          Lp ℝ 2 μ) D)
  have hPerron (D : Cfg) :
      lambda * Omega D = ∫ A : Cfg, V.1 A * K A D ∂μ := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel
        H 2 (by norm_num) b0 hb0 D
  have hMass :
      (∫ A : Cfg, V.1 A ∂μ) ≤ 1 := by
    simpa [V, μ] using
      (p4Q2PZ37AEN_originalNonnegativeVacuum_HaarIntegral_le_one H)
  have hC : 0 ≤ (13 * b0) * dJ g h := by
    exact mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 13) hb0)
      (p4Q2PZ37ADK_trueChordalDistance_nonneg g h)
  have hIntegral :
      |(∫ A : Cfg, V.1 A * K A Bg ∂μ) -
        (∫ A : Cfg, V.1 A * K A Bh ∂μ)| ≤
        ((13 * b0) * dJ g h) := by
    have hBound :=
      p4Q2PZ37AEN_real_weightedIntegral_absVariation
        μ (fun A : Cfg => V.1 A) (fun A => K A Bg) (fun A => K A Bh)
        ((13 * b0) * dJ g h) 1
        hfInt (hInt Bg) (hInt Bh) hf0
        (fun A =>
          p4Q2PZ37AEM_originalOneSlabKernel_unconditionalChordLipschitz
            H A B e g h)
        hMass hC
    simpa only [mul_one] using hBound
  have hScaled :
      lambda * |Omega Bg - Omega Bh| ≤
        ((13 * b0) * dJ g h) := by
    calc
      lambda * |Omega Bg - Omega Bh| =
          |lambda * Omega Bg - lambda * Omega Bh| := by
        rw [← mul_sub, abs_mul, abs_of_pos hLpos]
      _ = |(∫ A : Cfg, V.1 A * K A Bg ∂μ) -
          (∫ A : Cfg, V.1 A * K A Bh ∂μ)| := by
        rw [hPerron Bg, hPerron Bh]
      _ ≤ ((13 * b0) * dJ g h) := hIntegral
  have hFloor :
      k * |Omega Bg - Omega Bh| ≤ ((13 * b0) * dJ g h) := by
    calc
      k * |Omega Bg - Omega Bh| ≤
          lambda * |Omega Bg - Omega Bh| :=
        mul_le_mul_of_nonneg_right hLge (abs_nonneg _)
      _ ≤ ((13 * b0) * dJ g h) := hScaled
  have hDiv :
      |Omega Bg - Omega Bh| ≤ (((13 * b0) * dJ g h) / k) :=
    (le_div_iff₀ hk).2 hFloor
  calc
    |Omega Bg - Omega Bh| ≤ (((13 * b0) * dJ g h) / k) := hDiv
    _ = (13 * b0 * k⁻¹) * dJ g h := by
      rw [div_eq_mul_inv]
      ring

/-- Exact AEL/ADL physical one-link D_H calibration for the sharper
normalized original Perron L² coefficient. -/
theorem p4Q2PZ37AEN_originalContinuousVacuum_oneLinkSharpFullDistance
    (A B : Cfg) (e : Link) (g h : G) :
    |Omega (Replace B e g) - Omega (Replace B e h)| ≤
      (13 * b0 * k⁻¹) *
        p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
          (A, Replace B e g) (A, Replace B e h) := by
  rw [p4Q2PZ37AEL_originalFullDistance_secondBoundary_oneLink]
  exact p4Q2PZ37AEN_originalContinuousVacuum_oneLinkSharpLipschitz H B e g h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEN_originalNonnegativeVacuum_HaarIntegral_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEN_originalContinuousVacuum_oneLinkSharpLipschitz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEN_originalContinuousVacuum_oneLinkSharpFullDistance
