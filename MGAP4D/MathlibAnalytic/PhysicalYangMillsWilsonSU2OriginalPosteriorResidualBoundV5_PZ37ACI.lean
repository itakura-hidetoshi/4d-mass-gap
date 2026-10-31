import MGAP4D.MathlibAnalytic.CompactPosteriorEnergyResidual
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorEnergyRegressionV5_PZ37ACH

/-!
# P4-Q2-PZ37ACI — quantitative actual posterior energy residual

The original determinant has slope between L=exp(-32*b) and U=exp(32*b).
Centering at b*(U+L) and integrating the continuous determinant error gives
  Var(d+b*(U+L)*E) <= b^2*(U-L)^2/4.
Consequently the SAME actual posterior regression residual satisfies
  0 <= Q-4*k^2 <= (2*k-b*L)*(b*U-2*k) <= b^2*(U-L)^2/4
and the last envelope is at most 1024*b^4*exp(64*b).

This is an unconditional H/link/right-configuration independent estimate
of the genuine residual, not a residual-smallness premise. The physical
FF receiver and ACH double regression then give a quantitative GI error.
No source residual, nonzero covariance magnitude, outer mass, uniform
physical coercivity or continuum reconstruction is assumed or inferred.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Cov" => CompactEnergyMismatchMoment.covariance μ
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local instance p4Q2PZ37ACI_res_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACI_res_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACI_res_countable : SecondCountableTopology G := specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACI_res_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACI_res_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACI_res_probability : IsProbabilityMeasure μ := normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

/-- A scalar bound for the actual posterior residual; no model replacement. -/
def p4Q2PZ37ACI_originalPosteriorResidualEnvelope (b : ℝ) : ℝ :=
  b ^ 2 / 4 * (Real.exp (32 * b) - Real.exp (-32 * b)) ^ 2
local notation "rho" => p4Q2PZ37ACI_originalPosteriorResidualEnvelope

theorem p4Q2PZ37ACI_originalPosteriorResidualEnvelope_nonneg (b : ℝ) : 0 ≤ rho b := by
  unfold p4Q2PZ37ACI_originalPosteriorResidualEnvelope
  positivity

/-- Explicit fourth-order control, valid also at b=0. -/
theorem p4Q2PZ37ACI_originalPosteriorResidualEnvelope_le_quartic
    (b : ℝ) (hb : 0 ≤ b) : rho b ≤ 1024 * b ^ 4 * Real.exp (64 * b) := by
  have hgap : 0 ≤ Real.exp (32 * b) - Real.exp (-32 * b) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hexp : Real.exp (-64 * b) * Real.exp (32 * b) = Real.exp (-32 * b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlinear := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-64 * b))
    (Real.exp_nonneg (32 * b))
  rw [hexp] at hlinear
  have hupper : Real.exp (32 * b) - Real.exp (-32 * b) ≤
      64 * b * Real.exp (32 * b) := by nlinarith
  have hsq : (Real.exp (32 * b)) ^ 2 = Real.exp (64 * b) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    rho b ≤ b ^ 2 / 4 * (64 * b * Real.exp (32 * b)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hgap hupper 2) (by positivity)
    _ = 1024 * b ^ 4 * Real.exp (64 * b) := by
      rw [mul_pow, mul_pow, hsq]
      ring

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local instance p4Q2PZ37ACI_res_links : Fintype Link := Fintype.ofFinite _
local notation "left0" => originalWilsonExplicitIdentityBoundary H
local notation "left1" => p4Q2FQ_originalSU2LeftPiRotationAtLink H
local notation "density" => p4Q2PZ37ABT_originalPosteriorDensity H
local notation "contrast" => p4Q2GB_originalWilsonPosteriorLeftDensityContrast H
local notation "det" => p4Q2PZ37ABU_originalPosteriorDet H
local notation "slope" => p4Q2PZ37ABY_originalDetSlope H
local notation "Q" => p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq H
local notation "k" => p4Q2PZ37ACH_originalPosteriorEnergyContrast H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H

private theorem contrast_continuous (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    Continuous (contrast b hb B e) := by
  change Continuous (fun g => density b hb left0 B e g - density b hb (left1 e) B e g)
  exact (p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb left0 B e).sub
    (p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb (left1 e) B e)

private theorem contrast_variance (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    Var (contrast b hb B e) = Q b hb B e := by
  change (∫ g : G, contrast b hb B e g * contrast b hb B e g ∂μ) -
    (∫ g : G, contrast b hb B e g ∂μ) * (∫ g : G, contrast b hb B e g ∂μ) =
      ∫ g : G, (contrast b hb B e g) ^ 2 ∂μ
  rw [p4Q2PZ37ACH_originalContrast_mean_zero]
  simp only [zero_mul, sub_zero, pow_two]

private theorem contrast_covariance (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    Cov (contrast b hb B e) E = -k b hb B e := by
  unfold CompactEnergyMismatchMoment.covariance
  rw [p4Q2PZ37ACH_originalContrast_mean_zero]
  simp only [zero_mul, sub_zero]
  change (∫ g : G, contrast b hb B e g * E g ∂μ) = -(-(∫ g : G, E g * contrast b hb B e g ∂μ))
  simp only [neg_neg, mul_comm]

/-- Pointwise error of the unchanged determinant about the midpoint slope.
The possibly discontinuous total slope is used only pointwise. -/
theorem p4Q2PZ37ACI_originalDet_midpoint_error
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) :
    |det b hb B e g h - (b * (Real.exp (32 * b) + Real.exp (-32 * b))) * (E h - E g)| ≤
      (b * (Real.exp (32 * b) - Real.exp (-32 * b))) * |E h - E g| := by
  have hs := p4Q2PZ37ABY_originalDetSlope_twoSided H b hb B e g h
  have ha : |2 * slope b hb B e g h - (Real.exp (32 * b) + Real.exp (-32 * b))| ≤
      Real.exp (32 * b) - Real.exp (-32 * b) := abs_le.mpr ⟨by linarith, by linarith⟩
  have heq : det b hb B e g h - (b * (Real.exp (32 * b) + Real.exp (-32 * b))) * (E h - E g) =
      b * (2 * slope b hb B e g h - (Real.exp (32 * b) + Real.exp (-32 * b))) * (E h - E g) := by
    rw [p4Q2PZ37ABY_originalDet_eq_slope_mul_cross, p4Q2PZ37ABV_temporalCrossLog_eq_energy]
    ring
  rw [heq, abs_mul, abs_mul, abs_of_nonneg hb]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hb) (abs_nonneg _)

/-- The full original affine residual has a proved volume-independent variance bound. -/
theorem p4Q2PZ37ACI_originalAffineResidual_variance_le
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    Var (fun g => contrast b hb B e g +
      (b * (Real.exp (32 * b) + Real.exp (-32 * b))) * E g) ≤ rho b := by
  have hc : 0 ≤ b * (Real.exp (32 * b) - Real.exp (-32 * b)) :=
    mul_nonneg hb (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))
  have h := CompactPosteriorEnergyResidual.variance_contrast_add_energy_le μ
    (density b hb left0 B e) (density b hb (left1 e) B e) E
    (b * (Real.exp (32 * b) + Real.exp (-32 * b)))
    (b * (Real.exp (32 * b) - Real.exp (-32 * b)))
    (p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb left0 B e)
    (p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb (left1 e) B e)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
    (p4Q2PZ37ABT_originalPosteriorDensity_mass_one H b hb left0 B e)
    (p4Q2PZ37ABT_originalPosteriorDensity_mass_one H b hb (left1 e) B e)
    p4Q2PZ37ABZ_originalEnergy_Haar_variance hc
    (fun g h => p4Q2PZ37ACI_originalDet_midpoint_error H b hb B e g h)
  change Var (fun g => contrast b hb B e g +
    (b * (Real.exp (32 * b) + Real.exp (-32 * b))) * E g) ≤
      (b * (Real.exp (32 * b) - Real.exp (-32 * b))) ^ 2 / 4 at h
  convert h using 1 <;> unfold p4Q2PZ37ACI_originalPosteriorResidualEnvelope <;> ring

/-- A sharper k-dependent bound obtained by completing the actual variance square. -/
theorem p4Q2PZ37ACI_originalPosteriorResidual_le_energyProduct
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    Q b hb B e - 4 * (k b hb B e) ^ 2 ≤
      (2 * k b hb B e - b * Real.exp (-32 * b)) *
        (b * Real.exp (32 * b) - 2 * k b hb B e) := by
  have h := p4Q2PZ37ACI_originalAffineResidual_variance_le H b hb B e
  have hv := CompactEnergyMismatchMoment.variance_residual μ 1
    (b * (Real.exp (32 * b) + Real.exp (-32 * b)))
    (contrast b hb B e) E (contrast_continuous H b hb B e)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
  simp only [CompactEnergyMismatchMoment.residual, one_mul] at hv
  rw [hv, contrast_variance, contrast_covariance, p4Q2PZ37ABZ_originalEnergy_Haar_variance] at h
  unfold p4Q2PZ37ACI_originalPosteriorResidualEnvelope at h
  nlinarith

/-- The actual posterior residual is unconditionally bounded at every finite volume. -/
theorem p4Q2PZ37ACI_originalPosteriorResidual_le_envelope
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    0 ≤ Q b hb B e - 4 * (k b hb B e) ^ 2 ∧
      Q b hb B e - 4 * (k b hb B e) ^ 2 ≤ rho b := by
  refine ⟨p4Q2PZ37ACH_originalPosteriorResidual_nonneg H b hb B e, ?_⟩
  have h := p4Q2PZ37ACI_originalPosteriorResidual_le_energyProduct H b hb B e
  have hs := sq_nonneg (2 * k b hb B e -
    (b * (Real.exp (32 * b) + Real.exp (-32 * b))) / 2)
  unfold p4Q2PZ37ACI_originalPosteriorResidualEnvelope
  nlinarith

/-- Explicit fourth-order posterior residual bound, independent of H, B and e. -/
theorem p4Q2PZ37ACI_originalPosteriorResidual_le_quartic
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    Q b hb B e - 4 * (k b hb B e) ^ 2 ≤ 1024 * b ^ 4 * Real.exp (64 * b) :=
  (p4Q2PZ37ACI_originalPosteriorResidual_le_envelope H b hb B e).2.trans
    (p4Q2PZ37ACI_originalPosteriorResidualEnvelope_le_quartic b hb)

/-- ACH now has a proved numerical posterior-residual factor; no new hypothesis. -/
theorem p4Q2PZ37ACI_originalGI_energyRegression_explicit_sq
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    (gap b hb f e z + 4 * k b hb z.2 e * Cov (F b hb f e z) E) ^ 2 ≤
      (Var (F b hb f e z) - 4 * (Cov (F b hb f e z) E) ^ 2) * rho b := by
  have hF : Continuous (F b hb f e z) :=
    (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num) b hb f e).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hD := CompactEnergyMismatchMoment.regressionDefect_nonneg μ (F b hb f e z) E hF
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2) p4Q2PZ37ABZ_originalEnergy_Haar_variance
  exact (p4Q2PZ37ACH_originalGI_energyRegression_sq H b hb f e z).trans
    (mul_le_mul_of_nonneg_left
      (p4Q2PZ37ACI_originalPosteriorResidual_le_envelope H b hb z.2 e).2 hD)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_originalPosteriorResidualEnvelope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_originalPosteriorResidualEnvelope_le_quartic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_originalDet_midpoint_error
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_originalAffineResidual_variance_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_originalPosteriorResidual_le_energyProduct
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_originalPosteriorResidual_le_envelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_originalPosteriorResidual_le_quartic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACI_originalGI_energyRegression_explicit_sq
