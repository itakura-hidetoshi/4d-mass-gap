import MGAP4D.MathlibAnalytic.CompactEnergyRegressionContrast
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExplicitFXMomentRayleighV5_PZ37ACF

/-!
# P4-Q2-PZ37ACH — true posterior energy contrast and sharp GI regression

The SAME two interacting posterior densities have energy contrast
  k = - integral E(g) (p0(g)-ppi(g)) dHaar(g).
The actual determinant slope and true Haar energy variance 1/4 prove
  (b/2) exp(-32b) <= k <= (b/2) exp(32b)
for every H, true link and right configuration. On b0<=b<=B, b0>0,
this supplies the positive uniform floor (b0/2)exp(-32B).

For the ORIGINAL physical FF receiver F, C=Cov(F,E), D=Var(F)-4C^2,
and the ORIGINAL FX variance Q, remove the energy component from BOTH
F and the actual signed posterior density. The exact sharp estimate is
  (GI+4*k*C)^2 <= D*(Q-4*k^2),  0<=Q-4*k^2.
The residual on the right is an actual Haar regression variance. There is
no independent-density replacement, no new physical source, no removal
of the Perron/transfer factors, and no assertion that physical C is nonzero
or that either residual is small. These are real model estimates, not a
proof of a uniform GI moment, all-source coercivity or continuum mass gap.
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
local notation "ν" => Measure.prod μ μ
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Cov" => CompactEnergyMismatchMoment.covariance μ
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local instance p4Q2PZ37ACH_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACH_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACH_countable : SecondCountableTopology G := specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACH_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACH_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACH_probability : IsProbabilityMeasure μ := normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local instance p4Q2PZ37ACH_links : Fintype Link := Fintype.ofFinite _
local notation "left0" => originalWilsonExplicitIdentityBoundary H
local notation "left1" => p4Q2FQ_originalSU2LeftPiRotationAtLink H
local notation "density" => p4Q2PZ37ABT_originalPosteriorDensity H
local notation "contrast" => p4Q2GB_originalWilsonPosteriorLeftDensityContrast H
local notation "det" => p4Q2PZ37ABU_originalPosteriorDet H
local notation "Q" => p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H

private theorem contrast_continuous (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    Continuous (contrast b hb B e) := by
  change Continuous (fun g => density b hb left0 B e g - density b hb (left1 e) B e g)
  exact (p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb left0 B e).sub
    (p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb (left1 e) B e)

/-- Normalization of both ORIGINAL rows gives zero mean of their signed contrast. -/
theorem p4Q2PZ37ACH_originalContrast_mean_zero
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    (∫ g : G, contrast b hb B e g ∂μ) = 0 := by
  change (∫ g : G, density b hb left0 B e g - density b hb (left1 e) B e g ∂μ) = 0
  rw [integral_sub
    ((p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb left0 B e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb (left1 e) B e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)),
    p4Q2PZ37ABT_originalPosteriorDensity_mass_one,
    p4Q2PZ37ABT_originalPosteriorDensity_mass_one]
  ring

/-- The actual difference in posterior energy expectations, with positive orientation. -/
def p4Q2PZ37ACH_originalPosteriorEnergyContrast
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) : ℝ :=
  -(∫ g : G, E g * contrast b hb B e g ∂μ)
local notation "k" => p4Q2PZ37ACH_originalPosteriorEnergyContrast H

/-- Full determinant pairing, not a restriction to a favorable cap or tail. -/
theorem p4Q2PZ37ACH_originalEnergyContrast_pairing
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    (∫ w : G × G, (E w.2 - E w.1) * det b hb B e w.1 w.2 ∂ν) =
      2 * k b hb B e := by
  let P0 : G → ℝ := density b hb left0 B e
  let P1 : G → ℝ := density b hb (left1 e) B e
  have h0 : Continuous P0 := p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb left0 B e
  have h1 : Continuous P1 := p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb (left1 e) B e
  have hE := continuous_specialUnitaryWilsonPlaquetteEnergy 2
  have hpair := integral_twoDensitySignedPair_eq_two_mul_gap μ P0 P1 E h0 h1 hE
    (p4Q2PZ37ABT_originalPosteriorDensity_mass_one H b hb left0 B e)
    (p4Q2PZ37ABT_originalPosteriorDensity_mass_one H b hb (left1 e) B e)
  have hc : (∫ g : G, E g * contrast b hb B e g ∂μ) =
      (∫ g, P0 g * E g ∂μ) - ∫ g, P1 g * E g ∂μ := by
    change (∫ g : G, E g * (P0 g - P1 g) ∂μ) = _
    calc
      _ = ∫ g : G, P0 g * E g - P1 g * E g ∂μ := by
        apply integral_congr_ae
        filter_upwards with g
        ring
      _ = _ := integral_sub
        ((h0.mul hE).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        ((h1.mul hE).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hp (w : G × G) : (E w.2 - E w.1) * det b hb B e w.1 w.2 =
      -twoDensitySignedPair P0 P1 E w := by
    dsimp [p4Q2PZ37ABU_originalPosteriorDet, twoDensitySignedPair, P0, P1]
    ring
  simp_rw [hp]
  rw [integral_neg, hpair, ← hc]
  unfold p4Q2PZ37ACH_originalPosteriorEnergyContrast
  ring

/-- H/link/environment independent bounds, obtained from the FULL true integral. -/
theorem p4Q2PZ37ACH_originalEnergyContrast_twoSided
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    (b / 2) * Real.exp (-32 * b) ≤ k b hb B e ∧
      k b hb B e ≤ (b / 2) * Real.exp (32 * b) := by
  let W : G × G → ℝ := fun w => (E w.2 - E w.1) ^ 2
  let J : G × G → ℝ := fun w => (E w.2 - E w.1) * det b hb B e w.1 w.2
  have hE := continuous_specialUnitaryWilsonPlaquetteEnergy 2
  have hW : Continuous W := ((hE.comp continuous_snd).sub (hE.comp continuous_fst)).pow 2
  have hJ : Continuous J := ((hE.comp continuous_snd).sub (hE.comp continuous_fst)).mul
    (p4Q2PZ37ABV_originalDet_continuous H b hb B e)
  have hPoint (w : G × G) :
      (2 * b * Real.exp (-32 * b)) * W w ≤ J w ∧
        J w ≤ (2 * b * Real.exp (32 * b)) * W w := by
    have hs := p4Q2PZ37ABY_originalDetSlope_twoSided H b hb B e w.1 w.2
    have hlo := mul_le_mul_of_nonneg_left hs.1 (show 0 ≤ 2 * b * W w by dsimp [W]; positivity)
    have hhi := mul_le_mul_of_nonneg_left hs.2 (show 0 ≤ 2 * b * W w by dsimp [W]; positivity)
    have hj : J w = (2 * b * W w) * p4Q2PZ37ABY_originalDetSlope H b hb B e w.1 w.2 := by
      dsimp [J, W]
      rw [p4Q2PZ37ABY_originalDet_eq_slope_mul_cross, p4Q2PZ37ABV_temporalCrossLog_eq_energy]
      ring
    constructor
    · calc
        _ = (2 * b * W w) * Real.exp (-32 * b) := by ring
        _ ≤ _ := by rw [hj]; exact hlo
    · calc
        _ ≤ (2 * b * W w) * Real.exp (32 * b) := by rw [hj]; exact hhi
        _ = _ := by ring
  have hWSq : (∫ w : G × G, W w ∂ν) = (1 / 2 : ℝ) := by
    have hp (w : G × G) : W w = (E w.1 - E w.2) ^ 2 := by dsimp [W]; ring
    simp_rw [hp]
    rw [CompactEnergyMismatchMoment.difference_square_integral μ E hE,
      p4Q2PZ37ABZ_originalEnergy_Haar_variance]
    norm_num
  have hJI : Integrable J ν := hJ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLI : Integrable (fun w => (2 * b * Real.exp (-32 * b)) * W w) ν :=
    (continuous_const.mul hW).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hUI : Integrable (fun w => (2 * b * Real.exp (32 * b)) * W w) ν :=
    (continuous_const.mul hW).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlo := integral_mono hLI hJI (fun w => (hPoint w).1)
  have hhi := integral_mono hJI hUI (fun w => (hPoint w).2)
  rw [integral_const_mul, hWSq] at hlo hhi
  change _ ≤ ∫ w : G × G, (E w.2 - E w.1) * det b hb B e w.1 w.2 ∂ν at hlo
  change (∫ w : G × G, (E w.2 - E w.1) * det b hb B e w.1 w.2 ∂ν) ≤ _ at hhi
  rw [p4Q2PZ37ACH_originalEnergyContrast_pairing] at hlo hhi
  constructor <;> linarith

/-- Every positive original coupling has a strictly positive energy contrast. -/
theorem p4Q2PZ37ACH_originalEnergyContrast_pos
    (b : ℝ) (hb : 0 < b) (B : Cfg) (e : Link) : 0 < k b hb.le B e :=
  (mul_pos (half_pos hb) (Real.exp_pos _)).trans_le
    (p4Q2PZ37ACH_originalEnergyContrast_twoSided H b hb.le B e).1

/-- A genuine uniform positive energy-contrast floor on a prescribed positive interval.
This concerns the posterior ENERGY, not the unknown physical source covariance. -/
theorem p4Q2PZ37ACH_originalEnergyContrast_uniform_floor
    (b0 b upper : ℝ) (hb0 : 0 < b0) (hlo : b0 ≤ b) (hhi : b ≤ upper)
    (B : Cfg) (e : Link) :
    0 < (b0 / 2) * Real.exp (-32 * upper) ∧
      (b0 / 2) * Real.exp (-32 * upper) ≤ k b (hb0.le.trans hlo) B e := by
  have hExp : Real.exp (-32 * upper) ≤ Real.exp (-32 * b) := Real.exp_le_exp.mpr (by linarith)
  have hp := mul_le_mul hlo hExp (Real.exp_nonneg _) (hb0.le.trans hlo)
  refine ⟨mul_pos (half_pos hb0) (Real.exp_pos _), ?_⟩
  have hk := (p4Q2PZ37ACH_originalEnergyContrast_twoSided H b (hb0.le.trans hlo) B e).1
  linarith

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

/-- The posterior-side residual is an actual nonnegative regression variance. -/
theorem p4Q2PZ37ACH_originalPosteriorResidual_nonneg
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    0 ≤ Q b hb B e - 4 * (k b hb B e) ^ 2 := by
  have h := CompactEnergyMismatchMoment.regressionDefect_nonneg μ
    (contrast b hb B e) E (contrast_continuous H b hb B e)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2) p4Q2PZ37ABZ_originalEnergy_Haar_variance
  unfold CompactEnergyMismatchMoment.regressionDefect at h
  rw [contrast_variance, contrast_covariance, neg_sq] at h
  exact h

private theorem receiver_continuous (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Continuous (F b hb f e z) :=
  (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num) b hb f e).continuous.comp
    (continuous_const.prodMk continuous_id)

/-- Sharp unchanged-model GI regression estimate, with BOTH actual residuals. -/
theorem p4Q2PZ37ACH_originalGI_energyRegression_sq
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    (gap b hb f e z + 4 * k b hb z.2 e * Cov (F b hb f e z) E) ^ 2 ≤
      (Var (F b hb f e z) - 4 * (Cov (F b hb f e z) E) ^ 2) *
        (Q b hb z.2 e - 4 * (k b hb z.2 e) ^ 2) := by
  have hFD : Cov (F b hb f e z) (contrast b hb z.2 e) = gap b hb f e z := by
    unfold CompactEnergyMismatchMoment.covariance
    rw [p4Q2PZ37ACH_originalContrast_mean_zero]
    simp only [mul_zero, sub_zero]
    exact (p4Q2GI_originalWilsonSignedTwoPosteriorExpectationGap_eq_HaarPairing H b hb f e z).symm
  have h := CompactEnergyRegressionContrast.regression_pairing_sq_le μ
    (F b hb f e z) (contrast b hb z.2 e) E
    (receiver_continuous H b hb f e z) (contrast_continuous H b hb z.2 e)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2) p4Q2PZ37ABZ_originalEnergy_Haar_variance
  rw [hFD, contrast_covariance] at h
  unfold CompactEnergyMismatchMoment.regressionDefect at h
  rw [contrast_variance, contrast_covariance, neg_sq] at h
  convert h using 1 <;> ring

/-- Absolute error around the true posterior-energy coefficient, not an approximate center. -/
theorem p4Q2PZ37ACH_originalGI_energyRegression_abs
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    |gap b hb f e z + 4 * k b hb z.2 e * Cov (F b hb f e z) E| ≤
      Real.sqrt ((Var (F b hb f e z) - 4 * (Cov (F b hb f e z) E) ^ 2) *
        (Q b hb z.2 e - 4 * (k b hb z.2 e) ^ 2)) :=
  Real.abs_le_sqrt (p4Q2PZ37ACH_originalGI_energyRegression_sq H b hb f e z)

/-- Exact energy regression eliminates the GI error; its occurrence is NOT asserted. -/
theorem p4Q2PZ37ACH_originalGI_exact_of_zeroDefect
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (hD : Var (F b hb f e z) - 4 * (Cov (F b hb f e z) E) ^ 2 = 0) :
    gap b hb f e z = -4 * k b hb z.2 e * Cov (F b hb f e z) E := by
  have h := p4Q2PZ37ACH_originalGI_energyRegression_sq H b hb f e z
  rw [hD, zero_mul] at h
  have he : gap b hb f e z + 4 * k b hb z.2 e * Cov (F b hb f e z) E = 0 :=
    (sq_eq_zero_iff).mp (le_antisymm h (sq_nonneg _))
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACH_originalContrast_mean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACH_originalEnergyContrast_pairing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACH_originalEnergyContrast_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACH_originalEnergyContrast_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACH_originalEnergyContrast_uniform_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACH_originalPosteriorResidual_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACH_originalGI_energyRegression_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACH_originalGI_energyRegression_abs
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACH_originalGI_exact_of_zeroDefect
