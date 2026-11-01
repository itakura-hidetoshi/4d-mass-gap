import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCovarianceHaarBallsV5_PZ37ADH
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADI — necessary numeric Haar mass and Lipschitz-radius monotonicity

This is an appendix-only quantitative OBSTRUCTION for the SAME actual
finite-volume interacting Wilson SU(2) model, physical centered Gauss-law
source, original FF receiver, transfer/Perron section, original two
interacting posteriors and boundary pair-Haar probability.

ACJ's genuine pointwise covariance estimate 4*C_e(z)^2 <= B_H^2
and ADF's actual transfer/plaquette cap B_H^2 <= K_H together imply
4*C_e(z)^2 <= K_H at every actual boundary pair, without extra premises.

Consequently the strict ADH single-ball sufficient criterion
K_H < 68*C_e(z0)^2*ν_H(ball) forces ν_H(ball) > 1/17.
If a candidate ball has Haar mass <= 1/17, its numerical test is
IMPOSSIBLE, even if the ball exists, has positive measure and carries
nonzero covariance. The same criterion also necessarily requires
C_e(z0)^2 > K_H/68, since the original pair-Haar law is a probability.

For two positive certified Lipschitz constants L1 <= L2, the radius
|C(z0)|/(2*L1) is at least |C(z0)|/(2*L2), hence the actual Haar
ball mass and the candidate numeric right-hand side cannot decrease
when the coefficient improves. This does NOT assert any physical
Lipschitz constant, a numerical covariance amplitude, or a numerical
Haar ball mass has yet been established.

In particular the 1/17 result is a NECESSARY condition for the
specific ADH sufficient certificate; it is NOT a new necessary
condition for genuine signed GI response or for a continuum mass gap.
No H-uniform positive estimate or numerical threshold crossing is
claimed. The pseudometric remains ADH's compatible, noncalibrated
presentation; no new physical metric or probability law is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local instance p4Q2PZ37ADI_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADI_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADI_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADI_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADI_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADI_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G
local instance p4Q2PZ37ADI_matrixPseudometrizable :
    TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 2) (Fin 2) ℂ) := by
  change TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ)
  infer_instance
local instance p4Q2PZ37ADI_groupPseudometrizable :
    TopologicalSpace.PseudoMetrizableSpace G := by
  change TopologicalSpace.PseudoMetrizableSpace
    {u : Matrix (Fin 2) (Fin 2) ℂ |
      u ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ}
  infer_instance

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "b₀" => p4Q2PZ37ADC_fixedCoupling
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "K" => p4Q2PZ37ADF_originalTransferPlaquetteFCBound H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local instance p4Q2PZ37ADI_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADI_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ADI_pairPseudometrizable :
    TopologicalSpace.PseudoMetrizableSpace Pair := by
  infer_instance
local instance p4Q2PZ37ADI_pairPseudoMetric : PseudoMetricSpace Pair :=
  TopologicalSpace.pseudoMetrizableSpacePseudoMetric _

/-- ORIGINAL pointwise covariance cannot exceed one quarter of the
genuine explicit transfer/plaquette cap, at any physical boundary pair. -/
theorem p4Q2PZ37ADI_originalPointwiseCovariance_fourSq_le_cap
    (e : Link) (z : Pair) :
    4 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z) ^ 2 ≤ K := by
  have hCont : Continuous
      (F b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z) :=
    (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H 2 (by norm_num) b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e).continuous.comp
        (continuous_const.prodMk continuous_id)
  have hCov :
      4 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z) ^ 2 ≤
        Var (F b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z) := by
    change 4 * (CompactEnergyMismatchMoment.covariance μ
        (F b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z) E) ^ 2 ≤
      Var (F b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z)
    exact CompactEnergyMismatchMoment.four_covariance_sq_le_variance μ
      (F b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z) E hCont
      (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
      p4Q2PZ37ABZ_originalEnergy_Haar_variance
  have hVar :=
    p4Q2PZ37ACA_originalReceiver_variance_le_FC
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z
  change Var (F b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z) ≤
    (B b₀ p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 at hVar
  exact (hCov.trans hVar).trans
    (p4Q2PZ37ADF_originalFCsq_le_transferPlaquetteBound H)

/-- An original pair-Haar region with mass at most 1/17 CANNOT pass
the ADH 68*C(z0)^2*mass test. This is an unconditional statement
about the true Wilson covariance and actual K_H, not an artificial
scalar covariance or substitute probability space. -/
theorem p4Q2PZ37ADI_smallOriginalRegion_obstructs_numeric
    (e : Link) (z₀ : Pair) (A : Set Pair)
    (hSmall : Measure.real outer A ≤ (1 : ℝ) / 17) :
    68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 *
        Measure.real outer A ≤ K := by
  have hFour := p4Q2PZ37ADI_originalPointwiseCovariance_fourSq_le_cap H e z₀
  have hSq : 0 ≤ (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 :=
    sq_nonneg _
  have hMassScale : 68 * Measure.real outer A ≤ 4 := by
    linarith
  have hMul := mul_le_mul_of_nonneg_right hMassScale hSq
  calc
    68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 *
        Measure.real outer A =
      (68 * Measure.real outer A) *
        (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 := by ring
    _ ≤ 4 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 := hMul
    _ ≤ K := hFour

/-- Necessary geometric prerequisite for the strict ADH single-region
sufficient criterion: the region's ACTUAL Haar probability exceeds 1/17.
No Lipschitz or numerical value is inferred from this implication. -/
theorem p4Q2PZ37ADI_numeric_requires_mass_gt_oneSeventeenth
    (e : Link) (z₀ : Pair) (A : Set Pair)
    (hNumeric : K <
      68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 *
        Measure.real outer A) :
    (1 : ℝ) / 17 < Measure.real outer A := by
  by_contra hNot
  have hSmall : Measure.real outer A ≤ (1 : ℝ) / 17 :=
    le_of_not_gt hNot
  exact (not_lt_of_ge
    (p4Q2PZ37ADI_smallOriginalRegion_obstructs_numeric H e z₀ A hSmall))
      hNumeric

/-- The same numerical condition forces a LARGE genuine covariance
amplitude as a separate necessary test, because original pair-Haar
has total mass one: K_H/68 < C_e(z0)^2. -/
theorem p4Q2PZ37ADI_numeric_requires_covarianceAmplitude
    (e : Link) (z₀ : Pair) (A : Set Pair)
    (hNumeric : K <
      68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 *
        Measure.real outer A) :
    K / 68 <
      (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 := by
  have hMass : Measure.real outer A ≤ 1 := measureReal_le_one
  have hSq :
      0 ≤ 68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 := by
    positivity
  have hMul := mul_le_mul_of_nonneg_left hMass hSq
  have hUpper :
      68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 *
          Measure.real outer A ≤
        68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 := by
    nlinarith only [hMul]
  linarith

/-- If a candidate ORIGINAL Haar ball has mass <= 1/17, the
single-ball ADH strict numerical hypothesis is refuted independently
of its center or radius, for the fixed volume and genuine link. -/
theorem p4Q2PZ37ADI_smallActualHaarBall_obstructs_numeric
    (e : Link) (z₀ : Pair) (r : ℝ)
    (hSmall : Measure.real outer (Metric.ball z₀ r) ≤ (1 : ℝ) / 17) :
    68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 *
      Measure.real outer (Metric.ball z₀ r) ≤ K :=
  p4Q2PZ37ADI_smallOriginalRegion_obstructs_numeric
    H e z₀ (Metric.ball z₀ r) hSmall

/-- For the SAME actual covariance value, improving a certified
positive Lipschitz constant L1 <= L2 can only ENLARGE the explicit
ADH radius, and can only increase the original pair-Haar ball mass.
The compatible pseudometric is the SAME one for both bounds. -/
theorem p4Q2PZ37ADI_explicitLipschitzRadius_mass_antitone
    (e : Link) (z₀ : Pair) (L₁ L₂ : ℝ)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hCompare : L₁ ≤ L₂) :
    Measure.real outer (Metric.ball z₀
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L₂))) ≤
      Measure.real outer (Metric.ball z₀
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L₁))) := by
  have hDen₁ : 0 < 2 * L₁ := by positivity
  have hDen₂ : 0 < 2 * L₂ := by positivity
  have hCross :
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| * (2 * L₁) ≤
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| * (2 * L₂) := by
    exact mul_le_mul_of_nonneg_left (by linarith)
      (abs_nonneg _)
  have hRadius :
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L₂) ≤
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L₁) :=
    (div_le_div_iff₀ hDen₂ hDen₁).2 hCross
  exact measureReal_mono (Metric.ball_subset_ball hRadius)

/-- Larger certified Lipschitz constants give WEAKER candidate numeric
right-hand sides for the SAME real original covariance and Haar law. -/
theorem p4Q2PZ37ADI_explicitRadius_numeric_monotone
    (e : Link) (z₀ : Pair) (L₁ L₂ : ℝ)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hCompare : L₁ ≤ L₂)
    (hNumeric₂ : K <
      68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 *
        Measure.real outer (Metric.ball z₀
          (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L₂)))) :
    K < 68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 *
      Measure.real outer (Metric.ball z₀
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L₁))) := by
  have hMass :=
    p4Q2PZ37ADI_explicitLipschitzRadius_mass_antitone
      H e z₀ L₁ L₂ hL₁ hL₂ hCompare
  have hCoeff :
      0 ≤ 68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 := by
    positivity
  exact lt_of_lt_of_le hNumeric₂
    (mul_le_mul_of_nonneg_left hMass hCoeff)

/-- A separately proven better true physical Lipschitz coefficient
and a numerical test at a worse coefficient suffice to reuse ADH's
exact original GI conclusion. Neither certification is postulated. -/
theorem p4Q2PZ37ADI_betterLipschitz_numericGivesGI
    (e : Link) (z₀ : Pair)
    (hz₀ : C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ ≠ 0)
    (L₁ L₂ : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hCompare : L₁ ≤ L₂)
    (hLip₁ : ∀ z : Pair,
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| ≤
          L₁ * dist z z₀)
    (hNumeric₂ : K <
      68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 *
        Measure.real outer (Metric.ball z₀
          (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L₂)))) :
    0 < Budget b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e ∧
      ∃ V : Set Pair, IsOpen V ∧ 0 < Measure.real outer V ∧
        ∀ z ∈ V,
          0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z| := by
  have hNumeric₁ :=
    p4Q2PZ37ADI_explicitRadius_numeric_monotone
      H e z₀ L₁ L₂ hL₁ hL₂ hCompare hNumeric₂
  exact p4Q2PZ37ADH_originalLipschitzBall_numericGivesGI
    H e z₀ hz₀ L₁ hL₁ hLip₁ hNumeric₁

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADI_originalPointwiseCovariance_fourSq_le_cap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADI_smallOriginalRegion_obstructs_numeric
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADI_numeric_requires_mass_gt_oneSeventeenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADI_numeric_requires_covarianceAmplitude
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADI_smallActualHaarBall_obstructs_numeric
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADI_explicitLipschitzRadius_mass_antitone
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADI_explicitRadius_numeric_monotone
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADI_betterLipschitz_numericGivesGI
