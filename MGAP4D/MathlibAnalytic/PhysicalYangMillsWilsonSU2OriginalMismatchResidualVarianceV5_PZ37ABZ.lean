import MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalReceiverTransferSectionV5_PZ37ABZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABZ — actual full Wilson mismatch from energy residual variance

The SAME FF physical receiver F, two interacting posterior laws, and ABY
complete negative crossing moment are retained. For every a>0, square
completion proves M_{-s} <= (b/a) Var_Haar(F+s*a*E). No tail-smallness
hypothesis enters this bound. Genuine SU(2) Haar gives Var(E)=1/4, so the
right side is an explicit quadratic expression in the actual receiver
variance and receiver/energy covariance.

The covariance also gives an exact signed balance and an obstruction:
nonnegative oriented covariance makes ABY's sufficient margin nonpositive.
This does NOT imply that the original GI response itself is nonpositive.
The residual upper bound feeds the ABX rectangle and the original outer
configuration pair-Haar second moment with an explicit margin condition.
No H-uniform residual bound, rectangle mass, physical coercivity or
continuum mass gap is asserted. ABX's rectangle is not the fixed ABV cap.
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
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37ABZ_varianceGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABZ_varianceCompact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABZ_varianceCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABZ_varianceMeasurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABZ_varianceBorel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABZ_varianceProbability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The genuine Wilson energy has Haar mean one, by the original
zero-mean SU(2) character theorem. -/
theorem p4Q2PZ37ABZ_originalEnergy_Haar_mean : (∫ g : G, E g ∂μ) = 1 := by
  have hE : Integrable E μ :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := p4Q2PZ35D4_originalOneLinkHaar_characterZero
  change (∫ g : G, (1 : ℝ) - E g ∂μ) = 0 at h
  rw [integral_sub (integrable_const 1) hE] at h
  have hOne : (∫ _g : G, (1 : ℝ) ∂μ) = 1 := by simp
  rw [hOne] at h
  linarith

/-- Exact second moment of the same SU(2) Wilson energy. The coefficient
comes from genuine Haar Schur integration, not a finite subgroup law. -/
theorem p4Q2PZ37ABZ_originalEnergy_Haar_second :
    (∫ g : G, E g ^ 2 ∂μ) = (5 / 4 : ℝ) := by
  have hχ1 : χ (1 : G) = 1 := by
    unfold p4Q2PZ35C_originalOneLinkCharacter
    rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)]
    norm_num
  have hχSq : (∫ g : G, χ g ^ 2 ∂μ) = (1 / 4 : ℝ) := by
    have h := p4Q2PZ35D4_originalOneLinkHaar_characterQuarter (1 : G)
    simpa only [mul_one, p4Q2PZ35D5_originalCharacter_inv, hχ1, pow_two] using h
  have hE : Integrable E μ :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hχInt : Integrable (fun g : G => χ g ^ 2) μ :=
    ((continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp (g : G) : E g ^ 2 = χ g ^ 2 + 2 * E g - 1 := by
    unfold p4Q2PZ35C_originalOneLinkCharacter
    ring
  have hTwice : Integrable (fun g : G => 2 * E g) μ := hE.const_mul 2
  have hSum : Integrable (fun g : G => χ g ^ 2 + 2 * E g) μ := hχInt.add hTwice
  have hOneI : Integrable (fun _g : G => (1 : ℝ)) μ := integrable_const 1
  simp_rw [hp]
  rw [integral_sub hSum hOneI,
    integral_add hχInt hTwice, integral_const_mul,
    hχSq, p4Q2PZ37ABZ_originalEnergy_Haar_mean]
  norm_num

/-- The energy variance in the actual reference Haar is exactly 1/4. -/
theorem p4Q2PZ37ABZ_originalEnergy_Haar_variance :
    CompactEnergyMismatchMoment.variance μ E = (1 / 4 : ℝ) := by
  unfold CompactEnergyMismatchMoment.variance CompactEnergyMismatchMoment.covariance
  have h2 := p4Q2PZ37ABZ_originalEnergy_Haar_second
  simp only [pow_two] at h2
  rw [h2, p4Q2PZ37ABZ_originalEnergy_Haar_mean]
  norm_num

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local instance p4Q2PZ37ABZ_varianceLinks : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ABZ_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local notation "response" => p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num)
local notation "psi" => p4Q2PZ37ABY_originalCrossPair H
local notation "mass" => p4Q2PZ37ABY_originalCrossPartMass H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H

/-- A section of the original FF bounded continuous physical receiver. -/
def p4Q2PZ37ABZ_originalReceiverSection
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (g : G) : ℝ :=
  response b hb f e (z, g)
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H

private theorem p4Q2PZ37ABZ_receiver_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Continuous (F b hb f e z) :=
  (response b hb f e).continuous.comp (continuous_const.prodMk continuous_id)

/-- Exact identification with the generic energy pairing, retaining the
actual physical receiver and the original energy-crossing orientation. -/
theorem p4Q2PZ37ABZ_originalCrossPair_eq_energyPair
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    psi b hb f e z s = CompactEnergyMismatchMoment.signedPair b s (F b hb f e z) E := by
  funext w
  rw [p4Q2PZ37ABY_originalCrossPair_eq_energy]
  rfl

/-- The complete ABY mismatch is exactly the original-source analytic
mismatch; this equality makes no positivity or localization assumption. -/
theorem p4Q2PZ37ABZ_originalMismatch_eq_energyMismatch
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    mass b hb f e z (-s) =
      CompactEnergyMismatchMoment.mismatch μ b s (F b hb f e z) E := by
  unfold p4Q2PZ37ABY_originalCrossPartMass CompactEnergyMismatchMoment.mismatch
  rw [p4Q2PZ37ABZ_originalCrossPair_eq_energyPair]
  apply integral_congr_ae
  filter_upwards with w
  congr 1
  unfold CompactEnergyMismatchMoment.signedPair
  ring

/-- The signed crossing balance is the actual receiver-energy covariance. -/
theorem p4Q2PZ37ABZ_originalCrossPair_integral_eq_covariance
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    (∫ w : G × G, psi b hb f e z s w ∂ν) =
      -4 * b * s * CompactEnergyMismatchMoment.covariance μ (F b hb f e z) E := by
  rw [p4Q2PZ37ABZ_originalCrossPair_eq_energyPair]
  exact CompactEnergyMismatchMoment.signedPair_integral_eq_covariance μ b s _ E
    (p4Q2PZ37ABZ_receiver_continuous H b hb f e z)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

/-- Exact decomposition of the entire mismatch, retaining both the
absolute pair variation and the signed physical covariance. -/
theorem p4Q2PZ37ABZ_originalMismatch_eq_abs_covariance
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    mass b hb f e z (-s) =
      ((∫ w : G × G, |psi b hb f e z s w| ∂ν) +
        4 * b * s * CompactEnergyMismatchMoment.covariance μ (F b hb f e z) E) / 2 := by
  rw [p4Q2PZ37ABZ_originalMismatch_eq_energyMismatch,
    p4Q2PZ37ABZ_originalCrossPair_eq_energyPair]
  exact CompactEnergyMismatchMoment.mismatch_eq_abs_covariance μ b s _ E
    (p4Q2PZ37ABZ_receiver_continuous H b hb f e z)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

/-- Actual centered affine-energy residual variance of the same physical
source, for a chosen real slope. No residual bound is postulated. -/
def p4Q2PZ37ABZ_originalResidualVariance
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s a : ℝ) : ℝ :=
  CompactEnergyMismatchMoment.variance μ
    (CompactEnergyMismatchMoment.residual s a (F b hb f e z) E)
local notation "V" => p4Q2PZ37ABZ_originalResidualVariance H

/-- Quantitative complete mismatch bound from actual residual variance.
It applies to every physical source and every a>0, including b=0. -/
theorem p4Q2PZ37ABZ_originalMismatch_le_residualVariance
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s a : ℝ) (ha : 0 < a) :
    mass b hb f e z (-s) ≤ (b / a) * V b hb f e z s a := by
  rw [p4Q2PZ37ABZ_originalMismatch_eq_energyMismatch]
  exact CompactEnergyMismatchMoment.mismatch_le_residual_variance μ b s a hb ha
    (F b hb f e z) E (p4Q2PZ37ABZ_receiver_continuous H b hb f e z)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

/-- Genuine SU(2) specializes the exact residual variance polynomial,
without substituting a different receiver or energy. -/
theorem p4Q2PZ37ABZ_originalResidualVariance_eq_covariancePolynomial
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s a : ℝ) :
    V b hb f e z s a = CompactEnergyMismatchMoment.variance μ (F b hb f e z) +
      2 * s * a * CompactEnergyMismatchMoment.covariance μ (F b hb f e z) E +
        (s * a) ^ 2 / 4 := by
  unfold p4Q2PZ37ABZ_originalResidualVariance
  rw [CompactEnergyMismatchMoment.variance_residual μ s a _ E
    (p4Q2PZ37ABZ_receiver_continuous H b hb f e z)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2),
    p4Q2PZ37ABZ_originalEnergy_Haar_variance]
  ring

/-- Both full crossing parts obey the exact covariance balance. -/
theorem p4Q2PZ37ABZ_originalCrossParts_balance
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    mass b hb f e z s - mass b hb f e z (-s) =
      -4 * b * s * CompactEnergyMismatchMoment.covariance μ (F b hb f e z) E := by
  have h := integral_compactContinuous_eq_pos_sub_neg ν (psi b hb f e z s)
    (p4Q2PZ37ABY_originalCrossPair_continuous H b hb f e z s)
  have hn (w : G × G) : -(psi b hb f e z s w) = psi b hb f e z (-s) w := by
    unfold p4Q2PZ37ABY_originalCrossPair
    ring
  simp_rw [hn] at h
  rw [p4Q2PZ37ABZ_originalCrossPair_integral_eq_covariance] at h
  exact h.symm

/-- A nonnegative oriented actual covariance obstructs ABY's sufficient
positive margin. It is not a claim about the sign of the true GI gap. -/
theorem p4Q2PZ37ABZ_covariance_nonneg_obstructs_ABY_margin
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ)
    (hC : 0 ≤ s * CompactEnergyMismatchMoment.covariance μ (F b hb f e z) E) :
    (Real.exp (-32 * b) * mass b hb f e z s -
      Real.exp (32 * b) * mass b hb f e z (-s)) / 2 ≤ 0 := by
  have hbal := p4Q2PZ37ABZ_originalCrossParts_balance H b hb f e z s
  have hcross : 0 ≤ (4 * b) *
      (s * CompactEnergyMismatchMoment.covariance μ (F b hb f e z) E) :=
    mul_nonneg (by positivity) hC
  have horder : mass b hb f e z s ≤ mass b hb f e z (-s) := by nlinarith
  have hm : 0 ≤ mass b hb f e z (-s) := integral_nonneg (fun _ => le_max_right _ _)
  have he : Real.exp (-32 * b) ≤ Real.exp (32 * b) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h1 := mul_le_mul_of_nonneg_left horder (Real.exp_nonneg (-32 * b))
  have h2 := mul_le_mul_of_nonneg_right he hm
  linarith

/-- Bound the entire original posterior negative tail, using the proved
physical residual bound and ABY's unchanged determinant comparison. -/
theorem p4Q2PZ37ABZ_originalNegativeTail_le_residualVariance
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s a : ℝ) (ha : 0 < a) :
    p4Q2PZ37ABY_originalNegativeTail H b hb f e z s ≤
      Real.exp (32 * b) * ((b / a) * V b hb f e z s a) :=
  (p4Q2PZ37ABY_originalNegativeTail_twoSided H b hb f e z s).2.trans
    (mul_le_mul_of_nonneg_left
      (p4Q2PZ37ABZ_originalMismatch_le_residualVariance H b hb f e z s a ha)
      (Real.exp_nonneg (32 * b)))

/-- ABX's actual positive rectangle and the proved residual tail bound
give a full GI lower bound. Its positivity is not assumed or asserted. -/
theorem p4Q2PZ37ABZ_rectangle_GI_lower_with_residualVariance
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) (a : ℝ) (ha : 0 < a) :
    (R.eta * R.kappa * Real.exp (-32 * b) * Measure.real ν R.innerEvent -
      Real.exp (32 * b) * ((b / a) * V b hb f e z R.sign a)) / 2 ≤
        R.sign * gap b hb f e z := by
  have hGI := p4Q2PZ37ABY_rectangle_GI_lower_with_actualMismatch H b hb f e R z hz
  have hM := mul_le_mul_of_nonneg_left
    (p4Q2PZ37ABZ_originalMismatch_le_residualVariance H b hb f e z R.sign a ha)
    (Real.exp_nonneg (32 * b))
  linarith

/-- A verified residual margin on the actual outer rectangle controls
the original configuration pair-Haar second moment. The margin premise
is explicit; it is not derived uniformly in volume in this module. -/
theorem p4Q2PZ37ABZ_rectangle_outerMoment_lower_of_residualMargin
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (a delta : ℝ) (ha : 0 < a) (hdelta : 0 ≤ delta)
    (hMargin : ∀ z ∈ R.outerEvent,
      delta ≤ (R.eta * R.kappa * Real.exp (-32 * b) * Measure.real ν R.innerEvent -
        Real.exp (32 * b) * ((b / a) * V b hb f e z R.sign a)) / 2) :
    Measure.real outer R.outerEvent * delta ^ 2 ≤
      ∫ z : Cfg × Cfg, (gap b hb f e z) ^ 2 ∂outer := by
  have hs : R.sign ^ 2 = 1 := by
    rcases R.orientation with hs | hs <;> norm_num [hs]
  have hInt : Integrable (fun z : Cfg × Cfg => (gap b hb f e z) ^ 2) outer :=
    ((p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous H b hb f e).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) :
      delta ^ 2 ≤ (gap b hb f e z) ^ 2 := by
    have hd := (hMargin z hz).trans
      (p4Q2PZ37ABZ_rectangle_GI_lower_with_residualVariance H b hb f e R z hz a ha)
    have hsq := pow_le_pow_left₀ hdelta hd 2
    simpa only [mul_pow, hs, one_mul] using hsq
  have hSet : delta ^ 2 * Measure.real outer R.outerEvent ≤
      ∫ z in R.outerEvent, (gap b hb f e z) ^ 2 ∂outer :=
    setIntegral_ge_of_const_le_real R.outer_open.measurableSet (measure_ne_top _ _)
      hPoint hInt.integrableOn
  have hFull : (∫ z in R.outerEvent, (gap b hb f e z) ^ 2 ∂outer) ≤
      ∫ z : Cfg × Cfg, (gap b hb f e z) ^ 2 ∂outer :=
    setIntegral_le_integral hInt (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  simpa only [mul_comm] using hSet.trans hFull

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABZ_originalEnergy_Haar_mean
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABZ_originalEnergy_Haar_second
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABZ_originalEnergy_Haar_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalCrossPair_eq_energyPair
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalMismatch_eq_energyMismatch
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalCrossPair_integral_eq_covariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalMismatch_eq_abs_covariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalMismatch_le_residualVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalResidualVariance_eq_covariancePolynomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalCrossParts_balance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_covariance_nonneg_obstructs_ABY_margin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_originalNegativeTail_le_residualVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_rectangle_GI_lower_with_residualVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABZ_rectangle_outerMoment_lower_of_residualMargin
