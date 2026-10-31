import MGAP4D.MathlibAnalytic.CompactEnergyMismatchOptimization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferRegressionV5_PZ37ACA

/-!
# P4-Q2-PZ37ACA — optimized actual Wilson mismatch certificate

For the SAME original receiver, the complete mismatch is at most
b*(sqrt(Var F)+2*s*Cov(F,E)) for s^2=1. This is exactly the infimum of
ABZ's positive-slope residual budgets, with an explicit nonnegative
square remainder. The true Perron section gives the identical budget
b*P*(sqrt(Var U)-2*s*Cov(U,E)). No small physical covariance defect is
postulated. The original FC bound also controls the receiver variance.

On ABX's actual positive rectangle, Var F >= eta^2*nu(V)/2 > 0, so the
optimal slope is positive and attained there. Existence of a positive
ABZ residual certificate at one outer point is characterized exactly.
The optimized GI bound feeds the original outer pair-Haar moment without
asserting that one slope works on the entire outer event. Actual margin
smallness, H-uniformity, distant cancellation and coercivity remain open.
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
local instance p4Q2PZ37ACA_certificateGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACA_certificateCompact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACA_certificateCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACA_certificateMeasurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACA_certificateBorel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACA_certificateProbability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local instance p4Q2PZ37ACA_certificateLinks : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACA_certificateOuterProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local notation "transfer" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
  H 2 (by norm_num)
local notation "V" => p4Q2PZ37ABZ_originalResidualVariance H
local notation "mass" => p4Q2PZ37ABY_originalCrossPartMass H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local notation "Cov" => CompactEnergyMismatchMoment.covariance μ

private theorem p4Q2PZ37ACA_certificate_receiver_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Continuous (F b hb f e z) :=
  (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num) b hb f e).continuous.comp
    (continuous_const.prodMk continuous_id)

private theorem p4Q2PZ37ACA_certificate_sign_sq
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e) : R.sign ^ 2 = 1 := by
  rcases R.orientation with hs | hs <;> norm_num [hs]

/-- Exact optimal budget within the unchanged ABZ residual family. -/
def p4Q2PZ37ACA_originalOptimizedMismatchBound
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) : ℝ :=
  CompactEnergyMismatchMoment.optimalBudget b s (Var (F b hb f e z)) (Cov (F b hb f e z) E)
local notation "B" => p4Q2PZ37ACA_originalOptimizedMismatchBound H

/-- The full original mismatch admits a bound with no free positive slope. -/
theorem p4Q2PZ37ACA_originalMismatch_le_optimized
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (hs : s ^ 2 = 1) : mass b hb f e z (-s) ≤ B b hb f e z s := by
  rw [p4Q2PZ37ABZ_originalMismatch_eq_energyMismatch]
  exact CompactEnergyMismatchMoment.mismatch_le_optimized μ b s hb hs
    (F b hb f e z) E (p4Q2PZ37ACA_certificate_receiver_continuous H b hb f e z)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2) p4Q2PZ37ABZ_originalEnergy_Haar_variance

theorem p4Q2PZ37ACA_originalOptimizedMismatchBound_nonneg
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (hs : s ^ 2 = 1) : 0 ≤ B b hb f e z s := by
  have hm : (0 : ℝ) ≤ mass b hb f e z (-s) :=
    integral_nonneg (fun _ => le_max_right _ _)
  exact hm.trans (p4Q2PZ37ACA_originalMismatch_le_optimized H b hb f e z s hs)

/-- True physical transfer-section formula, with its original positive P. -/
theorem p4Q2PZ37ACA_originalOptimizedMismatchBound_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    B b hb f e z s = b * P b hb z *
      (Real.sqrt (Var (U b hb f e z)) - 2 * s * Cov (U b hb f e z) E) := by
  unfold p4Q2PZ37ACA_originalOptimizedMismatchBound CompactEnergyMismatchMoment.optimalBudget
  rw [p4Q2PZ37ACA_originalReceiver_stddev_eq_transfer,
    p4Q2PZ37ACA_originalReceiver_covariance_eq_transfer]
  ring

/-- An explicit original source-norm bound retains the actual covariance
term. The transfer norm and its volume dependence are not replaced. -/
theorem p4Q2PZ37ACA_originalMismatch_le_FC_covariance
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (hs : s ^ 2 = 1) :
    mass b hb f e z (-s) ≤ b *
      (‖transfer b hb‖⁻¹ * (Real.exp (8 * b) ^ 3 - 1) * ‖f‖ +
        2 * s * Cov (F b hb f e z) E) := by
  have hσ := p4Q2PZ37ACA_originalReceiver_stddev_le_FC H b hb f e z
  have hbound := mul_le_mul_of_nonneg_left
    (add_le_add hσ (le_refl (2 * s * Cov (F b hb f e z) E))) hb
  exact (p4Q2PZ37ACA_originalMismatch_le_optimized H b hb f e z s hs).trans hbound

/-- The true transfer-section regression defect is nonnegative without
any postulated cap or locality property. -/
theorem p4Q2PZ37ACA_originalTransferRegressionDefect_nonneg
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    0 ≤ Var (U b hb f e z) - 4 * (Cov (U b hb f e z) E) ^ 2 := by
  exact CompactEnergyMismatchMoment.regressionDefect_nonneg μ (U b hb f e z) E
    (p4Q2PZ37ABZ_originalTransferSection_continuous H b hb f e z)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2) p4Q2PZ37ABZ_originalEnergy_Haar_variance

/-- The unchanged residual budget is the scalar quadratic budget exactly. -/
theorem p4Q2PZ37ACA_originalResidualBudget_eq_quadratic
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s a : ℝ) (hs : s ^ 2 = 1) :
    (b / a) * V b hb f e z s a =
      CompactEnergyMismatchMoment.quadraticBudget b s (Var (F b hb f e z))
        (Cov (F b hb f e z) E) a := by
  unfold CompactEnergyMismatchMoment.quadraticBudget
  rw [p4Q2PZ37ABZ_originalResidualVariance_eq_covariancePolynomial, mul_pow, hs, one_mul]

/-- Exact excess above the optimal original-source budget. -/
theorem p4Q2PZ37ACA_originalResidualBudget_gap
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s a : ℝ) (hs : s ^ 2 = 1) (ha : 0 < a) :
    (b / a) * V b hb f e z s a - B b hb f e z s =
      (b / (4 * a)) * (a - 2 * Real.sqrt (Var (F b hb f e z))) ^ 2 := by
  rw [p4Q2PZ37ACA_originalResidualBudget_eq_quadratic H b hb f e z s a hs]
  exact CompactEnergyMismatchMoment.quadraticBudget_sub_optimal b s
    (Var (F b hb f e z)) (Cov (F b hb f e z) E) a
    (CompactEnergyMismatchMoment.variance_nonneg μ _
      (p4Q2PZ37ACA_certificate_receiver_continuous H b hb f e z)) ha

/-- A strict threshold can be reached by a positive slope exactly when
it exceeds the optimal budget, including the zero-variance endpoint. -/
theorem p4Q2PZ37ACA_originalResidualBudget_exists_lt_iff
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s t : ℝ) (hs : s ^ 2 = 1) :
    (∃ a : ℝ, 0 < a ∧ (b / a) * V b hb f e z s a < t) ↔ B b hb f e z s < t := by
  have hq (a : ℝ) := p4Q2PZ37ACA_originalResidualBudget_eq_quadratic H b hb f e z s a hs
  simp_rw [hq]
  exact CompactEnergyMismatchMoment.exists_quadraticBudget_lt_iff b s
    (Var (F b hb f e z)) (Cov (F b hb f e z) E) t hb
    (CompactEnergyMismatchMoment.variance_nonneg μ _
      (p4Q2PZ37ACA_certificate_receiver_continuous H b hb f e z))

/-- Actual ABX amplitude and mass force a quantitative receiver variance.
The region is ABX's own V, with no fixed-cap mass substituted. -/
theorem p4Q2PZ37ACA_rectangle_receiverVariance_lower
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) :
    R.eta ^ 2 * Measure.real ν R.innerEvent / 2 ≤ Var (F b hb f e z) := by
  have hs := p4Q2PZ37ACA_certificate_sign_sq H b hb f e R
  have hF := p4Q2PZ37ACA_certificate_receiver_continuous H b hb f e z
  have hInt : Integrable (fun w : G × G => (F b hb f e z w.1 - F b hb f e z w.2) ^ 2) ν :=
    (((hF.comp continuous_fst).sub (hF.comp continuous_snd)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (w : G × G) (hw : w ∈ R.innerEvent) :
      R.eta ^ 2 ≤ (F b hb f e z w.1 - F b hb f e z w.2) ^ 2 := by
    have hη := (R.aligned z hz w hw).1
    change R.eta ≤ R.sign * (F b hb f e z w.1 - F b hb f e z w.2) at hη
    have hsq := pow_le_pow_left₀ R.eta_pos.le hη 2
    simpa only [mul_pow, hs, one_mul] using hsq
  have hSet : R.eta ^ 2 * Measure.real ν R.innerEvent ≤
      ∫ w in R.innerEvent, (F b hb f e z w.1 - F b hb f e z w.2) ^ 2 ∂ν :=
    setIntegral_ge_of_const_le_real R.inner_open.measurableSet (measure_ne_top _ _)
      hPoint hInt.integrableOn
  have hFull : (∫ w in R.innerEvent, (F b hb f e z w.1 - F b hb f e z w.2) ^ 2 ∂ν) ≤
      ∫ w : G × G, (F b hb f e z w.1 - F b hb f e z w.2) ^ 2 ∂ν :=
    setIntegral_le_integral hInt (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  have h := hSet.trans hFull
  rw [CompactEnergyMismatchMoment.difference_square_integral μ _ hF] at h
  linarith

theorem p4Q2PZ37ACA_rectangle_receiverVariance_pos
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) : 0 < Var (F b hb f e z) := by
  have hpos : 0 < R.eta ^ 2 * Measure.real ν R.innerEvent / 2 :=
    div_pos (mul_pos (pow_pos R.eta_pos 2) R.inner_mass_pos) (by norm_num)
  exact hpos.trans_le (p4Q2PZ37ACA_rectangle_receiverVariance_lower H b hb f e R z hz)

/-- The actual aligned rectangle excludes the zero-variance endpoint,
so its optimal slope is positive and the infimum is attained. -/
theorem p4Q2PZ37ACA_rectangle_optimalSlope_attained
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) :
    0 < 2 * Real.sqrt (Var (F b hb f e z)) ∧
      (b / (2 * Real.sqrt (Var (F b hb f e z)))) *
        V b hb f e z R.sign (2 * Real.sqrt (Var (F b hb f e z))) = B b hb f e z R.sign := by
  have hv := p4Q2PZ37ACA_rectangle_receiverVariance_pos H b hb f e R z hz
  refine ⟨mul_pos (by norm_num) (Real.sqrt_pos.mpr hv), ?_⟩
  rw [p4Q2PZ37ACA_originalResidualBudget_eq_quadratic H b hb f e z R.sign _
    (p4Q2PZ37ACA_certificate_sign_sq H b hb f e R)]
  exact CompactEnergyMismatchMoment.quadraticBudget_at_sqrt b R.sign
    (Var (F b hb f e z)) (Cov (F b hb f e z) E) hv

/-- The original interacting posterior negative tail retains its full
domain and is bounded by the optimized actual-source budget. -/
theorem p4Q2PZ37ACA_originalNegativeTail_le_optimized
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (hs : s ^ 2 = 1) :
    p4Q2PZ37ABY_originalNegativeTail H b hb f e z s ≤ Real.exp (32 * b) * B b hb f e z s :=
  (p4Q2PZ37ABY_originalNegativeTail_twoSided H b hb f e z s).2.trans
    (mul_le_mul_of_nonneg_left
      (p4Q2PZ37ACA_originalMismatch_le_optimized H b hb f e z s hs) (Real.exp_nonneg _))

/-- Threshold for a positive certificate from ABX's actual inner rectangle. -/
def p4Q2PZ37ACA_originalRectangleThreshold
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e) : ℝ :=
  Real.exp (-64 * b) * R.eta * R.kappa * Measure.real ν R.innerEvent
local notation "T" => p4Q2PZ37ACA_originalRectangleThreshold H

/-- The supremum of the residual family's lower margins. It is attained
on the actual outer event, where the receiver variance is positive. -/
def p4Q2PZ37ACA_originalRectangleOptimizedMargin
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e) (z : Cfg × Cfg) : ℝ :=
  (R.eta * R.kappa * Real.exp (-32 * b) * Measure.real ν R.innerEvent -
    Real.exp (32 * b) * B b hb f e z R.sign) / 2
local notation "L" => p4Q2PZ37ACA_originalRectangleOptimizedMargin H

private theorem p4Q2PZ37ACA_scalarMargin_pos_iff
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e) (q : ℝ) :
    0 < (R.eta * R.kappa * Real.exp (-32 * b) * Measure.real ν R.innerEvent -
      Real.exp (32 * b) * q) / 2 ↔ q < T b hb f e R := by
  have he : Real.exp (-32 * b) = Real.exp (32 * b) * Real.exp (-64 * b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcoef : R.eta * R.kappa * Real.exp (-32 * b) * Measure.real ν R.innerEvent =
      Real.exp (32 * b) * T b hb f e R := by
    unfold p4Q2PZ37ACA_originalRectangleThreshold
    rw [he]
    ring
  rw [hcoef]
  constructor
  · intro h
    by_contra hn
    have hq : T b hb f e R ≤ q := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_left hq (Real.exp_nonneg (32 * b))
    linarith
  · intro hq
    have hm := mul_lt_mul_of_pos_left hq (Real.exp_pos (32 * b))
    linarith

/-- Exact pointwise existence criterion for a strictly positive ABZ
residual certificate. It makes no claim of one slope common to all z. -/
theorem p4Q2PZ37ACA_rectangle_positiveResidualCertificate_iff
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e) (z : Cfg × Cfg) :
    (∃ a : ℝ, 0 < a ∧
      0 < (R.eta * R.kappa * Real.exp (-32 * b) * Measure.real ν R.innerEvent -
        Real.exp (32 * b) * ((b / a) * V b hb f e z R.sign a)) / 2) ↔
      B b hb f e z R.sign < T b hb f e R := by
  simp_rw [p4Q2PZ37ACA_scalarMargin_pos_iff H b hb f e R]
  exact p4Q2PZ37ACA_originalResidualBudget_exists_lt_iff H b hb f e z R.sign
    (T b hb f e R) (p4Q2PZ37ACA_certificate_sign_sq H b hb f e R)

/-- If the optimized threshold fails, no positive slope repairs this
certificate family. This does not determine the sign of the true GI gap. -/
theorem p4Q2PZ37ACA_rectangle_no_positiveResidualCertificate
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e) (z : Cfg × Cfg)
    (hfail : T b hb f e R ≤ B b hb f e z R.sign) :
    ∀ a : ℝ, 0 < a →
      (R.eta * R.kappa * Real.exp (-32 * b) * Measure.real ν R.innerEvent -
        Real.exp (32 * b) * ((b / a) * V b hb f e z R.sign a)) / 2 ≤ 0 := by
  intro a ha
  by_contra hn
  have hp := (p4Q2PZ37ACA_rectangle_positiveResidualCertificate_iff H b hb f e R z).mp
    ⟨a, ha, lt_of_not_ge hn⟩
  exact (not_lt_of_ge hfail) hp

/-- The original full GI response is bounded below by the optimized
margin without choosing a slope simultaneously on the whole event. -/
theorem p4Q2PZ37ACA_rectangle_GI_lower_optimized
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) : L b hb f e R z ≤ R.sign * gap b hb f e z := by
  have hGI := p4Q2PZ37ABY_rectangle_GI_lower_with_actualMismatch H b hb f e R z hz
  have hM := mul_le_mul_of_nonneg_left
    (p4Q2PZ37ACA_originalMismatch_le_optimized H b hb f e z R.sign
      (p4Q2PZ37ACA_certificate_sign_sq H b hb f e R)) (Real.exp_nonneg (32 * b))
  unfold p4Q2PZ37ACA_originalRectangleOptimizedMargin
  linarith

theorem p4Q2PZ37ACA_rectangle_GI_pos_of_optimizedCertificate
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent)
    (hcert : B b hb f e z R.sign < T b hb f e R) : 0 < R.sign * gap b hb f e z := by
  have hm : 0 < L b hb f e R z :=
    (p4Q2PZ37ACA_scalarMargin_pos_iff H b hb f e R (B b hb f e z R.sign)).mpr hcert
  exact hm.trans_le (p4Q2PZ37ACA_rectangle_GI_lower_optimized H b hb f e R z hz)

/-- Original outer-Haar moment from a verified optimized margin, with
no common-slope or measurable-slope-selection hypothesis. -/
theorem p4Q2PZ37ACA_rectangle_outerMoment_lower_of_optimizedMargin
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hMargin : ∀ z ∈ R.outerEvent, delta ≤ L b hb f e R z) :
    Measure.real outer R.outerEvent * delta ^ 2 ≤
      ∫ z : Cfg × Cfg, (gap b hb f e z) ^ 2 ∂outer := by
  have hs := p4Q2PZ37ACA_certificate_sign_sq H b hb f e R
  have hInt : Integrable (fun z : Cfg × Cfg => (gap b hb f e z) ^ 2) outer :=
    ((p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous H b hb f e).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) : delta ^ 2 ≤ (gap b hb f e z) ^ 2 := by
    have hd := (hMargin z hz).trans (p4Q2PZ37ACA_rectangle_GI_lower_optimized H b hb f e R z hz)
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

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalMismatch_le_optimized
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalOptimizedMismatchBound_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalOptimizedMismatchBound_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalMismatch_le_FC_covariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalTransferRegressionDefect_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalResidualBudget_eq_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalResidualBudget_gap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalResidualBudget_exists_lt_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_rectangle_receiverVariance_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_rectangle_receiverVariance_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_rectangle_optimalSlope_attained
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_originalNegativeTail_le_optimized
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_rectangle_positiveResidualCertificate_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_rectangle_no_positiveResidualCertificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_rectangle_GI_lower_optimized
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_rectangle_GI_pos_of_optimizedCertificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACA_rectangle_outerMoment_lower_of_optimizedMargin
