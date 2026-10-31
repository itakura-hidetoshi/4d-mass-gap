import MGAP4D.MathlibAnalytic.CompactEnergyMismatchDefect
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOptimizedMismatchCertificateV5_PZ37ACA

/-!
# P4-Q2-PZ37ACB — direct covariance bounds for the original full GI response

The complete ABY positive/negative sandwich and the exact ABZ part balance
give a direct two-sided GI envelope from ACA's actual mismatch bound.
No rectangle or small-tail hypothesis is used. In particular an upper
bound for the positive mass is never used as a lower bound.

The center and error use the SAME original FF receiver, actual Haar
variance/covariance and both interacting posterior laws. Exact defect
criteria describe when this lower envelope is positive; their validity
for the genuine centered source is not postulated. The original Perron
section and transfer norm are retained. Volume uniformity remains open.
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
local instance p4Q2PZ37ACB_covarianceGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACB_covarianceCompact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACB_covarianceCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACB_covarianceMeasurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACB_covarianceBorel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACB_covarianceProbability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local instance p4Q2PZ37ACB_covarianceLinks : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACB_covarianceOuterProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "B" => p4Q2PZ37ACA_originalOptimizedMismatchBound H
local notation "mass" => p4Q2PZ37ABY_originalCrossPartMass H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local notation "Cov" => CompactEnergyMismatchMoment.covariance μ

private theorem p4Q2PZ37ACB_covariance_receiver_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Continuous (F b hb f e z) :=
  (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num) b hb f e).continuous.comp
    (continuous_const.prodMk continuous_id)

private theorem p4Q2PZ37ACB_expWidth_nonneg (b : ℝ) (hb : 0 ≤ b) :
    0 ≤ Real.exp (32 * b) - Real.exp (-32 * b) :=
  sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith))

/-- The direct signed lower envelope from the entire original part balance. -/
def p4Q2PZ37ACB_originalCovarianceGIMargin
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) : ℝ :=
  -b * (Real.exp (32 * b) + Real.exp (-32 * b)) * s * Cov (F b hb f e z) E -
    (b / 2) * (Real.exp (32 * b) - Real.exp (-32 * b)) *
      Real.sqrt (Var (F b hb f e z))
local notation "L" => p4Q2PZ37ACB_originalCovarianceGIMargin H

/-- An orientation-free pointwise lower margin for the absolute GI response. -/
def p4Q2PZ37ACB_originalAbsoluteCovarianceGIMargin
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) : ℝ :=
  b * (Real.exp (32 * b) + Real.exp (-32 * b)) * |Cov (F b hb f e z) E| -
    (b / 2) * (Real.exp (32 * b) - Real.exp (-32 * b)) *
      Real.sqrt (Var (F b hb f e z))
local notation "LAbs" => p4Q2PZ37ACB_originalAbsoluteCovarianceGIMargin H

/-- Full GI envelope, with no inner rectangle, tail-cap or source-profile
hypothesis. The exact signed balance is essential in both inequalities. -/
theorem p4Q2PZ37ACB_originalGI_covariance_twoSided
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (hs : s ^ 2 = 1) :
    L b hb f e z s ≤ s * gap b hb f e z ∧
      s * gap b hb f e z ≤
        -b * (Real.exp (32 * b) + Real.exp (-32 * b)) * s * Cov (F b hb f e z) E +
          (b / 2) * (Real.exp (32 * b) - Real.exp (-32 * b)) *
            Real.sqrt (Var (F b hb f e z)) := by
  have hGI := p4Q2PZ37ABY_originalGI_signed_twoSided H b hb f e z s
  have hBalance := p4Q2PZ37ABZ_originalCrossParts_balance H b hb f e z s
  have hM := p4Q2PZ37ACA_originalMismatch_le_optimized H b hb f e z s hs
  change mass b hb f e z (-s) ≤
    b * (Real.sqrt (Var (F b hb f e z)) + 2 * s * Cov (F b hb f e z) E) at hM
  have hScaled := mul_le_mul_of_nonneg_left hM (p4Q2PZ37ACB_expWidth_nonneg b hb)
  have hLowerBalance := congrArg (fun x : ℝ => Real.exp (-32 * b) * x) hBalance
  have hUpperBalance := congrArg (fun x : ℝ => Real.exp (32 * b) * x) hBalance
  unfold p4Q2PZ37ACB_originalCovarianceGIMargin
  constructor
  · nlinarith [hGI.1]
  · nlinarith [hGI.2]

/-- The actual GI is close to its actual covariance center, with an
explicit error controlled by the receiver standard deviation. -/
theorem p4Q2PZ37ACB_originalGI_abs_covariance_error
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    |gap b hb f e z +
      b * (Real.exp (32 * b) + Real.exp (-32 * b)) * Cov (F b hb f e z) E| ≤
      (b / 2) * (Real.exp (32 * b) - Real.exp (-32 * b)) *
        Real.sqrt (Var (F b hb f e z)) := by
  have h := p4Q2PZ37ACB_originalGI_covariance_twoSided H b hb f e z 1 (by norm_num)
  dsimp [p4Q2PZ37ACB_originalCovarianceGIMargin] at h
  simp only [one_mul, mul_one] at h
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The same error can be bounded by the proved FF/FC source norm bound.
The actual transfer norm and its volume dependence remain explicit. -/
theorem p4Q2PZ37ACB_originalGI_abs_covariance_error_le_FC
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    |gap b hb f e z +
      b * (Real.exp (32 * b) + Real.exp (-32 * b)) * Cov (F b hb f e z) E| ≤
      (b / 2) * (Real.exp (32 * b) - Real.exp (-32 * b)) *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) b hb‖⁻¹ * (Real.exp (8 * b) ^ 3 - 1) * ‖f‖) := by
  have hc : 0 ≤ (b / 2) * (Real.exp (32 * b) - Real.exp (-32 * b)) :=
    mul_nonneg (div_nonneg hb (by norm_num)) (p4Q2PZ37ACB_expWidth_nonneg b hb)
  exact (p4Q2PZ37ACB_originalGI_abs_covariance_error H b hb f e z).trans
    (mul_le_mul_of_nonneg_left
      (p4Q2PZ37ACA_originalReceiver_stddev_le_FC H b hb f e z) hc)

/-- Absolute-response control needs no fixed orientation over outer contexts. -/
theorem p4Q2PZ37ACB_originalGI_abs_lower
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    LAbs b hb f e z ≤ |gap b hb f e z| := by
  unfold p4Q2PZ37ACB_originalAbsoluteCovarianceGIMargin
  by_cases hC : 0 ≤ Cov (F b hb f e z) E
  · rw [abs_of_nonneg hC]
    have h := (p4Q2PZ37ACB_originalGI_covariance_twoSided H b hb f e z (-1)
      (by norm_num)).1
    dsimp [p4Q2PZ37ACB_originalCovarianceGIMargin] at h
    nlinarith [neg_le_abs (gap b hb f e z)]
  · rw [abs_of_nonpos (lt_of_not_ge hC).le]
    have h := (p4Q2PZ37ACB_originalGI_covariance_twoSided H b hb f e z 1
      (by norm_num)).1
    dsimp [p4Q2PZ37ACB_originalCovarianceGIMargin] at h
    nlinarith [le_abs_self (gap b hb f e z)]

/-- Exact Perron-section expression, with the physical covariance sign
reversal and the true positive prefactor retained. -/
theorem p4Q2PZ37ACB_originalCovarianceGIMargin_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    L b hb f e z s = P b hb z *
      (b * (Real.exp (32 * b) + Real.exp (-32 * b)) * s * Cov (U b hb f e z) E -
        (b / 2) * (Real.exp (32 * b) - Real.exp (-32 * b)) *
          Real.sqrt (Var (U b hb f e z))) := by
  unfold p4Q2PZ37ACB_originalCovarianceGIMargin
  rw [p4Q2PZ37ACA_originalReceiver_covariance_eq_transfer,
    p4Q2PZ37ACA_originalReceiver_stddev_eq_transfer]
  ring

/-- Direct GI error written in the original updated Perron transfer section. -/
theorem p4Q2PZ37ACB_originalGI_abs_transfer_covariance_error
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    |gap b hb f e z -
      b * (Real.exp (32 * b) + Real.exp (-32 * b)) * P b hb z * Cov (U b hb f e z) E| ≤
      (b / 2) * (Real.exp (32 * b) - Real.exp (-32 * b)) * P b hb z *
        Real.sqrt (Var (U b hb f e z)) := by
  have h := p4Q2PZ37ACB_originalGI_abs_covariance_error H b hb f e z
  rw [p4Q2PZ37ACA_originalReceiver_covariance_eq_transfer,
    p4Q2PZ37ACA_originalReceiver_stddev_eq_transfer] at h
  calc
    _ = |gap b hb f e z +
        b * (Real.exp (32 * b) + Real.exp (-32 * b)) *
          (-(P b hb z) * Cov (U b hb f e z) E)| := by
      congr 1
      ring
    _ ≤ (b / 2) * (Real.exp (32 * b) - Real.exp (-32 * b)) *
        (P b hb z * Real.sqrt (Var (U b hb f e z))) := h
    _ = _ := by ring

/-- The direct lower envelope expressed through the two opposite optimized
budgets. This is an algebraic identity, not a positive-mass lower estimate. -/
theorem p4Q2PZ37ACB_originalCovarianceGIMargin_eq_budgetDifference
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    L b hb f e z s =
      (Real.exp (-32 * b) * B b hb f e z (-s) -
        Real.exp (32 * b) * B b hb f e z s) / 2 := by
  unfold p4Q2PZ37ACB_originalCovarianceGIMargin
    p4Q2PZ37ACA_originalOptimizedMismatchBound CompactEnergyMismatchMoment.optimalBudget
  ring

/-- Positivity of the direct bound is exactly an opposite-budget ratio test. -/
theorem p4Q2PZ37ACB_covarianceMargin_pos_iff_budgetRatio
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    0 < L b hb f e z s ↔
      B b hb f e z s < Real.exp (-64 * b) * B b hb f e z (-s) := by
  rw [p4Q2PZ37ACB_originalCovarianceGIMargin_eq_budgetDifference]
  have he : Real.exp (-32 * b) = Real.exp (32 * b) * Real.exp (-64 * b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  constructor
  · intro h
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (Real.exp_nonneg (32 * b))
    nlinarith
  · intro h
    have hm := mul_lt_mul_of_pos_left h (Real.exp_pos (32 * b))
    nlinarith

/-- Exact favorable-sign and relative-defect criterion for positivity of
this lower bound. It does not assert that the physical source satisfies it. -/
theorem p4Q2PZ37ACB_covarianceMargin_pos_iff_defect
    (b : ℝ) (hb : 0 < b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (hs : s ^ 2 = 1) :
    0 < L b hb.le f e z s ↔
      s * Cov (F b hb.le f e z) E < 0 ∧
        (1 + Real.exp (-64 * b)) ^ 2 *
            (Var (F b hb.le f e z) - 4 * (Cov (F b hb.le f e z) E) ^ 2) <
          4 * Real.exp (-64 * b) * Var (F b hb.le f e z) := by
  rw [p4Q2PZ37ACB_covarianceMargin_pos_iff_budgetRatio]
  have hv := CompactEnergyMismatchMoment.variance_nonneg μ (F b hb.le f e z)
    (p4Q2PZ37ACB_covariance_receiver_continuous H b hb.le f e z)
  have hr1 : Real.exp (-64 * b) ≤ 1 := by
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith [hb.le])
      _ = 1 := Real.exp_zero
  exact CompactEnergyMismatchMoment.optimalBudget_lt_mul_opposite_iff_defect
    b s (Var (F b hb.le f e z)) (Cov (F b hb.le f e z) E) (Real.exp (-64 * b))
    hb hv hs (Real.exp_nonneg _) hr1

/-- The proved actual covariance/defect criterion implies signed GI positivity. -/
theorem p4Q2PZ37ACB_originalGI_pos_of_covarianceDefect
    (b : ℝ) (hb : 0 < b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (hs : s ^ 2 = 1)
    (hC : s * Cov (F b hb.le f e z) E < 0)
    (hD : (1 + Real.exp (-64 * b)) ^ 2 *
        (Var (F b hb.le f e z) - 4 * (Cov (F b hb.le f e z) E) ^ 2) <
      4 * Real.exp (-64 * b) * Var (F b hb.le f e z)) :
    0 < s * gap b hb.le f e z :=
  ((p4Q2PZ37ACB_covarianceMargin_pos_iff_defect H b hb f e z s hs).mpr ⟨hC, hD⟩).trans_le
    (p4Q2PZ37ACB_originalGI_covariance_twoSided H b hb.le f e z s hs).1


/-- Positivity criterion in the SAME actual transfer section. The strictly
positive Perron factor cancels from this relative defect test. -/
theorem p4Q2PZ37ACB_covarianceMargin_pos_iff_transferDefect
    (b : ℝ) (hb : 0 < b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (hs : s ^ 2 = 1) :
    0 < L b hb.le f e z s ↔
      0 < s * Cov (U b hb.le f e z) E ∧
        (1 + Real.exp (-64 * b)) ^ 2 *
            (Var (U b hb.le f e z) - 4 * (Cov (U b hb.le f e z) E) ^ 2) <
          4 * Real.exp (-64 * b) * Var (U b hb.le f e z) := by
  have hSign : s * Cov (F b hb.le f e z) E < 0 ↔
      0 < s * Cov (U b hb.le f e z) E := by
    have h := not_congr (p4Q2PZ37ACA_covariance_obstruction_iff_transfer H b hb.le f e z s)
    simpa only [not_le] using h
  have hp2 : 0 < (P b hb.le z) ^ 2 :=
    pow_pos (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb.le z) 2
  have hDefect :
      (1 + Real.exp (-64 * b)) ^ 2 *
          (Var (F b hb.le f e z) - 4 * (Cov (F b hb.le f e z) E) ^ 2) <
        4 * Real.exp (-64 * b) * Var (F b hb.le f e z) ↔
      (1 + Real.exp (-64 * b)) ^ 2 *
          (Var (U b hb.le f e z) - 4 * (Cov (U b hb.le f e z) E) ^ 2) <
        4 * Real.exp (-64 * b) * Var (U b hb.le f e z) := by
    rw [p4Q2PZ37ACA_originalRegressionDefect_eq_transfer,
      p4Q2PZ37ACA_originalReceiver_variance_eq_transfer]
    constructor
    · intro h
      by_contra hn
      have hScaled := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hp2.le
      nlinarith only [h, hScaled]
    · intro h
      have hScaled := mul_lt_mul_of_pos_left h hp2
      nlinarith only [hScaled]
  exact (p4Q2PZ37ACB_covarianceMargin_pos_iff_defect H b hb f e z s hs).trans
    (and_congr hSign hDefect)

/-- The actual full mismatch is controlled by the square root of the
actual regression defect when its actual covariance has the favorable sign. -/
theorem p4Q2PZ37ACB_originalMismatch_le_sqrtDefect
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (hs : s ^ 2 = 1) (hC : s * Cov (F b hb f e z) E ≤ 0) :
    mass b hb f e z (-s) ≤
      b * Real.sqrt (Var (F b hb f e z) - 4 * (Cov (F b hb f e z) E) ^ 2) := by
  rw [p4Q2PZ37ABZ_originalMismatch_eq_energyMismatch]
  exact CompactEnergyMismatchMoment.mismatch_le_sqrt_regressionDefect μ b s hb hs
    (F b hb f e z) E (p4Q2PZ37ACB_covariance_receiver_continuous H b hb f e z)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2) p4Q2PZ37ABZ_originalEnergy_Haar_variance hC

/-- Entire original posterior negative tail from the same genuine defect. -/
theorem p4Q2PZ37ACB_originalNegativeTail_le_sqrtDefect
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (hs : s ^ 2 = 1) (hC : s * Cov (F b hb f e z) E ≤ 0) :
    p4Q2PZ37ABY_originalNegativeTail H b hb f e z s ≤
      Real.exp (32 * b) *
        (b * Real.sqrt (Var (F b hb f e z) - 4 * (Cov (F b hb f e z) E) ^ 2)) :=
  (p4Q2PZ37ABY_originalNegativeTail_twoSided H b hb f e z s).2.trans
    (mul_le_mul_of_nonneg_left
      (p4Q2PZ37ACB_originalMismatch_le_sqrtDefect H b hb f e z s hs hC)
      (Real.exp_nonneg _))

/-- The complete covariance balance improves the existing ACA rectangle
margin that uses the SAME optimized mismatch budget. The actual ABX mass
is retained in the comparison; no fixed cap is substituted. -/
theorem p4Q2PZ37ACB_rectangle_optimizedMargin_le_covarianceMargin
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) :
    p4Q2PZ37ACA_originalRectangleOptimizedMargin H b hb f e R z ≤ L b hb f e z R.sign := by
  have hs : R.sign ^ 2 = 1 := by
    rcases R.orientation with h | h <;> norm_num [h]
  have hsneg : (-R.sign) ^ 2 = 1 := by simpa only [neg_sq] using hs
  have hPlus := p4Q2PZ37ACA_originalMismatch_le_optimized H b hb f e z (-R.sign) hsneg
  simp only [neg_neg] at hPlus
  have hWindow := (p4Q2PZ37ABY_rectangle_crossPositive_mass_lower H b hb f e R z hz).trans hPlus
  have hScaled := mul_le_mul_of_nonneg_left hWindow (Real.exp_nonneg (-32 * b))
  rw [p4Q2PZ37ACB_originalCovarianceGIMargin_eq_budgetDifference]
  unfold p4Q2PZ37ACA_originalRectangleOptimizedMargin
  nlinarith

/-- A positive existing rectangle margin necessarily passes the new
favorable-sign and relative-defect test on that same outer point. -/
theorem p4Q2PZ37ACB_rectangle_positiveMargin_implies_covarianceDefect
    (b : ℝ) (hb : 0 < b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb.le f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent)
    (hMargin : 0 < p4Q2PZ37ACA_originalRectangleOptimizedMargin H b hb.le f e R z) :
    R.sign * Cov (F b hb.le f e z) E < 0 ∧
      (1 + Real.exp (-64 * b)) ^ 2 *
          (Var (F b hb.le f e z) - 4 * (Cov (F b hb.le f e z) E) ^ 2) <
        4 * Real.exp (-64 * b) * Var (F b hb.le f e z) := by
  have hs : R.sign ^ 2 = 1 := by
    rcases R.orientation with h | h <;> norm_num [h]
  exact (p4Q2PZ37ACB_covarianceMargin_pos_iff_defect H b hb f e z R.sign hs).mp
    (hMargin.trans_le
      (p4Q2PZ37ACB_rectangle_optimizedMargin_le_covarianceMargin H b hb.le f e R z hz))

/-- Original outer-Haar second moment from a verified absolute covariance
margin on any measurable event. No common orientation, slope selection,
inner rectangle or auxiliary-Haar/outer-Haar identification is assumed. -/
theorem p4Q2PZ37ACB_originalOuterMoment_lower_of_absoluteCovarianceMargin
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (A : Set (Cfg × Cfg)) (hA : MeasurableSet A)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hMargin : ∀ z ∈ A, delta ≤ LAbs b hb f e z) :
    Measure.real outer A * delta ^ 2 ≤
      ∫ z : Cfg × Cfg, (gap b hb f e z) ^ 2 ∂outer := by
  have hInt : Integrable (fun z : Cfg × Cfg => (gap b hb f e z) ^ 2) outer :=
    ((p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous H b hb f e).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (z : Cfg × Cfg) (hz : z ∈ A) : delta ^ 2 ≤ (gap b hb f e z) ^ 2 := by
    have h := (hMargin z hz).trans (p4Q2PZ37ACB_originalGI_abs_lower H b hb f e z)
    have hs := pow_le_pow_left₀ hdelta h 2
    simpa only [sq_abs] using hs
  have hSet : delta ^ 2 * Measure.real outer A ≤
      ∫ z in A, (gap b hb f e z) ^ 2 ∂outer :=
    setIntegral_ge_of_const_le_real hA (measure_ne_top _ _) hPoint hInt.integrableOn
  have hFull : (∫ z in A, (gap b hb f e z) ^ 2 ∂outer) ≤
      ∫ z : Cfg × Cfg, (gap b hb f e z) ^ 2 ∂outer :=
    setIntegral_le_integral hInt (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  simpa only [mul_comm] using hSet.trans hFull

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalGI_covariance_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalGI_abs_covariance_error
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalGI_abs_covariance_error_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalGI_abs_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalCovarianceGIMargin_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalGI_abs_transfer_covariance_error
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalCovarianceGIMargin_eq_budgetDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_covarianceMargin_pos_iff_budgetRatio
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_covarianceMargin_pos_iff_defect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalGI_pos_of_covarianceDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_covarianceMargin_pos_iff_transferDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalMismatch_le_sqrtDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalNegativeTail_le_sqrtDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_rectangle_optimizedMargin_le_covarianceMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_rectangle_positiveMargin_implies_covarianceDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACB_originalOuterMoment_lower_of_absoluteCovarianceMargin

