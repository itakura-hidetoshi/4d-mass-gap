import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedCovarianceFCThresholdV5_PZ37ADE
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalizationFloor

/-!
# P4-Q2-PZ37ADF — explicit original transfer/plaquette FC budget

The SAME genuine finite-volume interacting Wilson SU(2) source and
receiver as ADE are retained without changing either posterior,
the positive Perron representative, the original boundary pair-Haar
measure, the transfer operator, or the fixed positive coupling b0.

Let A_H be the original global one-slab Wilson action budget and
P_H the actual spatial plaquette count. The already-proved genuine
physical transfer bound ||T_(H,b)|| >= exp(-b*A_H), together with the
original Gauss-law centered source estimate ||f0_H||^2 <= 6*P_H,
gives an entirely explicit finite-volume upper bound

  B(H,b0)^2 <= 6*P_H*exp(2*b0*A_H)*(exp(8*b0)^3-1)^2.

The exact ADE threshold B^2 < 272*S is therefore implied by
the concrete SU(2) comparison of this explicit upper bound with
272 times the ACTUAL covariance second moment S(H,b0,e).

Every GI certificate and signed-response conclusion below is
conditional on that additional numerical comparison. This is a
coarse global-action bound; it is NOT an unconditional proof of
GI certificate positivity, an H-uniform estimate, or the continuum
Yang--Mills mass gap. Its explicit action-budget dependence exposes
rather than conceals the remaining volume-scaling obstruction.
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
local instance p4Q2PZ37ADF_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADF_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADF_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADF_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADF_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADF_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

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
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "Cov" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "P" =>
  (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)
local notation "A" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local instance p4Q2PZ37ADF_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADF_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Explicit original physical one-slab/plaquette scalar upper budget.
A_H is the genuine Wilson slab action upper bound, and P_H is the
genuine spatial plaquette count. No unknown transfer norm remains. -/
def p4Q2PZ37ADF_originalTransferPlaquetteFCBound : ℝ :=
  6 * P * Real.exp (2 * b₀ * A) * (Real.exp (8 * b₀) ^ 3 - 1) ^ 2

/-- The explicit finite-volume scalar upper bound is nonnegative. -/
theorem p4Q2PZ37ADF_originalTransferPlaquetteFCBound_nonneg :
    0 ≤ p4Q2PZ37ADF_originalTransferPlaquetteFCBound H := by
  unfold p4Q2PZ37ADF_originalTransferPlaquetteFCBound
  positivity

/-- Unconditional ACTUAL Wilson finite-volume estimate:
the original FC envelope squared is bounded by the original source
norm estimate and the genuine positive transfer kernel minorization.
In particular no substitute source or independent Haar model enters. -/
theorem p4Q2PZ37ADF_originalFCsq_le_transferPlaquetteBound :
    (B b₀ p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 ≤
      p4Q2PZ37ADF_originalTransferPlaquetteFCBound H := by
  let t : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) b₀ p4Q2PZ37ADC_fixedCoupling_pos.le‖⁻¹
  let v : ℝ := Real.exp (b₀ * A)
  let q : ℝ := Real.exp (8 * b₀) ^ 3 - 1
  have htNonneg : 0 ≤ t := by
    dsimp [t]
    exact inv_nonneg.mpr
      (norm_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) b₀ p4Q2PZ37ADC_fixedCoupling_pos.le))
  have htInvLe : t ≤ v := by
    have ht :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferNorm_inv_le_globalMinorizationFloor_inv
        H 2 (by norm_num) b₀ p4Q2PZ37ADC_fixedCoupling_pos.le
    change
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b₀ p4Q2PZ37ADC_fixedCoupling_pos.le‖⁻¹ ≤
        (Real.exp (-(b₀ * A)))⁻¹ at ht
    dsimp [t, v]
    simpa only [Real.exp_neg, inv_inv] using ht
  have htSq : t ^ 2 ≤ v ^ 2 :=
    pow_le_pow_left₀ htNonneg htInvLe 2
  have hfSq : ‖f₀‖ ^ 2 ≤ 6 * P := by
    simpa only [Fintype.card_eq_nat_card] using
      (p4Q2PZ37AAI_originalCenteredPhysicalNorm_sq_le_six_plaquetteCount H)
  have hFirst :
      t ^ 2 * q ^ 2 * ‖f₀‖ ^ 2 ≤
        v ^ 2 * q ^ 2 * ‖f₀‖ ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right htSq (sq_nonneg q))
      (sq_nonneg ‖f₀‖)
  have hSecond :
      v ^ 2 * q ^ 2 * ‖f₀‖ ^ 2 ≤
        v ^ 2 * q ^ 2 * (6 * P) :=
    mul_le_mul_of_nonneg_left hfSq
      (mul_nonneg (sq_nonneg v) (sq_nonneg q))
  have hCap :
      (B b₀ p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 ≤
        v ^ 2 * q ^ 2 * (6 * P) := by
    change (t * q * ‖f₀‖) ^ 2 ≤ v ^ 2 * q ^ 2 * (6 * P)
    calc
      (t * q * ‖f₀‖) ^ 2 =
          t ^ 2 * q ^ 2 * ‖f₀‖ ^ 2 := by ring
      _ ≤ v ^ 2 * q ^ 2 * ‖f₀‖ ^ 2 := hFirst
      _ ≤ v ^ 2 * q ^ 2 * (6 * P) := hSecond
  have hExp : v ^ 2 = Real.exp (2 * b₀ * A) := by
    dsimp [v]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    (B b₀ p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 ≤
      v ^ 2 * q ^ 2 * (6 * P) := hCap
    _ = p4Q2PZ37ADF_originalTransferPlaquetteFCBound H := by
      rw [hExp]
      dsimp [p4Q2PZ37ADF_originalTransferPlaquetteFCBound, q]
      ring

/-- Actual physical covariance moment exceeding the completely
explicit transfer/plaquette FC cap implies the original GI SQUARED
mean certificate is positive. The comparison remains a hypothesis. -/
theorem p4Q2PZ37ADF_transferPlaquetteBound_lt_moment_gives_positiveBudget
    (e : Link)
    (hNumeric :
      p4Q2PZ37ADF_originalTransferPlaquetteFCBound H <
        272 * S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) :
    0 < Budget b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  exact p4Q2PZ37ADE_fixedCovarianceFC_gives_positiveBudget H e
    (lt_of_le_of_lt (p4Q2PZ37ADF_originalFCsq_le_transferPlaquetteBound H) hNumeric)

/-- The same conditional explicit comparison yields a nonzero actual
SIGNED two-interacting-posterior GI response on an OPEN positive
original boundary pair-Haar-mass set. -/
theorem p4Q2PZ37ADF_transferPlaquetteBound_lt_moment_gives_openGI
    (e : Link)
    (hNumeric :
      p4Q2PZ37ADF_originalTransferPlaquetteFCBound H <
        272 * S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) :
    ∃ V : Set Pair, IsOpen V ∧ 0 < Measure.real outer V ∧
      ∀ z ∈ V,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z| := by
  exact p4Q2PZ37ADE_fixedCovarianceFC_gives_openGI H e
    (lt_of_le_of_lt (p4Q2PZ37ADF_originalFCsq_le_transferPlaquetteBound H) hNumeric)

/-- A quantitative actual covariance OPEN region can be compared
directly to the explicit transfer/plaquette budget, without an
unmeasured physical transfer norm in the criterion. -/
theorem p4Q2PZ37ADF_transferPlaquetteBound_lt_region_gives_positiveBudget
    (e : Link) (U : Set Pair) (a : ℝ)
    (hOpen : IsOpen U) (ha : 0 < a)
    (hCov :
      ∀ z ∈ U, a ≤ |Cov b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z|)
    (hNumeric :
      p4Q2PZ37ADF_originalTransferPlaquetteFCBound H <
        272 * (a ^ 2 * Measure.real outer U)) :
    0 < Budget b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  exact p4Q2PZ37ADE_originalRegionNumeric_gives_positiveBudget
    H e U a hOpen ha hCov
      (lt_of_le_of_lt (p4Q2PZ37ADF_originalFCsq_le_transferPlaquetteBound H) hNumeric)

/-- Conditional positive-mass OPEN signed GI response from a
genuinely measurable local covariance region and the explicit cap. -/
theorem p4Q2PZ37ADF_transferPlaquetteBound_lt_region_gives_openGI
    (e : Link) (U : Set Pair) (a : ℝ)
    (hOpen : IsOpen U) (ha : 0 < a)
    (hCov :
      ∀ z ∈ U, a ≤ |Cov b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z|)
    (hNumeric :
      p4Q2PZ37ADF_originalTransferPlaquetteFCBound H <
        272 * (a ^ 2 * Measure.real outer U)) :
    ∃ V : Set Pair, IsOpen V ∧ 0 < Measure.real outer V ∧
      ∀ z ∈ V,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z| := by
  exact p4Q2PZ37ADE_originalRegionNumeric_gives_openGI
    H e U a hOpen ha hCov
      (lt_of_le_of_lt (p4Q2PZ37ADF_originalFCsq_le_transferPlaquetteBound H) hNumeric)

/-- At a fixed H, compare one TRUE common covariance-moment lower
constant to the concrete volume-dependent scalar cap. This does NOT
assert any lower bound uniform over H. -/
theorem p4Q2PZ37ADF_fixedVolumeTransferPlaquetteCap_allLinks
    [Nonempty Link] (s₀ : ℝ)
    (hLower :
      ∀ e : Link, s₀ ≤ S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e)
    (hNumeric :
      p4Q2PZ37ADF_originalTransferPlaquetteFCBound H < 272 * s₀) :
    ∀ e : Link, 0 < Budget b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  exact p4Q2PZ37ADE_fixedVolumeConstant_dominance_allLinks H s₀ hLower
    (lt_of_le_of_lt (p4Q2PZ37ADF_originalFCsq_le_transferPlaquetteBound H) hNumeric)

/-- If the actual original mean GI squared certificate is
nonpositive, its covariance moment cannot exceed this explicit
finite-volume transfer/plaquette cap divided by 272. This does not
assert pointwise or signed GI-response vanishing. -/
theorem p4Q2PZ37ADF_nonpositiveBudget_forces_moment_cap
    (e : Link)
    (hNonpos : Budget b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e ≤ 0) :
    272 * S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e ≤
      p4Q2PZ37ADF_originalTransferPlaquetteFCBound H := by
  exact
    (p4Q2PZ37ADE_nonpositiveBudget_forces_FC_obstruction H e hNonpos).trans
      (p4Q2PZ37ADF_originalFCsq_le_transferPlaquetteBound H)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADF_originalTransferPlaquetteFCBound_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADF_originalFCsq_le_transferPlaquetteBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADF_transferPlaquetteBound_lt_moment_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADF_transferPlaquetteBound_lt_moment_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADF_transferPlaquetteBound_lt_region_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADF_transferPlaquetteBound_lt_region_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADF_fixedVolumeTransferPlaquetteCap_allLinks
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADF_nonpositiveBudget_forces_moment_cap
