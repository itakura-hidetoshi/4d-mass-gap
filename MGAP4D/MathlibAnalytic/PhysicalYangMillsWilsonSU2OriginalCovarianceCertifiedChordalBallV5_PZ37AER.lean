import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullChordalExplicitDensityModulusV5_PZ37AEQ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalDensityCompactNumeratorFloorV5_PZ37AEG
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AER — original covariance stability from a certified numerator radius

The exact original centered physical Wilson covariance is C_e=N_e/q_H.
AEG proves an H-dependent strictly positive physical q_H floor, an
H-dependent true Haar numerator ceiling, and uniform D_H continuity
of N_e. AEQ now gives the first EXPLICIT genuine full-boundary q_H
absolute slope at every D_H <= 1, derived from AEP full-link Harnack.

For an original positive covariance center a, a certified numerator
modulus radius r_N, an original q_H floor lambda and a true numerator
ceiling M, this file constructs the physical radius

  delta_q = lambda^2*C_e(a)/(4*(M+lambda)),
  L_q = 13*beta0*exp(13*beta0)*M_q(H),
  R = min(r_N, 1, delta_q/(L_q+1)) > 0.

On D_H(z,w)<R the *genuine* physical covariance fluctuates by at most
C_e(a)/2. The original two gauge-opposite Haar balls consequently give
the strict positive half-amplitude polynomial second-moment floor.

The r_N certificate exists (AEG), so the physical radius R exists
unconditionally at every finite H and genuine link. Neither r_N nor
C_e(a), lambda, M, or M_q(H) is numerically evaluated. Thus R is an
explicit formula in true finite-H certificates, NOT a numerical radius
or an H-uniform Lipschitz constant. No new measure, independent
posterior, uniform coercivity, GI threshold, physical spectral gap, or
continuum four-dimensional Yang--Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A nonnegative slope is controlled by the strictly positive
denominator L+1, even if L vanishes. -/
theorem p4Q2PZ37AER_realSlopeBudget
    (L delta : ℝ) (hL : 0 ≤ L) (hdelta : 0 ≤ delta) :
    L * (delta / (L + 1)) ≤ delta := by
  have hpos : 0 < L + 1 := by linarith only [hL]
  have hEq : L * (delta / (L + 1)) = (L * delta) / (L + 1) := by ring
  rw [hEq]
  apply (div_le_iff₀ hpos).mpr
  nlinarith only [hdelta]

/-- Two explicit quarter-amplitude numerator/denominator budgets
combine to at most half the actual physical covariance amplitude. -/
theorem p4Q2PZ37AER_realQuarterBudgets
    (lambda M a : ℝ) (hlambda : 0 < lambda)
    (hM : 0 ≤ M) (ha : 0 < a) :
    ((lambda * a / 4) +
        (M / lambda) * (lambda ^ 2 * a / (4 * (M + lambda)))) / lambda
      ≤ a / 2 := by
  have hsum : 0 < M + lambda := add_pos_of_nonneg_of_pos hM hlambda
  have hfrac : M / (M + lambda) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hsum).mpr
    linarith only [hlambda]
  have hEq :
      ((lambda * a / 4) +
          (M / lambda) * (lambda ^ 2 * a / (4 * (M + lambda)))) / lambda =
        a / 4 + (M / (M + lambda)) * (a / 4) := by
    field_simp [ne_of_gt hlambda, ne_of_gt hsum]
  rw [hEq]
  have hMul : (M / (M + lambda)) * (a / 4) ≤ 1 * (a / 4) :=
    mul_le_mul_of_nonneg_right hfrac (by positivity)
  nlinarith only [hMul]

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AER_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AER_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AER_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AER_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AER_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "N" => p4Q2PZ37AEF_originalCenteredCovarianceNumerator H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "k" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "Mq" =>
  Real.exp (b0 *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) /
      Real.sqrt (k ^ 3)
local notation "Lq" => (13 * b0) * Real.exp (13 * b0) * Mq

local instance p4Q2PZ37AER_links : Fintype Link := Fintype.ofFinite _

/-- AEQ's exact original q_H density slope on the whole original
two-boundary D_H unit ball, with no hypothetical posterior. -/
theorem p4Q2PZ37AER_originalDensity_explicitUnitBallSlope
    (z w : Pair) (hD : D z w ≤ 1) :
    |q b0 hb0 z - q b0 hb0 w| ≤ Lq * D z w := by
  have h := p4Q2PZ37AEQ_originalJQDensity_fullBall_localLipschitz
    H z w 1 hD
  simpa only [mul_one] using h

/-- A certified physical numerator D_H radius plus AEG's genuine
q_H floor and numerator ceiling determine a concrete FORMULA for
an original covariance half-amplitude radius and the original
gauge-opposite two-ball Haar moment floor. The input r_N remains
a real source-numerator certification obligation, not a new axiom. -/
theorem p4Q2PZ37AER_originalCertifiedNumerator_explicitStableBall
    (e : Link) (a : Pair) (lambda M rN : ℝ)
    (ha : 0 < C b0 hb0 e a) (hlambda : 0 < lambda)
    (hM : 0 ≤ M) (hrN : 0 < rN)
    (hQFloor : ∀ z : Pair, lambda ≤ q b0 hb0 z)
    (hNmax : ∀ z : Pair, |N e z| ≤ M)
    (hNmod : ∀ z w : Pair, D z w < rN →
      |N e z - N e w| ≤ lambda * C b0 hb0 e a / 4) :
    ∃ R : ℝ,
      R = min rN (min 1
        ((lambda ^ 2 * C b0 hb0 e a / (4 * (M + lambda))) / (Lq + 1))) ∧
      0 < R ∧
      (∀ z w : Pair, D z w < R →
        |C b0 hb0 e z - C b0 hb0 e w| ≤ C b0 hb0 e a / 2) ∧
      (C b0 hb0 e a / 2) ^ 2 *
        (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
          (8 * Fintype.card Link)) ≤ S b0 hb0 e := by
  let amp : ℝ := C b0 hb0 e a
  let dN : ℝ := lambda * amp / 4
  let dq : ℝ := lambda ^ 2 * amp / (4 * (M + lambda))
  have hsum : 0 < M + lambda := add_pos_of_nonneg_of_pos hM hlambda
  have hdN : 0 < dN := by
    dsimp [dN]
    positivity
  have hdq : 0 < dq := by
    dsimp [dq]
    positivity
  have hCoupling : 0 ≤ (13 * b0 : ℝ) :=
    mul_nonneg (by norm_num) hb0
  have hMq : 0 ≤ Mq :=
    div_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)
  have hLq : 0 ≤ Lq :=
    mul_nonneg (mul_nonneg hCoupling (Real.exp_nonneg _)) hMq
  have hLq1 : 0 < Lq + 1 := by linarith only [hLq]
  let R : ℝ := min rN (min 1 (dq / (Lq + 1)))
  have hR : 0 < R := by
    dsimp [R]
    exact lt_min hrN (lt_min (by norm_num) (div_pos hdq hLq1))
  have hRleN : R ≤ rN := by
    dsimp [R]
    exact min_le_left _ _
  have hRle1 : R ≤ 1 := by
    dsimp [R]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hRleQ : R ≤ dq / (Lq + 1) := by
    dsimp [R]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hSlopeR : Lq * R ≤ dq := by
    calc
      Lq * R ≤ Lq * (dq / (Lq + 1)) :=
        mul_le_mul_of_nonneg_left hRleQ hLq
      _ ≤ dq := p4Q2PZ37AER_realSlopeBudget Lq dq hLq hdq.le
  have hNmodR : ∀ z w : Pair, D z w < R →
      |N e z - N e w| ≤ dN := by
    intro z w hzw
    exact hNmod z w (hzw.trans_le hRleN)
  have hQmodR : ∀ z w : Pair, D z w < R →
      |q b0 hb0 z - q b0 hb0 w| ≤ dq := by
    intro z w hzw
    have hUnit : D z w ≤ 1 := hzw.le.trans hRle1
    calc
      |q b0 hb0 z - q b0 hb0 w| ≤ Lq * D z w :=
        p4Q2PZ37AER_originalDensity_explicitUnitBallSlope H z w hUnit
      _ ≤ Lq * R := mul_le_mul_of_nonneg_left hzw.le hLq
      _ ≤ dq := hSlopeR
  have hExact :=
    p4Q2PZ37AEF_originalNumeratorDensity_givesCovarianceModulus
      H e R lambda M dN dq hlambda hQFloor hNmax hNmodR hQmodR
  have hBudget : (dN + (M / lambda) * dq) / lambda ≤ amp / 2 :=
    p4Q2PZ37AER_realQuarterBudgets lambda M amp hlambda hM ha
  have hCovMod : ∀ z w : Pair, D z w < R →
      |C b0 hb0 e z - C b0 hb0 e w| ≤ amp / 2 := by
    intro z w hzw
    exact (hExact z w hzw).trans hBudget
  have hHalfPos : 0 ≤ amp / 2 := div_nonneg ha.le (by norm_num)
  have hHalfLt : amp / 2 < amp := by linarith only [ha]
  have hMoment :=
    p4Q2PZ37AEE_certifiedTwoSignError_doubleMomentFloor
      H e a R (amp / 2) hR hHalfPos hHalfLt hCovMod
  have hHalfIdentity : C b0 hb0 e a - amp / 2 = C b0 hb0 e a / 2 := by
    dsimp [amp]
    ring
  rw [hHalfIdentity] at hMoment
  exact ⟨R, rfl, hR, hCovMod, hMoment⟩

/-- UNCONDITIONAL fixed-H existence: AED supplies a true positive
original covariance center, AEG supplies actual lambda, M, and
numerator modulus r_N, while AEQ replaces the density modulus by
its certified explicit full-boundary slope. The resulting positive
radius has the displayed formula, not a fabricated numerical value. -/
theorem p4Q2PZ37AER_originalEveryLink_explicitDensityRadius_exists
    (e : Link) :
    ∃ a : Pair, 0 < C b0 hb0 e a ∧
      ∃ lambda M rN R : ℝ,
        0 < lambda ∧ 0 < M ∧ 0 < rN ∧ 0 < R ∧
        R = min rN (min 1
          ((lambda ^ 2 * C b0 hb0 e a / (4 * (M + lambda))) / (Lq + 1))) ∧
        (∀ z w : Pair, D z w < R →
          |C b0 hb0 e z - C b0 hb0 e w| ≤ C b0 hb0 e a / 2) ∧
        (C b0 hb0 e a / 2) ^ 2 *
          (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
            (8 * Fintype.card Link)) ≤ S b0 hb0 e := by
  obtain ⟨a, ha, _hMax⟩ :=
    p4Q2PZ37AED_originalPositiveMaximumCovariance_exists H e
  obtain ⟨lambda, hlambda, hFloor⟩ :=
    p4Q2PZ37AEG_originalDensity_globalPositiveFloor_exists H
  obtain ⟨M, hM, hNmax⟩ :=
    p4Q2PZ37AEG_originalNumerator_positiveMaxAbs_exists H e
  have hdN : 0 < lambda * C b0 hb0 e a / 4 := by positivity
  obtain ⟨rN, hrN, hNmodStrict⟩ :=
    p4Q2PZ37AEG_originalNumerator_uniformChordalModulus
      H e (lambda * C b0 hb0 e a / 4) hdN
  have hNmod : ∀ z w : Pair, D z w < rN →
      |N e z - N e w| ≤ lambda * C b0 hb0 e a / 4 := by
    intro z w hzw
    exact (hNmodStrict z w hzw).le
  obtain ⟨R, hReq, hR, hCovMod, hMoment⟩ :=
    p4Q2PZ37AER_originalCertifiedNumerator_explicitStableBall
      H e a lambda M rN ha hlambda hM.le hrN hFloor hNmax hNmod
  exact ⟨a, ha, lambda, M, rN, R,
    hlambda, hM, hrN, hR, hReq, hCovMod, hMoment⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AER_realSlopeBudget
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AER_realQuarterBudgets
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AER_originalDensity_explicitUnitBallSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AER_originalCertifiedNumerator_explicitStableBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AER_originalEveryLink_explicitDensityRadius_exists
