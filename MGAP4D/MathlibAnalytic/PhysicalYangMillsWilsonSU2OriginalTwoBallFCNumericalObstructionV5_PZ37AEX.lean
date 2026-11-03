import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalReceiverExplicitCovarianceBallV5_PZ37AEW
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEX — unavoidable FC obstruction for the AEW two-ball floor

AEW's original Wilson/Haar two-ball lower bound is valid and strictly
positive. Nevertheless, the original ACJ pointwise four-covariance-
square <= FC-envelope-square inequality and the explicit two-ball
Haar-volume polynomial imply that 272 times this PARTICULAR conservative
lower bound is at most 17/128 of the ORIGINAL FC envelope square.

Hence it can NEVER satisfy the strict FC numerical premise in the AEW
GI corollary. This is a no-go for the specific AEW two-ball lower-bound
certificate, NOT for the true covariance moment, GI positivity, the
original SU(2) physical model, or continuum Yang--Mills mass gap.

No surrogate model, source, Haar law, Wilson kernel, weakened premise,
new axiom, or numerical sample is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The genuine small-ball polynomial is universally tiny once there
is at least one physical link. The radius is nonnegative, and the
radius cap 2 remains unchanged from AED/AEE/AEW. -/
theorem p4Q2PZ37AEX_realTwoBallPolynomial_le_oneOver256
    (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 ≤ R) :
    (min (R / (2 * (n : ℝ) + 1)) 2 / 4) ^ (8 * n) ≤ (1 / 256 : ℝ) := by
  let x : ℝ := min (R / (2 * (n : ℝ) + 1)) 2 / 4
  have hden : 0 < (2 * (n : ℝ) + 1) := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith only [hn0]
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg
      (le_min (div_nonneg hR hden.le) (by norm_num))
      (by norm_num)
  have hxhalf : x ≤ (1 / 2 : ℝ) := by
    dsimp [x]
    calc
      min (R / (2 * (n : ℝ) + 1)) 2 / 4 ≤ (2 : ℝ) / 4 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      _ = 1 / 2 := by norm_num
  have hx8 : x ^ 8 ≤ (1 / 256 : ℝ) := by
    calc
      x ^ 8 ≤ (1 / 2 : ℝ) ^ 8 := pow_le_pow_left₀ hx0 hxhalf 8
      _ = 1 / 256 := by norm_num
  cases n with
  | zero =>
      omega
  | succ m =>
      have hx8nonneg : 0 ≤ x ^ 8 := pow_nonneg hx0 8
      have hx8one : x ^ 8 ≤ (1 : ℝ) := by linarith only [hx8]
      have hpowm : (x ^ 8) ^ m ≤ (1 : ℝ) := by
        have h := pow_le_pow_left₀ hx8nonneg hx8one m
        simpa only [one_pow] using h
      change x ^ (8 * (m + 1)) ≤ (1 / 256 : ℝ)
      calc
        x ^ (8 * (m + 1)) = (x ^ 8) ^ m * x ^ 8 := by
          rw [← pow_mul, pow_succ]
        _ ≤ 1 * x ^ 8 := mul_le_mul_of_nonneg_right hpowm hx8nonneg
        _ = x ^ 8 := by ring
        _ ≤ 1 / 256 := hx8

/-- The scalar FC-versus-two-ball inequality, with NO assertion that
the genuine full second moment satisfies the same small-ball ceiling.
The exact factor 17/128 is 272 / (16 * 128). -/
theorem p4Q2PZ37AEX_real_FC_twoBallCeiling
    (B C p : ℝ)
    (hCov : 4 * C ^ 2 ≤ B ^ 2)
    (hp : p ≤ (1 / 256 : ℝ)) :
    272 * ((C / 2) ^ 2 * (2 * p)) ≤ (17 / 128 : ℝ) * B ^ 2 := by
  have hC : (C / 2) ^ 2 ≤ B ^ 2 / 16 := by
    nlinarith only [hCov]
  have hP : 2 * p ≤ (1 / 128 : ℝ) := by linarith only [hp]
  have hA :
      (C / 2) ^ 2 * (2 * p) ≤ (C / 2) ^ 2 * (1 / 128 : ℝ) :=
    mul_le_mul_of_nonneg_left hP (sq_nonneg _)
  have hB :
      (C / 2) ^ 2 * (1 / 128 : ℝ) ≤
        B ^ 2 / 16 * (1 / 128 : ℝ) :=
    mul_le_mul_of_nonneg_right hC (by norm_num)
  calc
    272 * ((C / 2) ^ 2 * (2 * p)) ≤
        272 * ((C / 2) ^ 2 * (1 / 128 : ℝ)) :=
      mul_le_mul_of_nonneg_left hA (by norm_num)
    _ ≤ 272 * (B ^ 2 / 16 * (1 / 128 : ℝ)) :=
      mul_le_mul_of_nonneg_left hB (by norm_num)
    _ = (17 / 128 : ℝ) * B ^ 2 := by ring

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Var" => CompactEnergyMismatchMoment.variance mu
local notation "Cov" => CompactEnergyMismatchMoment.covariance mu

local instance p4Q2PZ37AEX_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEX_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEX_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEX_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEX_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AEX_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "k" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "lambdaQ" => (1 : ℝ) / Real.sqrt ((k⁻¹)^3)
local notation "LF" => p4Q2PZ37AEW_originalReceiverFullSlope H
local notation "Mq" =>
  Real.exp (b0 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) /
    Real.sqrt (k^3)
local notation "Lq" => (13*b0)*Real.exp (13*b0)*Mq

local instance p4Q2PZ37AEX_links : Fintype Link := Fintype.ofFinite _

/-- Reprove the genuine ACJ pointwise FC covariance ceiling using
the ORIGINAL energy Haar variance identity and ACA's actual source
receiver variance bound; ACJ's earlier private helper is not imported. -/
theorem p4Q2PZ37AEX_originalCovariance_fourSquare_le_trueFC
    (e : Link) (a : Pair) :
    4 * (C b0 hb0 e a) ^ 2 ≤ (B b0 hb0) ^ 2 := by
  have hF : Continuous (F b0 hb0 f0 e a) :=
    (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H 2 (by norm_num) b0 hb0 f0 e).continuous.comp
        (continuous_const.prodMk continuous_id)
  have h4 :
      4 * (C b0 hb0 e a) ^ 2 ≤ Var (F b0 hb0 f0 e a) := by
    exact CompactEnergyMismatchMoment.four_covariance_sq_le_variance mu
      (F b0 hb0 f0 e a) E hF
      (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
      p4Q2PZ37ABZ_originalEnergy_Haar_variance
  have hV :
      Var (F b0 hb0 f0 e a) ≤ (B b0 hb0) ^ 2 := by
    exact p4Q2PZ37ACA_originalReceiver_variance_le_FC
      H b0 hb0 f0 e a
  exact h4.trans hV

/-- At each ACTUAL receiver link, the AEW two-ball Haar polynomial
can never make the numerical FC comparison cross the original 272
threshold. This is a bound for the conservative AEW floor only. -/
theorem p4Q2PZ37AEX_originalAEWTwoBall_272Floor_le_FCfraction
    (e : Link) (a : Pair) (R : ℝ) (hR : 0 ≤ R) :
    272 * ((C b0 hb0 e a / 2) ^ 2 *
       (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
         (8 * Fintype.card Link))) ≤
      (17 / 128 : ℝ) * (B b0 hb0) ^ 2 := by
  have hn : 0 < Fintype.card Link := Fintype.card_pos_iff.mpr ⟨e⟩
  have hp := p4Q2PZ37AEX_realTwoBallPolynomial_le_oneOver256
    (Fintype.card Link) hn R hR
  have hCov := p4Q2PZ37AEX_originalCovariance_fourSquare_le_trueFC H e a
  exact p4Q2PZ37AEX_real_FC_twoBallCeiling
    (B b0 hb0) (C b0 hb0 e a)
    ((min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
      (8 * Fintype.card Link)) hCov hp

/-- Precise obstruction: the AEW GI sufficient condition
'B^2 < 272 * explicit_two_ball_floor' is IMPOSSIBLE for the
unchanged original physical model, at EVERY genuine link and
every nonnegative radius. This does NOT rule out B^2<272*S. -/
theorem p4Q2PZ37AEX_originalAEWTwoBall_strictFCNumerical_impossible
    (e : Link) (a : Pair) (R : ℝ) (hR : 0 ≤ R) :
    ¬ (B b0 hb0) ^ 2 <
      272 * ((C b0 hb0 e a / 2) ^ 2 *
        (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
          (8 * Fintype.card Link))) := by
  have hceiling :=
    p4Q2PZ37AEX_originalAEWTwoBall_272Floor_le_FCfraction H e a R hR
  have hB : (17 / 128 : ℝ) * (B b0 hb0) ^ 2 ≤ (B b0 hb0) ^ 2 := by
    nlinarith only [sq_nonneg (B b0 hb0)]
  exact not_lt_of_ge (hceiling.trans hB)

/-- AEW's unconditional genuine positive-radius witnesses survive
unchanged; their CONSERVATIVE lower-bound FC threshold has exactly
the new no-go. This leaves the TRUE moment-based GI test unresolved. -/
theorem p4Q2PZ37AEX_originalEveryLink_physicalBallWithFCObstruction
    (e : Link) :
    ∃ a : Pair, 0 < C b0 hb0 e a ∧
      ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
        R = min ((lambdaQ*C b0 hb0 e a/4)/(LF+1))
          (min 1
            ((lambdaQ^2*C b0 hb0 e a/(4*(M+lambdaQ)))/(Lq+1))) ∧
        (∀ z w : Pair, D z w < R →
          |C b0 hb0 e z-C b0 hb0 e w| ≤ C b0 hb0 e a/2) ∧
        (C b0 hb0 e a/2)^2 *
          (2*(min (R/(2*(Fintype.card Link : ℝ)+1)) 2/4)^
            (8*Fintype.card Link)) ≤ S b0 hb0 e ∧
        ¬ (B b0 hb0)^2 <
          272 * ((C b0 hb0 e a / 2)^2 *
            (2*(min (R/(2*(Fintype.card Link : ℝ)+1)) 2/4)^
              (8*Fintype.card Link))) := by
  obtain ⟨a, ha, M, R, hM, hR, hFormula, hStable, hMoment⟩ :=
    p4Q2PZ37AEW_originalEveryLink_explicitPhysicalBall_exists H e
  refine ⟨a, ha, M, R, hM, hR, hFormula, hStable, hMoment, ?_⟩
  exact p4Q2PZ37AEX_originalAEWTwoBall_strictFCNumerical_impossible
    H e a R hR.le

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEX_realTwoBallPolynomial_le_oneOver256
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEX_real_FC_twoBallCeiling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEX_originalCovariance_fourSquare_le_trueFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEX_originalAEWTwoBall_272Floor_le_FCfraction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEX_originalAEWTwoBall_strictFCNumerical_impossible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEX_originalEveryLink_physicalBallWithFCObstruction
