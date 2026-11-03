import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalWeightedTransferResidualFCGateV5_PZ37AEZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFA — exceptional genuine pair-Haar tail budget

Continue AEZ's exact source/transfer/Perron-weighted residual-vs-signal
test, retaining AEX's strict no-go for the tiny conservative AEW two-ball
floor. On the SAME original finite-volume interacting Wilson SU(2)
physics, fixed original positive b0, genuine centered Gauss-law
physical source, Perron ground representative, right-link-updated
transfer, and actual outer pair-Haar law, split the original boundary
space into good and exceptional contexts without assuming a uniform
pointwise relative residual estimate.

For theta>=0, let the actual exceptional event be
  Bad_theta = {z | theta * A_F(z)^2 < W_F(z)}
            = {z | theta * A_U(z)^2 < W_U(z)}.
The equality is pointwise: A_F^2=P_z^2*A_U^2 and W_F=P_z^2*W_U,
where P_z>0 is the TRUE original Perron/transfer prefactor.

The original FC envelope proves W_F(z)<=B_H^2 everywhere. Therefore
  R4_H = W_H <= theta*A4_H + B_H^2 * nu_H(Bad_theta).
A4_H=4*S_H>0 and R4_H is the real original Perron-weighted higher-mode
Haar energy. This is a global bound with an ACTUAL exceptional-set
probability, not the AEW two-ball floor or a substitute probability.

With independently established theta<64 and epsilon>=nu_H(Bad_theta),
  theta*A4 + B_H^2*epsilon <64*A4
suffices for positive original ACO mean squared-GI certificate, hence
its inherited actual signed two-posterior GI nonzero open Haar region.
With a separate original FC unused-variance bound E<=sigma*A4,
  (theta+sigma)*A4+B_H^2*epsilon <64*A4
suffices for the STRICT true FC numerical test.

Conversely a nonpositive mean squared-GI certificate forces
  (64-theta)*A4 <= B_H^2 *nu_H(Bad_theta)
for every theta>=0; with theta<64 the exceptional set has positive
explicit real Haar-mass floor. The failed true FC numerical test
obeys the analogous conditional (64-theta-sigma) bound if the actual
FC slack satisfies the independent sigma control.

No estimate of the exceptional mass, theta, sigma, or H-uniform
constant is asserted without physical proof. This is not a no-go
for genuine GI, volume-uniform coercivity, the physical Hamiltonian,
or the continuum 4D Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Reusable compact-probability upper-tail integration: continuous
nonnegative g, continuous f with a REAL cap, and theta>=0. The
exceptional event is the exact strict failure of f<=theta*g. -/
theorem p4Q2PZ37AFA_compactExceptionalIntegralBound
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [CompactSpace α] [BorelSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (f g : α → ℝ) (hf : Continuous f) (hg : Continuous g)
    (theta cap : ℝ) (hTheta : 0 ≤ theta)
    (hgNonneg : ∀ z, 0 ≤ g z)
    (hFC : ∀ z, f z ≤ cap) :
    (∫ z, f z ∂ν) ≤ theta * (∫ z, g z ∂ν) +
      cap * Measure.real ν {z | theta * g z < f z} := by
  classical
  let E : Set α := {z | theta * g z < f z}
  have hE : MeasurableSet E :=
    (isOpen_lt (continuous_const.mul hg) hf).measurableSet
  have hFI : Integrable f ν :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hGI : Integrable g ν :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hEI : Integrable (E.indicator (fun _ : α => (1 : ℝ))) ν :=
    (integrable_const _).indicator hE
  have hThetaI : Integrable (fun z : α => theta * g z) ν :=
    hGI.const_mul theta
  have hCapI : Integrable (fun z : α =>
      cap * E.indicator (fun _ => (1 : ℝ)) z) ν :=
    hEI.const_mul cap
  have hUpperI : Integrable (fun z : α =>
      theta * g z + cap * E.indicator (fun _ => (1 : ℝ)) z) ν :=
    hThetaI.add hCapI
  have hPoint (z : α) :
      f z ≤ theta * g z + cap * E.indicator (fun _ => (1 : ℝ)) z := by
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz]
      have hMul : 0 ≤ theta * g z := mul_nonneg hTheta (hgNonneg z)
      linarith only [hFC z, hMul]
    · rw [Set.indicator_of_notMem hz]
      have hGood : f z ≤ theta * g z := le_of_not_gt hz
      simpa only [mul_zero, add_zero] using hGood
  have hUpperEq :
      (∫ z : α, theta * g z +
          cap * E.indicator (fun _ => (1 : ℝ)) z ∂ν) =
        theta * (∫ z : α, g z ∂ν) + cap * Measure.real ν E := by
    rw [integral_add hThetaI hCapI, integral_const_mul,
      integral_const_mul, integral_indicator_const (1 : ℝ) hE]
    simp
  have hCompare := integral_mono hFI hUpperI hPoint
  rw [hUpperEq] at hCompare
  exact hCompare

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local instance p4Q2PZ37AFA_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFA_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFA_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFA_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFA_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFA_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "tA2" => p4Q2PZ37ACQ_transferAmplitudeSq H
local notation "tW" => p4Q2PZ37ACQ_transferResidualEnergy H
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H
local notation "Wz" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Eunused" => p4Q2PZ37AEY_originalFCUnusedVariance H
local notation "A4" => p4Q2PZ37AEZ_originalWeightedTransferFourMoment H
local notation "R4" => p4Q2PZ37AEZ_originalWeightedTransferHigherMoment H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H

local instance p4Q2PZ37AFA_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFA_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The STRICT original-Haar bad-boundary set for actual higher SU(2)
receiver modes relative to its four-mode signal. -/
def p4Q2PZ37AFA_originalExceptionalBoundary
    (e : Link) (theta : ℝ) : Set Pair :=
  {z | theta * (A b0 hb0 e z)^2 < Wz b0 hb0 e z}
local notation "Bad" => p4Q2PZ37AFA_originalExceptionalBoundary H

/-- AFA's actual original exceptional boundary is open, not an
unmeasurable or independently sampled exceptional event. -/
theorem p4Q2PZ37AFA_originalExceptionalBoundary_isOpen
    (e : Link) (theta : ℝ) : IsOpen (Bad e theta) := by
  exact isOpen_lt
    (continuous_const.mul
      (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b0 hb0 e))
    (p4Q2PZ37ACR_originalResidual_continuous H b0 hb0 e)

/-- The same exceptional set is exactly the failure set of the TRUE
right-link-updated transfer section. The positive Perron factor
cancels in the pointwise strict inequality, not from its integrals. -/
theorem p4Q2PZ37AFA_originalExceptionalBoundary_iff_transfer
    (e : Link) (theta : ℝ) (z : Pair) :
    z ∈ Bad e theta ↔ theta * tA2 b0 hb0 e z < tW b0 hb0 e z := by
  change theta * (A b0 hb0 e z)^2 < Wz b0 hb0 e z ↔ _
  rw [p4Q2PZ37ACQ_originalAmplitudeSq_eq_transfer H b0 hb0 e z,
    p4Q2PZ37ACQ_originalResidualEnergy_eq_transfer H b0 hb0 e z]
  have hp : 0 < (P b0 hb0 z)^2 :=
    pow_pos (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b0 hb0 z) _
  have hFactor :
      theta * ((P b0 hb0 z)^2 * tA2 b0 hb0 e z) =
        (P b0 hb0 z)^2 * (theta * tA2 b0 hb0 e z) := by ring
  rw [hFactor]
  exact mul_lt_mul_left hp

/-- ACTUAL original four-mode variance and higher-character residual:
global bound uses only the true FC cap and the measurable exceptional
boundary mass. The AEX two-ball tiny-volume factor does not enter. -/
theorem p4Q2PZ37AFA_originalExceptionalHaarMoment_upper
    (e : Link) (theta : ℝ) (hTheta : 0 ≤ theta) :
    R4 e ≤ theta * A4 e +
      (B b0 hb0)^2 * Measure.real outer (Bad e theta) := by
  have hFull :
      (∫ z : Pair, Wz b0 hb0 e z ∂outer) ≤
        theta * (∫ z : Pair, (A b0 hb0 e z)^2 ∂outer) +
          (B b0 hb0)^2 * Measure.real outer (Bad e theta) :=
    p4Q2PZ37AFA_compactExceptionalIntegralBound outer
      (Wz b0 hb0 e) (fun z : Pair => (A b0 hb0 e z)^2)
      (p4Q2PZ37ACR_originalResidual_continuous H b0 hb0 e)
      (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b0 hb0 e)
      theta ((B b0 hb0)^2) hTheta
      (fun z => sq_nonneg (A b0 hb0 e z))
      (p4Q2PZ37ACR_originalResidual_le_FC H b0 hb0 e)
  change Wbar b0 hb0 e ≤
    theta * (∫ z : Pair, (A b0 hb0 e z)^2 ∂outer) +
      (B b0 hb0)^2 * Measure.real outer (Bad e theta) at hFull
  rw [p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral H b0 hb0 e] at hFull
  rw [p4Q2PZ37AEZ_originalWeightedHigher_eq_trueResidual H e,
    p4Q2PZ37AEZ_originalWeightedFour_eq_trueCovariance H e]
  exact hFull

/-- A separately certified true exceptional Haar mass upper bound
provides the weighted transfer residual energy bound without an
all-context transfer ratio. -/
theorem p4Q2PZ37AFA_originalExceptionalMass_upper
    (e : Link) (theta epsilon : ℝ) (hTheta : 0 ≤ theta)
    (hMass : Measure.real outer (Bad e theta) ≤ epsilon) :
    R4 e ≤ theta * A4 e + (B b0 hb0)^2 * epsilon := by
  have hOld :=
    p4Q2PZ37AFA_originalExceptionalHaarMoment_upper H e theta hTheta
  have hProd : (B b0 hb0)^2 * Measure.real outer (Bad e theta) ≤
      (B b0 hb0)^2 * epsilon :=
    mul_le_mul_of_nonneg_left hMass (sq_nonneg _)
  linarith only [hOld, hProd]

/-- An independently verified true bad-set Haar mass with a strict
numerical surplus gives the SAME original ACO mean squared-GI
certificate. No pointwise inequality on the entire outer space. -/
theorem p4Q2PZ37AFA_originalExceptionalMass_gives_positiveBudget
    (e : Link) (theta epsilon : ℝ) (hTheta : 0 ≤ theta)
    (hMass : Measure.real outer (Bad e theta) ≤ epsilon)
    (hNumerical :
      theta * A4 e + (B b0 hb0)^2 * epsilon < 64 * A4 e) :
    0 < Budget b0 hb0 e := by
  have hR := p4Q2PZ37AFA_originalExceptionalMass_upper
    H e theta epsilon hTheta hMass
  have hp := p4Q2PZ37AEZ_originalWeightedFour_pos H e
  have hStrict : R4 e < 64 * A4 e := hR.trans_lt hNumerical
  apply (p4Q2PZ37AEZ_originalBudget_pos_iff_transferRatio_lt64 H e).mpr
  exact (div_lt_iff₀ hp).mpr hStrict

/-- The original two interacting Wilson posterior signed GI response is
nonzero on a genuine open positive-Haar set, conditionally on AFA's
exceptional-mass numerical bound. -/
theorem p4Q2PZ37AFA_originalExceptionalMass_gives_openGI
    (e : Link) (theta epsilon : ℝ) (hTheta : 0 ≤ theta)
    (hMass : Measure.real outer (Bad e theta) ≤ epsilon)
    (hNumerical :
      theta * A4 e + (B b0 hb0)^2 * epsilon < 64 * A4 e) :
    ∃ T : Set Pair, IsOpen T ∧ 0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 f0 e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion H b0 hb0 e
    (p4Q2PZ37AFA_originalExceptionalMass_gives_positiveBudget
      H e theta epsilon hTheta hMass hNumerical)

/-- With a SEPARATELY certified true unused FC variance envelope
E<=sigma*A4, the actual exceptional Haar mass also suffices for the
stronger FC threshold, not only the actual squared GI certificate. -/
theorem p4Q2PZ37AFA_originalExceptionalMassFC_gives_trueFC
    (e : Link) (theta sigma epsilon : ℝ) (hTheta : 0 ≤ theta)
    (hMass : Measure.real outer (Bad e theta) ≤ epsilon)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hNumerical :
      (theta + sigma) * A4 e + (B b0 hb0)^2 * epsilon <
        64 * A4 e) :
    (B b0 hb0)^2 < 272 * S b0 hb0 e := by
  have hR := p4Q2PZ37AFA_originalExceptionalMass_upper
    H e theta epsilon hTheta hMass
  have hBound : R4 e + Eunused e < 64 * A4 e := by
    nlinarith only [hR, hSlack, hNumerical]
  have hActual : Wbar b0 hb0 e + Eunused e < 256 * S b0 hb0 e := by
    rw [p4Q2PZ37AEZ_originalWeightedHigher_eq_trueResidual H e,
      p4Q2PZ37AEZ_originalWeightedFour_eq_trueCovariance H e] at hBound
    nlinarith only [hBound]
  exact (p4Q2PZ37AEY_originalTrueFC_iff_fullResidualAndUnused H e).mpr
    hActual

/-- The original FC endpoint, once AFA's actual exceptional Haar mass
is numerically certified, still propagates through the pre-existing
two-posterior open signed-GI theorem. -/
theorem p4Q2PZ37AFA_originalExceptionalMassFC_gives_openGI
    (e : Link) (theta sigma epsilon : ℝ) (hTheta : 0 ≤ theta)
    (hMass : Measure.real outer (Bad e theta) ≤ epsilon)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hNumerical :
      (theta + sigma) * A4 e + (B b0 hb0)^2 * epsilon <
        64 * A4 e) :
    ∃ T : Set Pair, IsOpen T ∧ 0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 f0 e z| := by
  exact p4Q2PZ37ADE_fixedCovarianceFC_gives_openGI H e
    (p4Q2PZ37AFA_originalExceptionalMassFC_gives_trueFC
      H e theta sigma epsilon hTheta hMass hSlack hNumerical)

/-- Failure of the true original mean squared GI certificate forces
an EXPLICIT lower exceptional probability: no all-context estimate
has been smuggled in, and no genuine signed-GI vanishing follows. -/
theorem p4Q2PZ37AFA_nonpositiveBudget_exceptionalMass_floor
    (e : Link) (theta : ℝ) (hTheta : 0 ≤ theta) :
    Budget b0 hb0 e ≤ 0 →
      ((64 - theta) * A4 e) / (B b0 hb0)^2 ≤
        Measure.real outer (Bad e theta) := by
  intro hNonpos
  have hMoment :=
    (p4Q2PZ37AEY_nonpositiveBudget_iff_higherHaarObstruction H e).mp hNonpos
  have hLower : 64 * A4 e ≤ R4 e := by
    rw [p4Q2PZ37AEZ_originalWeightedFour_eq_trueCovariance H e,
      p4Q2PZ37AEZ_originalWeightedHigher_eq_trueResidual H e]
    nlinarith only [hMoment]
  have hUpper :=
    p4Q2PZ37AFA_originalExceptionalHaarMoment_upper H e theta hTheta
  have hFC : 0 < (B b0 hb0)^2 :=
    p4Q2PZ37ADB_originalFCsq_pos H b0 p4Q2PZ37ADC_fixedCoupling_pos e
  apply (div_le_iff₀ hFC).mpr
  nlinarith only [hLower, hUpper]

/-- If theta<64 and the true GI MEAN certificate fails, its genuine
transfer exception must occupy a positive amount of true pair Haar mass. -/
theorem p4Q2PZ37AFA_nonpositiveBudget_exceptionalMass_pos
    (e : Link) (theta : ℝ) (hTheta : 0 ≤ theta)
    (hThetaSmall : theta < 64)
    (hNonpos : Budget b0 hb0 e ≤ 0) :
    0 < Measure.real outer (Bad e theta) := by
  have hFloor := p4Q2PZ37AFA_nonpositiveBudget_exceptionalMass_floor
    H e theta hTheta hNonpos
  have hp := p4Q2PZ37AEZ_originalWeightedFour_pos H e
  have hFC := p4Q2PZ37ADB_originalFCsq_pos
    H b0 p4Q2PZ37ADC_fixedCoupling_pos e
  have hPositive : 0 < ((64 - theta) * A4 e) / (B b0 hb0)^2 :=
    div_pos (mul_pos (sub_pos.mpr hThetaSmall) hp) hFC
  exact hPositive.trans_le hFloor

/-- A failed TRUE original full-moment FC test, together with a
SEPARATE actually checked FC unused-slack control, forces a lower
exceptional Haar mass and cannot be misread as the AEX two-ball no-go. -/
theorem p4Q2PZ37AFA_failedTrueFC_exceptionalMass_floor
    (e : Link) (theta sigma : ℝ) (hTheta : 0 ≤ theta)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hFCFail : 272 * S b0 hb0 e ≤ (B b0 hb0)^2) :
    ((64 - theta - sigma) * A4 e) / (B b0 hb0)^2 ≤
      Measure.real outer (Bad e theta) := by
  have hFull : 256 * S b0 hb0 e ≤
      Wbar b0 hb0 e + Eunused e := by
    have hNot : ¬ (B b0 hb0)^2 < 272 * S b0 hb0 e :=
      not_lt_of_ge hFCFail
    by_contra hBad
    have hStrict : Wbar b0 hb0 e + Eunused e < 256 * S b0 hb0 e :=
      lt_of_not_ge hBad
    exact hNot ((p4Q2PZ37AEY_originalTrueFC_iff_fullResidualAndUnused H e).mpr
      hStrict)
  have hLower : 64 * A4 e ≤ R4 e + Eunused e := by
    rw [p4Q2PZ37AEZ_originalWeightedFour_eq_trueCovariance H e,
      p4Q2PZ37AEZ_originalWeightedHigher_eq_trueResidual H e]
    nlinarith only [hFull]
  have hUpper :=
    p4Q2PZ37AFA_originalExceptionalHaarMoment_upper H e theta hTheta
  have hFC : 0 < (B b0 hb0)^2 :=
    p4Q2PZ37ADB_originalFCsq_pos H b0 p4Q2PZ37ADC_fixedCoupling_pos e
  apply (div_le_iff₀ hFC).mpr
  nlinarith only [hLower, hUpper, hSlack]

/-- When theta+sigma<64, the TRUE FC test can fail only if a genuine
positive-Haar exceptional transfer-boundary set remains. -/
theorem p4Q2PZ37AFA_failedTrueFC_exceptionalMass_pos
    (e : Link) (theta sigma : ℝ) (hTheta : 0 ≤ theta)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hTotal : theta + sigma < 64)
    (hFCFail : 272 * S b0 hb0 e ≤ (B b0 hb0)^2) :
    0 < Measure.real outer (Bad e theta) := by
  have hFloor := p4Q2PZ37AFA_failedTrueFC_exceptionalMass_floor
    H e theta sigma hTheta hSlack hFCFail
  have hp := p4Q2PZ37AEZ_originalWeightedFour_pos H e
  have hFC := p4Q2PZ37ADB_originalFCsq_pos
    H b0 p4Q2PZ37ADC_fixedCoupling_pos e
  have hCoef : 0 < 64 - theta - sigma := by linarith only [hTotal]
  have hPos : 0 < ((64 - theta - sigma) * A4 e) / (B b0 hb0)^2 :=
    div_pos (mul_pos hCoef hp) hFC
  exact hPos.trans_le hFloor

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFA_compactExceptionalIntegralBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFA_originalExceptionalBoundary_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFA_originalExceptionalBoundary_iff_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFA_originalExceptionalHaarMoment_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFA_originalExceptionalMass_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFA_originalExceptionalMass_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFA_originalExceptionalMass_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFA_originalExceptionalMassFC_gives_trueFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFA_originalExceptionalMassFC_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFA_nonpositiveBudget_exceptionalMass_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFA_nonpositiveBudget_exceptionalMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFA_failedTrueFC_exceptionalMass_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFA_failedTrueFC_exceptionalMass_pos
