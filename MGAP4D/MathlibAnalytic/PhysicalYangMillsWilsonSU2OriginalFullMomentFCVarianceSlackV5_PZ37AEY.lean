import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTwoBallFCNumericalObstructionV5_PZ37AEX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEY — genuine full-moment FC variance slack and residual budget

Continue AEX append-only. The AEX no-go applies only to the conservative
AEW two-ball floor, never to the true outer-Haar covariance moment S.

At the unchanged original fixed coupling b0, use the SAME Wilson SU(2)
receiver, centered Gauss-law source, true Perron transfer, original
pair-Haar measure, and true FC envelope B. Let
  Vbar = integral_outer Var_Haar(F_z) = 16*S + Wbar.
Define the *derived* (not hypothesized) nonnegative unused FC allowance
  E = B^2 - Vbar >= 0.
Then exactly
  B^2 = 16*S + Wbar + E,
  272*S-B^2 = 256*S-(Wbar+E).
Thus the true FC threshold is equivalent to Wbar+E < 256*S.
The dimensionless non-four-mode-plus-unused-FC fraction
  ell = (Wbar+E)/B^2
satisfies 16*S/B^2 + ell = 1 and 0 <= ell < 1.
The true numerical threshold is exactly ell < 16/17.

These identities isolate TWO genuine obstructions: the actual higher
SU(2) Haar residual and slack in the actual FC bound. The absence of a
quantitative estimate for either is NOT silently replaced by positivity
of S or a small-ball estimate. Conditional sufficient conditions and
their nonpositive-mean converse are proved. All constants remain H-
dependent; no H-uniform positivity, actual GI necessity, or continuum
Yang--Mills mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local instance p4Q2PZ37AEY_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEY_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEY_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEY_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEY_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AEY_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Vbar" => p4Q2PZ37ACK_originalReceiverVarianceMoment H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "u" => p4Q2PZ37ADB_originalSignalFCFraction H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H

local instance p4Q2PZ37AEY_links : Fintype Link := Fintype.ofFinite _

/-- The actual nonnegative amount by which the genuine FC envelope
exceeds the original receiver's full outer-Haar variance. -/
def p4Q2PZ37AEY_originalFCUnusedVariance (e : Link) : ℝ :=
  (B b0 hb0) ^ 2 - Vbar b0 hb0 e

local notation "Eunused" => p4Q2PZ37AEY_originalFCUnusedVariance H

theorem p4Q2PZ37AEY_originalFCUnusedVariance_nonneg (e : Link) :
    0 ≤ Eunused e := by
  unfold p4Q2PZ37AEY_originalFCUnusedVariance
  exact sub_nonneg.mpr
    (p4Q2PZ37ADB_originalVarianceMoment_le_FC H b0 hb0 e)

/-- The complete genuine variance allocation, retaining the
nonnegative higher-character remainder AND the unused FC allowance. -/
theorem p4Q2PZ37AEY_originalFullHaarFC_partition (e : Link) :
    (B b0 hb0) ^ 2 =
      16 * S b0 hb0 e + Wbar b0 hb0 e + Eunused e := by
  unfold p4Q2PZ37AEY_originalFCUnusedVariance
  rw [p4Q2PZ37ACK_originalVarianceMoment_eq H b0 hb0 e]
  ring

/-- Exact full-moment margin: no two-ball floor occurs here. -/
theorem p4Q2PZ37AEY_originalFullMomentFC_margin_exact (e : Link) :
    272 * S b0 hb0 e - (B b0 hb0) ^ 2 =
      256 * S b0 hb0 e - (Wbar b0 hb0 e + Eunused e) := by
  rw [p4Q2PZ37AEY_originalFullHaarFC_partition H e]
  ring

/-- The original strict numerical test is equivalent to controlling
the sum of TWO derived genuine physical obstructions. -/
theorem p4Q2PZ37AEY_originalTrueFC_iff_fullResidualAndUnused (e : Link) :
    (B b0 hb0) ^ 2 < 272 * S b0 hb0 e ↔
      Wbar b0 hb0 e + Eunused e < 256 * S b0 hb0 e := by
  have hEq := p4Q2PZ37AEY_originalFullMomentFC_margin_exact H e
  constructor <;> intro h <;> linarith only [hEq, h]

/-- Fraction of the SAME original FC envelope accounted for by
higher-SU(2) Haar modes plus unused envelope capacity. -/
def p4Q2PZ37AEY_originalNonFourPlusUnusedFraction (e : Link) : ℝ :=
  (Wbar b0 hb0 e + Eunused e) / (B b0 hb0) ^ 2

local notation "loss" => p4Q2PZ37AEY_originalNonFourPlusUnusedFraction H

/-- The genuine four-mode FC signal share and its two-part complement
exhaust the same original physical FC envelope exactly. -/
theorem p4Q2PZ37AEY_originalFCFraction_partition (e : Link) :
    u b0 hb0 e + loss e = 1 := by
  have hB : 0 < (B b0 hb0) ^ 2 :=
    p4Q2PZ37ADB_originalFCsq_pos H b0 p4Q2PZ37ADC_fixedCoupling_pos e
  have hp := p4Q2PZ37AEY_originalFullHaarFC_partition H e
  have hn : 16 * S b0 hb0 e + (Wbar b0 hb0 e + Eunused e) =
      (B b0 hb0) ^ 2 := by linarith only [hp]
  change (16 * S b0 hb0 e) / (B b0 hb0) ^ 2 +
    (Wbar b0 hb0 e + Eunused e) / (B b0 hb0) ^ 2 = 1
  calc
    _ = (16 * S b0 hb0 e + (Wbar b0 hb0 e + Eunused e)) /
          (B b0 hb0) ^ 2 := by simp only [add_div]
    _ = (B b0 hb0) ^ 2 / (B b0 hb0) ^ 2 := by rw [hn]
    _ = 1 := div_self (ne_of_gt hB)

/-- The two-part loss is a genuine dimensionless number in [0,1).
Its strict upper bound uses only the previously proved S>0. -/
theorem p4Q2PZ37AEY_originalNonFourPlusUnusedFraction_bounds (e : Link) :
    0 ≤ loss e ∧ loss e < 1 := by
  have hB : 0 < (B b0 hb0) ^ 2 :=
    p4Q2PZ37ADB_originalFCsq_pos H b0 p4Q2PZ37ADC_fixedCoupling_pos e
  have hW := p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b0 hb0 e
  have hE := p4Q2PZ37AEY_originalFCUnusedVariance_nonneg H e
  have hU := (p4Q2PZ37ADB_originalSignalFraction_pos_le_one
    H b0 p4Q2PZ37ADC_fixedCoupling_pos e).1
  have hp := p4Q2PZ37AEY_originalFCFraction_partition H e
  constructor
  · exact div_nonneg (add_nonneg hW hE) hB.le
  · linarith only [hp, hU]

/-- The precise AEY dimensionless criterion:
true full-Haar FC dominance if and only if the derived two-part
loss occupies less than 16/17 of the unchanged FC envelope. -/
theorem p4Q2PZ37AEY_originalLossFraction_iff_trueFC (e : Link) :
    loss e < (16 / 17 : ℝ) ↔
      (B b0 hb0) ^ 2 < 272 * S b0 hb0 e := by
  have hp := p4Q2PZ37AEY_originalFCFraction_partition H e
  have ht := p4Q2PZ37ADE_fixedSignal_iff_originalCovarianceFC H e
  constructor
  · intro hl
    apply ht.mp
    have hu : (1 / 17 : ℝ) < u b0 hb0 e := by
      linarith only [hp, hl]
    exact hu
  · intro hb
    have hu := ht.mpr hb
    linarith only [hp, hu]

/-- Explicit conditional analytical entry point: upper bound the
actual higher Haar energy and the genuine unused FC allowance by a
common true S; do not assume that either bound is available. -/
theorem p4Q2PZ37AEY_originalRelativeResidualSlack_suffices
    (e : Link) (theta : ℝ)
    (hControl :
      Wbar b0 hb0 e + Eunused e ≤ theta * S b0 hb0 e)
    (hTheta : theta < 256) :
    (B b0 hb0) ^ 2 < 272 * S b0 hb0 e := by
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos
    H b0 p4Q2PZ37ADC_fixedCoupling_pos e
  apply (p4Q2PZ37AEY_originalTrueFC_iff_fullResidualAndUnused H e).mpr
  exact lt_of_le_of_lt hControl (mul_lt_mul_of_pos_right hTheta hs)

/-- A verified physical residual/slack inequality yields a positive
original GI SQUARED mean certificate, with no substitute receiver. -/
theorem p4Q2PZ37AEY_originalRelativeResidualSlack_gives_positiveBudget
    (e : Link) (theta : ℝ)
    (hControl :
      Wbar b0 hb0 e + Eunused e ≤ theta * S b0 hb0 e)
    (hTheta : theta < 256) :
    0 < Budget b0 hb0 e := by
  exact p4Q2PZ37ADE_fixedCovarianceFC_gives_positiveBudget H e
    (p4Q2PZ37AEY_originalRelativeResidualSlack_suffices H e theta hControl hTheta)

/-- The same conditional inequality propagates through the EXISTING
original signed two-posterior theorem to an open positive-Haar set. -/
theorem p4Q2PZ37AEY_originalRelativeResidualSlack_gives_openGI
    (e : Link) (theta : ℝ)
    (hControl :
      Wbar b0 hb0 e + Eunused e ≤ theta * S b0 hb0 e)
    (hTheta : theta < 256) :
    ∃ Uset : Set Pair, IsOpen Uset ∧
      0 < Measure.real
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) Uset ∧
      ∀ z ∈ Uset,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z| := by
  exact p4Q2PZ37ADE_fixedCovarianceFC_gives_openGI H e
    (p4Q2PZ37AEY_originalRelativeResidualSlack_suffices H e theta hControl hTheta)

/-- Distinguish AEY's conservative original-FC numerical test from the
SHARP positive-mean sufficient GI certificate. At b0, the latter is
equivalent to Wbar < 256*S, with NO unused-FC slack term.
Thus FC dominance is sufficient, but it has NOT been proved necessary
for positive GI budget or the actual signed GI gap. -/
theorem p4Q2PZ37AEY_originalBudget_pos_iff_trueHigherHaar (e : Link) :
    0 < Budget b0 hb0 e ↔ Wbar b0 hb0 e < 256 * S b0 hb0 e := by
  have h :=
    p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_residual
      H b0 p4Q2PZ37ADC_fixedCoupling_pos e
  rw [p4Q2PZ37ADC_fixedCoupling_gap_eq_quarter] at h
  constructor
  · intro hb
    have hw := h.mp hb
    nlinarith only [hw]
  · intro hw
    apply h.mpr
    nlinarith only [hw]

/-- The exact higher-Haar residual obstruction for nonpositive mean
certificate, distinct from AEX's conservative two-ball obstruction. -/
theorem p4Q2PZ37AEY_nonpositiveBudget_iff_higherHaarObstruction
    (e : Link) :
    Budget b0 hb0 e ≤ 0 ↔ 256 * S b0 hb0 e ≤ Wbar b0 hb0 e := by
  simpa only [not_lt] using
    not_congr (p4Q2PZ37AEY_originalBudget_pos_iff_trueHigherHaar H e)

/-- Failure of the ORIGINAL positive GI mean sufficient certificate
forces the exact complementary lower residual/slack inequality.
It does NOT imply that the signed physical GI gap vanishes. -/
theorem p4Q2PZ37AEY_nonpositiveBudget_forces_fullResidualSlack (e : Link)
    (hNonpos : Budget b0 hb0 e ≤ 0) :
    256 * S b0 hb0 e ≤ Wbar b0 hb0 e + Eunused e := by
  have hOld :=
    p4Q2PZ37ADE_nonpositiveBudget_forces_FC_obstruction H e hNonpos
  have hEq := p4Q2PZ37AEY_originalFullMomentFC_margin_exact H e
  linarith only [hOld, hEq]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_originalFCUnusedVariance_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_originalFullHaarFC_partition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_originalFullMomentFC_margin_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_originalTrueFC_iff_fullResidualAndUnused
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_originalFCFraction_partition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_originalNonFourPlusUnusedFraction_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_originalLossFraction_iff_trueFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_originalRelativeResidualSlack_suffices
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_originalRelativeResidualSlack_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_originalRelativeResidualSlack_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_originalBudget_pos_iff_trueHigherHaar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_nonpositiveBudget_iff_higherHaarObstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEY_nonpositiveBudget_forces_fullResidualSlack
