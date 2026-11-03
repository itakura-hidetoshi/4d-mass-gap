import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullMomentFCVarianceSlackV5_PZ37AEY
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHigherModeHaarTailV5_PZ37ACR
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEZ — true Perron-weighted transfer residual/FC gate

Continue the proved AEX no-go and AEY full-moment decomposition, keeping
the original interacting finite-volume Wilson SU(2), actual centered
Gauss-law physical source, genuine Perron vacuum, real original transfer
section U_z, its updated right-link density, and the original outer
pair-Haar probability measure.

At ADC's original fixed positive coupling b0, define
  a_H = integral_outer P_z^2 * sum_j m_U(z,j)^2 = 4*S_H > 0,
  w_H = integral_outer P_z^2 * residual_U(z) = W_H >= 0,
  e_H = B_H^2 - integral_outer P_z^2 * Var_Haar(U_z) >= 0.

The exact dimensionless transfer ratios
  r_H=w_H/a_H, s_H=e_H/a_H
are both nonnegative. The *actual* ACO squared-GI mean certificate is
positive exactly if r_H<64. The stronger full-moment FC test is
equivalent to r_H+s_H<64. The distinction is structural: the genuine
GI certificate does not require FC envelope saturation.

A genuine pointwise original-transfer bound
  residual_U(z) <= theta * sum_j m_U(z,j)^2  (for EVERY actual boundary z)
implies the weighted mean inequality w_H<=theta*a_H; hence theta<64
suffices for the positive mean certificate and a real open-Haar set
of nonzero original signed two-posterior GI. If an independent genuine
FC-slack control e_H<=sigma*a_H is also obtained, theta+sigma<64
suffices for the original FC numeric test. These are EXPLICIT
CONDITIONAL hypotheses, not smuggled estimates of the actual Wilson
transfer. Conversely failure of the positive mean certificate forces
a real boundary violating any such proposed all-context theta<64
bound; a failed FC test with controlled slack does likewise.

No surrogate transfer, independent Haar distribution, replacement
source, altered threshold, volume-uniform estimate, H1-H4 or continuum
4D Yang--Mills mass-gap claim is made. The AEX two-ball no-go remains.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local instance p4Q2PZ37AEZ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEZ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEZ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEZ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEZ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AEZ_probability : IsProbabilityMeasure mu :=
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
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local notation "tA2" => p4Q2PZ37ACQ_transferAmplitudeSq H
local notation "tW" => p4Q2PZ37ACQ_transferResidualEnergy H
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H
local notation "Wz" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Eunused" => p4Q2PZ37AEY_originalFCUnusedVariance H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H

local instance p4Q2PZ37AEZ_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AEZ_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Genuine weighted first-four SU(2) Haar transfer energy; no weight
or updated transfer density is discarded. -/
def p4Q2PZ37AEZ_originalWeightedTransferFourMoment (e : Link) : ℝ :=
  ∫ z : Pair, (P b0 hb0 z)^2 * tA2 b0 hb0 e z ∂outer
local notation "A4" => p4Q2PZ37AEZ_originalWeightedTransferFourMoment H

/-- Actual higher-character weighted transfer energy. -/
def p4Q2PZ37AEZ_originalWeightedTransferHigherMoment (e : Link) : ℝ :=
  ∫ z : Pair, (P b0 hb0 z)^2 * tW b0 hb0 e z ∂outer
local notation "R4" => p4Q2PZ37AEZ_originalWeightedTransferHigherMoment H

/-- Exact dimensionless true-transfer higher-residual-to-signal ratio. -/
def p4Q2PZ37AEZ_originalTransferResidualRatio (e : Link) : ℝ :=
  R4 e / A4 e
local notation "ratio" => p4Q2PZ37AEZ_originalTransferResidualRatio H

/-- Exact dimensionless unused ORIGINAL FC envelope ratio, in units of
the genuine Perron-weighted four-mode transfer energy. -/
def p4Q2PZ37AEZ_originalTransferFCUnusedRatio (e : Link) : ℝ :=
  Eunused e / A4 e
local notation "slack" => p4Q2PZ37AEZ_originalTransferFCUnusedRatio H

/-- The original four-mode transfer energy is exactly 4*S, not the
unweighted independent-Haar expression. -/
theorem p4Q2PZ37AEZ_originalWeightedFour_eq_trueCovariance (e : Link) :
    A4 e = 4 * S b0 hb0 e := by
  exact p4Q2PZ37ACQ_weightedTransferAmplitude_integral H b0 hb0 e

/-- The original higher transfer energy is exactly the TRUE physical
receiver higher Haar residual Wbar. -/
theorem p4Q2PZ37AEZ_originalWeightedHigher_eq_trueResidual (e : Link) :
    R4 e = Wbar b0 hb0 e := by
  exact p4Q2PZ37ACQ_weightedTransferResidual_integral H b0 hb0 e

/-- The genuine actual transfer's weighted first-four denominator
is strictly positive at EVERY finite volume and genuine link. -/
theorem p4Q2PZ37AEZ_originalWeightedFour_pos (e : Link) : 0 < A4 e := by
  rw [p4Q2PZ37AEZ_originalWeightedFour_eq_trueCovariance]
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos
    H b0 p4Q2PZ37ADC_fixedCoupling_pos e
  linarith only [hs]

/-- The original source/transfer FC slack also has an exact expression
using the REAL updated-Perron transfer variance, not an imposed bound. -/
theorem p4Q2PZ37AEZ_originalFCUnused_eq_weightedTransferVariance
    (e : Link) :
    Eunused e = (B b0 hb0)^2 -
      (∫ z : Pair, (P b0 hb0 z)^2 *
        CompactEnergyMismatchMoment.variance mu (U b0 hb0 f0 e z) ∂outer) := by
  unfold p4Q2PZ37AEY_originalFCUnusedVariance
  rw [p4Q2PZ37ACQ_weightedTransferVariance_integral H b0 hb0 e]

/-- Neither of the actual dimensionless losses is a negative quantity.
This says nothing about a useful numerical UPPER bound on either. -/
theorem p4Q2PZ37AEZ_originalTransferLossRatios_nonneg (e : Link) :
    0 ≤ ratio e ∧ 0 ≤ slack e := by
  have hp := p4Q2PZ37AEZ_originalWeightedFour_pos H e
  have hR : 0 ≤ R4 e := by
    rw [p4Q2PZ37AEZ_originalWeightedHigher_eq_trueResidual]
    exact p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b0 hb0 e
  have hE := p4Q2PZ37AEY_originalFCUnusedVariance_nonneg H e
  exact ⟨div_nonneg hR hp.le, div_nonneg hE hp.le⟩

/-- The EXACT true squared GI mean certificate uses the physical
residual ratio alone; NO original FC unused variance is required. -/
theorem p4Q2PZ37AEZ_originalBudget_pos_iff_transferRatio_lt64
    (e : Link) :
    0 < Budget b0 hb0 e ↔ ratio e < 64 := by
  have hp := p4Q2PZ37AEZ_originalWeightedFour_pos H e
  have h64 : 64 * A4 e = 256 * S b0 hb0 e := by
    rw [p4Q2PZ37AEZ_originalWeightedFour_eq_trueCovariance]
    ring
  have hRatio : (ratio e < 64) ↔
      Wbar b0 hb0 e < 256 * S b0 hb0 e := by
    change R4 e / A4 e < 64 ↔ _
    rw [div_lt_iff₀ hp, p4Q2PZ37AEZ_originalWeightedHigher_eq_trueResidual, h64]
  exact (p4Q2PZ37AEY_originalBudget_pos_iff_trueHigherHaar H e).trans hRatio.symm

/-- Strict original FC numerical dominance instead requires BOTH
higher Haar modes and the actual unused FC envelope ratio to fit. -/
theorem p4Q2PZ37AEZ_originalTrueFC_iff_transferRatioPlusSlack_lt64
    (e : Link) :
    (B b0 hb0)^2 < 272 * S b0 hb0 e ↔
      ratio e + slack e < 64 := by
  have hp := p4Q2PZ37AEZ_originalWeightedFour_pos H e
  have h64 : 64 * A4 e = 256 * S b0 hb0 e := by
    rw [p4Q2PZ37AEZ_originalWeightedFour_eq_trueCovariance]
    ring
  have hRatio : (ratio e + slack e < 64) ↔
      Wbar b0 hb0 e + Eunused e < 256 * S b0 hb0 e := by
    change R4 e / A4 e + Eunused e / A4 e < 64 ↔ _
    rw [← add_div, div_lt_iff₀ hp,
      p4Q2PZ37AEZ_originalWeightedHigher_eq_trueResidual, h64]
  exact (p4Q2PZ37AEY_originalTrueFC_iff_fullResidualAndUnused H e).trans hRatio.symm

/-- Genuine all-context transfer-side pointwise comparison is strong
enough to compare the ACTUAL Perron-weighted outer Haar integrals.
The hypothesis is NOT asserted unconditionally. -/
theorem p4Q2PZ37AEZ_originalAllContextTransferBound_gives_weightedMoment
    (e : Link) (theta : ℝ)
    (hPoint : ∀ z : Pair,
      tW b0 hb0 e z ≤ theta * tA2 b0 hb0 e z) :
    R4 e ≤ theta * A4 e := by
  have hPointPhysical (z : Pair) :
      Wz b0 hb0 e z ≤ theta * (A b0 hb0 e z)^2 := by
    calc
      Wz b0 hb0 e z =
          (P b0 hb0 z)^2 * tW b0 hb0 e z :=
        p4Q2PZ37ACQ_originalResidualEnergy_eq_transfer H b0 hb0 e z
      _ ≤ (P b0 hb0 z)^2 * (theta * tA2 b0 hb0 e z) :=
        mul_le_mul_of_nonneg_left (hPoint z) (sq_nonneg _)
      _ = theta * ((P b0 hb0 z)^2 * tA2 b0 hb0 e z) := by ring
      _ = theta * (A b0 hb0 e z)^2 := by
        rw [p4Q2PZ37ACQ_originalAmplitudeSq_eq_transfer H b0 hb0 e z]
  have hWI : Integrable (fun z : Pair => Wz b0 hb0 e z) outer :=
    (p4Q2PZ37ACR_originalResidual_continuous H b0 hb0 e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAI : Integrable (fun z : Pair => theta * (A b0 hb0 e z)^2) outer :=
    (continuous_const.mul
      (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b0 hb0 e)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hInt : (∫ z : Pair, Wz b0 hb0 e z ∂outer) ≤
      ∫ z : Pair, theta * (A b0 hb0 e z)^2 ∂outer := by
    apply integral_mono hWI hAI
    intro z
    exact hPointPhysical z
  rw [integral_const_mul,
    p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral H b0 hb0 e] at hInt
  change Wbar b0 hb0 e ≤ theta * (4 * S b0 hb0 e) at hInt
  rw [p4Q2PZ37AEZ_originalWeightedHigher_eq_trueResidual,
    p4Q2PZ37AEZ_originalWeightedFour_eq_trueCovariance]
  exact hInt

/-- A verified genuine original-transfer pointwise ratio theta<64
would be a NEW quantitative sufficient bound for positive mean GI.
No such all-context theta has yet been derived from the Wilson kernel. -/
theorem p4Q2PZ37AEZ_originalPointwiseTransferRatio_gives_positiveBudget
    (e : Link) (theta : ℝ)
    (hPoint : ∀ z : Pair,
      tW b0 hb0 e z ≤ theta * tA2 b0 hb0 e z)
    (hTheta : theta < 64) :
    0 < Budget b0 hb0 e := by
  have hW := p4Q2PZ37AEZ_originalAllContextTransferBound_gives_weightedMoment
    H e theta hPoint
  have hp := p4Q2PZ37AEZ_originalWeightedFour_pos H e
  have hlt : R4 e < 64 * A4 e :=
    hW.trans_lt (mul_lt_mul_of_pos_right hTheta hp)
  exact (p4Q2PZ37AEZ_originalBudget_pos_iff_transferRatio_lt64 H e).mpr
    ((div_lt_iff₀ hp).mpr hlt)

/-- The same conditional original-transfer bound propagates through
the existing genuine two-interacting-posterior open-GI theorem. -/
theorem p4Q2PZ37AEZ_originalPointwiseTransferRatio_gives_openGI
    (e : Link) (theta : ℝ)
    (hPoint : ∀ z : Pair,
      tW b0 hb0 e z ≤ theta * tA2 b0 hb0 e z)
    (hTheta : theta < 64) :
    ∃ T : Set Pair, IsOpen T ∧
      0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 f0 e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion H b0 hb0 e
    (p4Q2PZ37AEZ_originalPointwiseTransferRatio_gives_positiveBudget
      H e theta hPoint hTheta)

/-- With separately verified original FC slack sigma, the combined
pointwise-transfer and real source-envelope bounds suffice for the
STRONGER full-moment FC threshold. Both inputs are explicit hypotheses. -/
theorem p4Q2PZ37AEZ_originalTransferAndFCSlack_gives_trueFC
    (e : Link) (theta sigma : ℝ)
    (hPoint : ∀ z : Pair,
      tW b0 hb0 e z ≤ theta * tA2 b0 hb0 e z)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hTotal : theta + sigma < 64) :
    (B b0 hb0)^2 < 272 * S b0 hb0 e := by
  have hW := p4Q2PZ37AEZ_originalAllContextTransferBound_gives_weightedMoment
    H e theta hPoint
  have hp := p4Q2PZ37AEZ_originalWeightedFour_pos H e
  have hBound : R4 e + Eunused e < 64 * A4 e := by
    calc
      R4 e + Eunused e ≤ theta * A4 e + sigma * A4 e :=
        add_le_add hW hSlack
      _ = (theta + sigma) * A4 e := by ring
      _ < 64 * A4 e := mul_lt_mul_of_pos_right hTotal hp
  have hTrue : Wbar b0 hb0 e + Eunused e < 256 * S b0 hb0 e := by
    calc
      Wbar b0 hb0 e + Eunused e = R4 e + Eunused e := by
        rw [p4Q2PZ37AEZ_originalWeightedHigher_eq_trueResidual]
      _ < 64 * A4 e := hBound
      _ = 256 * S b0 hb0 e := by
        rw [p4Q2PZ37AEZ_originalWeightedFour_eq_trueCovariance]
        ring
  exact (p4Q2PZ37AEY_originalTrueFC_iff_fullResidualAndUnused H e).mpr hTrue

/-- FC numeric certification through the original source envelope
implies the inherited true signed-GI response in an open genuine-Haar
set; no theorem assumes a surrogate receiver. -/
theorem p4Q2PZ37AEZ_originalTransferAndFCSlack_gives_openGI
    (e : Link) (theta sigma : ℝ)
    (hPoint : ∀ z : Pair,
      tW b0 hb0 e z ≤ theta * tA2 b0 hb0 e z)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hTotal : theta + sigma < 64) :
    ∃ T : Set Pair, IsOpen T ∧
      0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 f0 e z| := by
  exact p4Q2PZ37ADE_fixedCovarianceFC_gives_openGI H e
    (p4Q2PZ37AEZ_originalTransferAndFCSlack_gives_trueFC
      H e theta sigma hPoint hSlack hTotal)

/-- If the positive original GI MEAN CERTIFICATE fails, any proposed
all-context transfer bound theta<64 must be violated at a GENUINE
original boundary configuration. This does not imply actual GI vanishes. -/
theorem p4Q2PZ37AEZ_nonpositiveBudget_has_trueTransferViolation
    (e : Link) (theta : ℝ) (hTheta : theta < 64)
    (hNonpos : Budget b0 hb0 e ≤ 0) :
    ∃ z : Pair,
      theta * tA2 b0 hb0 e z < tW b0 hb0 e z := by
  by_contra hn
  have hEvery : ∀ z : Pair, tW b0 hb0 e z ≤ theta * tA2 b0 hb0 e z := by
    intro z
    by_contra hbad
    exact hn ⟨z, lt_of_not_ge hbad⟩
  have hp := p4Q2PZ37AEZ_originalPointwiseTransferRatio_gives_positiveBudget
    H e theta hEvery hTheta
  exact (not_lt_of_ge hNonpos) hp

/-- Even if an independently checked genuine FC slack bound is supplied,
failure of the full-moment FC test forces a real boundary violating
every all-context transfer bound with theta+sigma<64. -/
theorem p4Q2PZ37AEZ_failedTrueFC_has_trueTransferViolation
    (e : Link) (theta sigma : ℝ)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hTotal : theta + sigma < 64)
    (hFCfail : 272 * S b0 hb0 e ≤ (B b0 hb0)^2) :
    ∃ z : Pair,
      theta * tA2 b0 hb0 e z < tW b0 hb0 e z := by
  by_contra hn
  have hEvery : ∀ z : Pair, tW b0 hb0 e z ≤ theta * tA2 b0 hb0 e z := by
    intro z
    by_contra hbad
    exact hn ⟨z, lt_of_not_ge hbad⟩
  have hp := p4Q2PZ37AEZ_originalTransferAndFCSlack_gives_trueFC
    H e theta sigma hEvery hSlack hTotal
  exact (not_lt_of_ge hFCfail) hp

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_originalWeightedFour_eq_trueCovariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_originalWeightedHigher_eq_trueResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_originalWeightedFour_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_originalFCUnused_eq_weightedTransferVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_originalTransferLossRatios_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_originalBudget_pos_iff_transferRatio_lt64
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_originalTrueFC_iff_transferRatioPlusSlack_lt64
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_originalAllContextTransferBound_gives_weightedMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_originalPointwiseTransferRatio_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_originalPointwiseTransferRatio_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_originalTransferAndFCSlack_gives_trueFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_originalTransferAndFCSlack_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_nonpositiveBudget_has_trueTransferViolation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEZ_failedTrueFC_has_trueTransferViolation
