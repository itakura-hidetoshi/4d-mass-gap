import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGIMeanVarianceThresholdV5_PZ37ACP

/-!
# P4-Q2-PZ37ACQ — exact Perron-weighted transfer-section four-mode projection

This module does not replace the interacting SU(2) Wilson receiver. It
expresses its genuine ACK four-mode Haar projection and its orthogonal
remainder in terms of ABZ's *actual* transfer section
  U_z(g) = I_{f0}(B[e:=g]) / sqrtDensity(A,B[e:=g])
and positive transfer/Perron prefactor
  P_z = ||T||^(-1) sqrtDensity(A,B).
ABZ proves F_z(g)=constant_z-P_z*U_z(g). The constant disappears from all
four zero-mean Haar coefficients, while P_z survives as a positive weight.

For all original contexts z, exactly:
  m_F(z,j) = -P_z*m_U(z,j)
  A_F(z)^2 = P_z^2 * sum_j m_U(z,j)^2
  W_F(z) = P_z^2 * integral (remainder_U(z,g))^2 dHaar(g).
Consequently the original outer pair-Haar law gives
  4*S = integral_outer P_z^2 * sum_j m_U(z,j)^2
  Wbar = integral_outer P_z^2 * residual_U(z),
  M_GI = integral_outer P_z^2 *
     (kappa*sum_j m_U(z,j)^2-rho*residual_U(z)).

This removes no original posterior, Perron factor, boundary data or
spatial source and makes the remaining physical obstruction explicit:
the weighted higher-mode energy must be controlled relative to the
weighted true transfer first-mode energy. Neither ratio inequality nor
unconditional positive GI is assumed or asserted. No common support,
uniformity in volume, H1-H4, continuum construction or mass gap follows.
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
local notation "φ" => p4Q2PZ37ACK_fourModeCharacter
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local instance p4Q2PZ37ACQ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACQ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACQ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACQ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACQ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACQ_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local notation "m" => p4Q2PZ37ACK_originalFourModeCoefficient H
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "Vbar" => p4Q2PZ37ACK_originalReceiverVarianceMoment H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "kappa" => p4Q2PZ37ACO_originalGISlopeSq
local notation "rho" => p4Q2PZ37ACI_originalPosteriorResidualEnvelope
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "Q" => p4Q2PZ37ACO_originalGISquaredMargin H
local notation "tau" => p4Q2PZ37ACP_originalPosteriorExponentGapSq
local instance p4Q2PZ37ACQ_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACQ_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Original transfer section's genuine SU(2) Haar coefficient, preserving
its right-link update and updated joint Perron half-density. -/
def p4Q2PZ37ACQ_transferCoefficient
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (j : Fin 4) : ℝ :=
  CompactFiniteHaarProjection.coefficient μ (U b hb f₀ e z) φ j
local notation "tm" => p4Q2PZ37ACQ_transferCoefficient H

/-- The four true first-character Fourier modes of the same transfer. -/
def p4Q2PZ37ACQ_transferAmplitudeSq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  ∑ j : Fin 4, (tm b hb e z j) ^ 2
local notation "tA2" => p4Q2PZ37ACQ_transferAmplitudeSq H

/-- The original normalized-SU(2)-Haar orthogonal remainder of U_z. -/
def p4Q2PZ37ACQ_transferResidualEnergy
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  ∫ g : G, (CompactFiniteHaarProjection.remainder μ
    (U b hb f₀ e z) φ g) ^ 2 ∂μ
local notation "tW" => p4Q2PZ37ACQ_transferResidualEnergy H

/-- True transfer-side squared GI mean-margin integrand, without P_z^2. -/
def p4Q2PZ37ACQ_transferSquaredGIMargin
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  kappa b * tA2 b hb e z - rho b * tW b hb e z
local notation "tQ" => p4Q2PZ37ACQ_transferSquaredGIMargin H

/-- Actual fixed-boundary ABZ response difference: the unupdated term
cancels, but the updated Perron half-density inside U does not. -/
theorem p4Q2PZ37ACQ_originalReceiver_difference_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (g h : G) :
    F b hb f₀ e z g - F b hb f₀ e z h =
      -(P b hb z) * (U b hb f₀ e z g - U b hb f₀ e z h) := by
  have hd := p4Q2PZ37ABZ_originalDifference_eq_transferSection
    H b hb f₀ e z g h
  change F b hb f₀ e z g - F b hb f₀ e z h =
    P b hb z * (U b hb f₀ e z h - U b hb f₀ e z g) at hd
  rw [hd]
  ring

/-- Each of the four original receiver coefficients is the corresponding
REAL transfer-section coefficient times the same negative Perron factor. -/
theorem p4Q2PZ37ACQ_originalCoefficient_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (j : Fin 4) :
    m b hb e z j = -(P b hb z) * tm b hb e z j := by
  have hF : Continuous (F b hb f₀ e z) :=
    (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2
      (by norm_num) b hb f₀ e).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hU : Continuous (U b hb f₀ e z) :=
    p4Q2PZ37ABZ_originalTransferSection_continuous H b hb f₀ e z
  have hCov := CompactEnergyMismatchMoment.covariance_of_difference_eq μ
    (F b hb f₀ e z) (U b hb f₀ e z) (φ j) (-(P b hb z))
    hF hU (p4Q2PZ37ACK_fourModeCharacter_continuous j)
    (p4Q2PZ37ACQ_originalReceiver_difference_eq_transfer H b hb e z)
  change (∫ g : G, F b hb f₀ e z g * φ j g ∂μ) -
      (∫ g : G, F b hb f₀ e z g ∂μ) * (∫ g : G, φ j g ∂μ) =
    -(P b hb z) *
      ((∫ g : G, U b hb f₀ e z g * φ j g ∂μ) -
       (∫ g : G, U b hb f₀ e z g ∂μ) * (∫ g : G, φ j g ∂μ)) at hCov
  rw [p4Q2PZ37ACK_fourModeCharacter_mean_zero j] at hCov
  simp only [mul_zero, sub_zero] at hCov
  exact hCov

/-- Positive-prefactor factorization of the genuine SAME-context four-mode
covariance amplitude, without replacing the receiver by a surrogate. -/
theorem p4Q2PZ37ACQ_originalAmplitudeSq_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    (A b hb e z) ^ 2 = (P b hb z) ^ 2 * tA2 b hb e z := by
  rw [p4Q2PZ37ACM_originalCovarianceAmplitude_sq H b hb e z]
  change (∑ j : Fin 4, (m b hb e z j) ^ 2) =
    (P b hb z) ^ 2 * (∑ j : Fin 4, (tm b hb e z j) ^ 2)
  calc
    (∑ j : Fin 4, (m b hb e z j) ^ 2) =
        ∑ j : Fin 4, (P b hb z) ^ 2 * (tm b hb e z j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [p4Q2PZ37ACQ_originalCoefficient_eq_transfer H b hb e z j]
          ring
    _ = _ := by rw [Finset.mul_sum]

/-- True transfer residual has its own nonnegative original Haar-square
presentation; the four exact Gram quarters are not modified. -/
theorem p4Q2PZ37ACQ_transferResidualEnergy_eq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    tW b hb e z =
      CompactEnergyMismatchMoment.variance μ (U b hb f₀ e z) -
        4 * tA2 b hb e z := by
  exact CompactFiniteHaarProjection.pythagoras μ
    (U b hb f₀ e z) φ
    (p4Q2PZ37ABZ_originalTransferSection_continuous H b hb f₀ e z)
    p4Q2PZ37ACK_fourModeCharacter_continuous
    p4Q2PZ37ACK_fourModeCharacter_mean_zero
    p4Q2PZ37ACK_fourModeCharacter_gram

/-- Actual physical higher-mode energy scales with the SAME squared Perron
prefactor. It is not bounded by the four character modes. -/
theorem p4Q2PZ37ACQ_originalResidualEnergy_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    W b hb e z = (P b hb z) ^ 2 * tW b hb e z := by
  have hm (j : Fin 4) := p4Q2PZ37ACQ_originalCoefficient_eq_transfer H b hb e z j
  have hs : (∑ j : Fin 4, (m b hb e z j) ^ 2) =
      (P b hb z) ^ 2 * (∑ j : Fin 4, (tm b hb e z j) ^ 2) := by
    calc
      _ = ∑ j : Fin 4, (P b hb z) ^ 2 * (tm b hb e z j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hm j]
        ring
      _ = _ := by rw [Finset.mul_sum]
  rw [p4Q2PZ37ACK_originalFourModeResidualEnergy_eq H b hb e z,
    p4Q2PZ37ACA_originalReceiver_variance_eq_transfer H b hb f₀ e z,
    p4Q2PZ37ACQ_transferResidualEnergy_eq H b hb e z]
  change (P b hb z) ^ 2 *
      CompactEnergyMismatchMoment.variance μ (U b hb f₀ e z) -
        4 * (∑ j : Fin 4, (m b hb e z j) ^ 2) =
      (P b hb z) ^ 2 *
        (CompactEnergyMismatchMoment.variance μ (U b hb f₀ e z) -
          4 * (∑ j : Fin 4, (tm b hb e z j) ^ 2))
  rw [hs]
  ring

/-- Nonnegative original Haar square of the genuine updated transfer
section's higher-mode remainder, at each fixed pair of original boundaries. -/
theorem p4Q2PZ37ACQ_transferResidualEnergy_nonneg
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    0 ≤ tW b hb e z :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- Nonnegative sum of FOUR actual character coefficients, without any
assumed componentwise relation to the true physical source. -/
theorem p4Q2PZ37ACQ_transferAmplitudeSq_nonneg
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    0 ≤ tA2 b hb e z := by
  unfold p4Q2PZ37ACQ_transferAmplitudeSq
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

/-- The unmodified pair-Haar mean of the Perron-weighted original
transfer's four first character modes is precisely 4*S>0 for b>0. -/
theorem p4Q2PZ37ACQ_weightedTransferAmplitude_integral
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    (∫ z : Pair, (P b hb z) ^ 2 * tA2 b hb e z ∂outer) =
      4 * S b hb e := by
  calc
    _ = ∫ z : Pair, (A b hb e z) ^ 2 ∂outer := by
      apply integral_congr_ae
      filter_upwards with z
      exact (p4Q2PZ37ACQ_originalAmplitudeSq_eq_transfer H b hb e z).symm
    _ = 4 * S b hb e :=
      p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral H b hb e

/-- Exact outer mean of the actual higher-mode transfer residual with the
true physical Perron weight, without dropping that weight. -/
theorem p4Q2PZ37ACQ_weightedTransferResidual_integral
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    (∫ z : Pair, (P b hb z) ^ 2 * tW b hb e z ∂outer) =
      Wbar b hb e := by
  change (∫ z : Pair, (P b hb z) ^ 2 * tW b hb e z ∂outer) =
    ∫ z : Pair, W b hb e z ∂outer
  apply integral_congr_ae
  filter_upwards with z
  exact (p4Q2PZ37ACQ_originalResidualEnergy_eq_transfer H b hb e z).symm

/-- Actual pair-Haar weighted physical transfer-section variance equals
the UNCHANGED mean variance of the FF receiver. -/
theorem p4Q2PZ37ACQ_weightedTransferVariance_integral
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    (∫ z : Pair, (P b hb z) ^ 2 *
        CompactEnergyMismatchMoment.variance μ (U b hb f₀ e z) ∂outer) =
      Vbar b hb e := by
  change (∫ z : Pair, (P b hb z) ^ 2 *
        CompactEnergyMismatchMoment.variance μ (U b hb f₀ e z) ∂outer) =
    ∫ z : Pair, CompactEnergyMismatchMoment.variance μ (F b hb f₀ e z) ∂outer
  apply integral_congr_ae
  filter_upwards with z
  exact (p4Q2PZ37ACA_originalReceiver_variance_eq_transfer H b hb f₀ e z).symm

/-- Crucial SAME-context identity: the genuine original squared GI
orbit-margin equals the squared Perron factor times the transfer margin. -/
theorem p4Q2PZ37ACQ_originalSquaredGIMargin_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    Q b hb e z = (P b hb z) ^ 2 * tQ b hb e z := by
  unfold p4Q2PZ37ACO_originalGISquaredMargin
    p4Q2PZ37ACQ_transferSquaredGIMargin
  rw [p4Q2PZ37ACQ_originalAmplitudeSq_eq_transfer H b hb e z,
    p4Q2PZ37ACQ_originalResidualEnergy_eq_transfer H b hb e z]
  ring

/-- Original GI mean budget as an EXPLICIT weighted integral of the
unchanged physical transfer section and its four SU(2) Haar modes. -/
theorem p4Q2PZ37ACQ_weightedTransferGIMargin_integral
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    (∫ z : Pair, (P b hb z) ^ 2 * tQ b hb e z ∂outer) =
      Budget b hb e := by
  calc
    _ = ∫ z : Pair, Q b hb e z ∂outer := by
      apply integral_congr_ae
      filter_upwards with z
      exact (p4Q2PZ37ACQ_originalSquaredGIMargin_eq_transfer H b hb e z).symm
    _ = Budget b hb e :=
      p4Q2PZ37ACO_originalGIMeanBudget_integral H b hb e

/-- The exact ACP physical GI positivity criterion rewritten solely as
the relative original Perron-weighted transfer first-mode/remainder test.
The test remains OPEN for the unchanged Wilson receiver. -/
theorem p4Q2PZ37ACQ_originalGIBudget_pos_iff_weightedTransfer
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < Budget b hb.le e ↔
      tau b * (∫ z : Pair, (P b hb.le z) ^ 2 * tW b hb.le e z ∂outer) <
        16 * (∫ z : Pair, (P b hb.le z) ^ 2 * tA2 b hb.le e z ∂outer) := by
  rw [p4Q2PZ37ACQ_weightedTransferResidual_integral H b hb.le e,
    p4Q2PZ37ACQ_weightedTransferAmplitude_integral H b hb.le e,
    p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_residual H b hb e]
  constructor <;> intro h <;> nlinarith only [h]

/-- An unconditional genuine context with a Perron-independent relative
transfer residual comparison follows from ACO's original positive-mass
same-context construction. No physical GI positivity premise is needed. -/
theorem p4Q2PZ37ACQ_exists_transfer_relativeResidual
    (b : ℝ) (hb : 0 < b) (e : Link)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ z : Pair, 0 < tA2 b hb.le e z ∧
      (4 * S b hb.le e) * tW b hb.le e z <
        (Wbar b hb.le e + epsilon) * tA2 b hb.le e z := by
  obtain ⟨z, hA, hRatio⟩ :=
    p4Q2PZ37ACO_exists_sameContext_relativeResidual H b hb e epsilon hepsilon
  have hp : 0 < (P b hb.le z) ^ 2 :=
    pow_pos (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb.le z) _
  have hAmp := p4Q2PZ37ACQ_originalAmplitudeSq_eq_transfer H b hb.le e z
  have hRes := p4Q2PZ37ACQ_originalResidualEnergy_eq_transfer H b hb.le e z
  have hTransferAmp : 0 < tA2 b hb.le e z := by
    have hA2 : 0 < (A b hb.le e z) ^ 2 := pow_pos hA _
    rw [hAmp] at hA2
    exact (mul_pos_iff_of_pos_left hp).mp hA2
  refine ⟨z, hTransferAmp, ?_⟩
  rw [hAmp, hRes] at hRatio
  have hFact :
      (4 * S b hb.le e) * ((P b hb.le z) ^ 2 * tW b hb.le e z) =
        (P b hb.le z) ^ 2 * ((4 * S b hb.le e) * tW b hb.le e z) := by ring
  have hFact2 :
      (Wbar b hb.le e + epsilon) *
          ((P b hb.le z) ^ 2 * tA2 b hb.le e z) =
        (P b hb.le z) ^ 2 *
          ((Wbar b hb.le e + epsilon) * tA2 b hb.le e z) := by ring
  rw [hFact, hFact2] at hRatio
  by_contra hnot
  have hge : (Wbar b hb.le e + epsilon) * tA2 b hb.le e z ≤
      (4 * S b hb.le e) * tW b hb.le e z := le_of_not_gt hnot
  have hprod := mul_le_mul_of_nonneg_left hge hp.le
  exact (not_le_of_gt hRatio) hprod

/-- If the true weighted transfer-section test is eventually discharged
from the original Perron and two-posterior data, the true original GI
response is nonzero on an OPEN, positive-Haar-mass set. -/
theorem p4Q2PZ37ACQ_weightedTransferThreshold_gives_open_positiveGIRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hThreshold : tau b *
        (∫ z : Pair, (P b hb.le z) ^ 2 * tW b hb.le e z ∂outer) <
      16 * (∫ z : Pair, (P b hb.le z) ^ 2 * tA2 b hb.le e z ∂outer)) :
    ∃ T : Set Pair, IsOpen T ∧
      0 < Measure.real outer T ∧
      ∀ z ∈ T, 0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le f₀ e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion H b hb.le e
    ((p4Q2PZ37ACQ_originalGIBudget_pos_iff_weightedTransfer H b hb e).mpr
      hThreshold)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_originalReceiver_difference_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_originalCoefficient_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_originalAmplitudeSq_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_transferResidualEnergy_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_originalResidualEnergy_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_transferResidualEnergy_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_transferAmplitudeSq_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_weightedTransferAmplitude_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_weightedTransferResidual_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_weightedTransferVariance_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_originalSquaredGIMargin_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_weightedTransferGIMargin_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_originalGIBudget_pos_iff_weightedTransfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_exists_transfer_relativeResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACQ_weightedTransferThreshold_gives_open_positiveGIRegion
