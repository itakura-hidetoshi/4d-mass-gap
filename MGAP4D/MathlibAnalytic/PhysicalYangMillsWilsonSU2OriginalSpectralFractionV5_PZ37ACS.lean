import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHigherModeHaarTailV5_PZ37ACR

/-!
# P4-Q2-PZ37ACS — exact original Perron-weighted four-mode spectral fraction

This is the SAME interacting Wilson SU(2) model with the unchanged
centered Gauss-law physical source, FF receiver, positive Perron
representative, transfer norm, two actual interacting posterior laws,
original boundary configurations and original pair-Haar measure.

For fixed H, b>0 and true spatial link e, let
  S     = E_outer[original covariance^2] > 0,
  Vbar  = E_outer[Var_Haar(F_z)] = 16*S + Wbar > 0,
  Wbar  = E_outer[actual higher four-mode remainder] >= 0.
Define the ORIGINAL physical first-four Haar energy fraction
  eta = 16*S/Vbar
      = 4*E_outer[P_z^2 * sum_j u_j(z)^2] /
            E_outer[P_z^2 * Var_Haar(U_z)]
and the complementary higher-mode fraction omega=Wbar/Vbar.
Here P_z and U_z are the exact updated Perron-normalized transfer
factors from ABZ/ACQ; NO outer Perron weight is dropped.
The exact partition is eta+omega=1, 0<eta<=1, 0<=omega<1.

ACI/ACP give tau(b)=(exp(64*b)-1)^2>0 and the sharp criterion
  M_GI>0  iff  eta > tau/(tau+4)
          iff omega < 4/(tau+4).
The threshold lies strictly between zero and one, but there is NO
proof that the original physical eta is above it. More strongly the
normalized signed distance to this critical fraction is an exact,
not merely qualitative, original GI mean certificate identity.

The SAME original local squared GI margin has the sharp pointwise
variance/form-mode comparison (without any assumed local variance
floor). Whenever the actual receiver variance at a context is positive,
its local first-four energy fraction is within [0,1] and its strict
comparison with tau/(tau+4) is equivalent to the positive original
ACM squared GI certificate margin at that context. This is a
certificate and NOT an identity for the actual signed GI response.

No new physical assumptions, alternative receiver, independent Haar
law, H-uniform estimate, H1-H4, OS/Wightman reconstruction, or
continuum Yang-Mills mass gap are asserted.
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
local instance p4Q2PZ37ACS_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACS_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACS_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACS_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACS_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACS_probability : IsProbabilityMeasure (normalizedCompactHaar G) :=
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
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H
local notation "V" => p4Q2PZ37ACL_originalCenteredReceiverVariance H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "Vbar" => p4Q2PZ37ACK_originalReceiverVarianceMoment H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "Q" => p4Q2PZ37ACO_originalGISquaredMargin H
local notation "kappa" => p4Q2PZ37ACO_originalGISlopeSq
local notation "tau" => p4Q2PZ37ACP_originalPosteriorExponentGapSq
local notation "tA2" => p4Q2PZ37ACQ_transferAmplitudeSq H
local notation "tW" => p4Q2PZ37ACQ_transferResidualEnergy H
local instance p4Q2PZ37ACS_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACS_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Dimensionless fraction of ACTUAL original receiver variance captured
by the four genuine SU(2) fundamental Haar modes. -/
def p4Q2PZ37ACS_originalFirstFourEnergyFraction
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  (16 * S b hb e) / Vbar b hb e
local notation "eta" => p4Q2PZ37ACS_originalFirstFourEnergyFraction H

/-- The complementary higher-mode fraction of exactly the same original
Wilson receiver and original pair-Haar law. -/
def p4Q2PZ37ACS_originalHigherModeEnergyFraction
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  Wbar b hb e / Vbar b hb e
local notation "omega" => p4Q2PZ37ACS_originalHigherModeEnergyFraction H

/-- The exact dimensionless ACI/ACP two-interacting-posterior threshold. -/
def p4Q2PZ37ACS_originalPosteriorCriticalEnergyFraction (b : ℝ) : ℝ :=
  tau b / (tau b + 4)
local notation "critical" => p4Q2PZ37ACS_originalPosteriorCriticalEnergyFraction

/-- First-four local fraction. It is only used with an independently
verified positive ORIGINAL receiver variance at this context. -/
def p4Q2PZ37ACS_originalPointwiseFirstFourFraction
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  (4 * (A b hb e z) ^ 2) / V b hb e z
local notation "localEta" => p4Q2PZ37ACS_originalPointwiseFirstFourFraction H

/-- The actual finite-volume original receiver variance mean is positive
at every b>0, without introducing a numerical or uniform lower floor. -/
theorem p4Q2PZ37ACS_originalMeanReceiverVariance_pos
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < Vbar b hb.le e := by
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hw := p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b hb.le e
  rw [p4Q2PZ37ACK_originalVarianceMoment_eq H b hb.le e]
  linarith

/-- No more than the whole true receiver energy can be in the first four
SU(2) modes, and at positive coupling the fraction is strictly nonzero. -/
theorem p4Q2PZ37ACS_originalFirstFourFraction_pos_le_one
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < eta b hb.le e ∧ eta b hb.le e ≤ 1 := by
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hw := p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b hb.le e
  have hv := p4Q2PZ37ACS_originalMeanReceiverVariance_pos H b hb e
  have hAllocation := p4Q2PZ37ACK_originalVarianceMoment_eq H b hb.le e
  unfold p4Q2PZ37ACS_originalFirstFourEnergyFraction
  constructor
  · exact div_pos (mul_pos (by norm_num) hs) hv
  · apply (div_le_iff₀ hv).mpr
    nlinarith only [hAllocation, hw]

/-- The higher-character residual energy fraction is nonnegative and
strictly below the entire physical receiver variance at every b>0. -/
theorem p4Q2PZ37ACS_originalHigherModeFraction_nonneg_lt_one
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 ≤ omega b hb.le e ∧ omega b hb.le e < 1 := by
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hw := p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b hb.le e
  have hv := p4Q2PZ37ACS_originalMeanReceiverVariance_pos H b hb e
  have hAllocation := p4Q2PZ37ACK_originalVarianceMoment_eq H b hb.le e
  unfold p4Q2PZ37ACS_originalHigherModeEnergyFraction
  constructor
  · exact div_nonneg hw hv.le
  · apply (div_lt_iff₀ hv).mpr
    nlinarith only [hAllocation, hs]

/-- Exact original Pythagorean energy partition at the OUTER Haar mean. -/
theorem p4Q2PZ37ACS_originalEnergyFraction_partition
    (b : ℝ) (hb : 0 < b) (e : Link) :
    eta b hb.le e + omega b hb.le e = 1 := by
  have hv := p4Q2PZ37ACS_originalMeanReceiverVariance_pos H b hb e
  have hAllocation := p4Q2PZ37ACK_originalVarianceMoment_eq H b hb.le e
  unfold p4Q2PZ37ACS_originalFirstFourEnergyFraction
    p4Q2PZ37ACS_originalHigherModeEnergyFraction
  calc
    (16 * S b hb.le e) / Vbar b hb.le e +
        Wbar b hb.le e / Vbar b hb.le e =
      (16 * S b hb.le e + Wbar b hb.le e) / Vbar b hb.le e := by rw [add_div]
    _ = Vbar b hb.le e / Vbar b hb.le e := by rw [← hAllocation]
    _ = 1 := div_self (ne_of_gt hv)

/-- The exact genuine original transfer/Perron weighted first-four mode
fraction. Neither P_z^2 nor the updated denominator in U_z is dropped. -/
theorem p4Q2PZ37ACS_originalFirstFourFraction_eq_weightedTransfer
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    eta b hb e =
      (4 * (∫ z : Pair, (P b hb z) ^ 2 * tA2 b hb e z ∂outer)) /
      (∫ z : Pair, (P b hb z) ^ 2 *
        CompactEnergyMismatchMoment.variance μ (U b hb f₀ e z) ∂outer) := by
  unfold p4Q2PZ37ACS_originalFirstFourEnergyFraction
  rw [p4Q2PZ37ACQ_weightedTransferAmplitude_integral H b hb e,
    p4Q2PZ37ACQ_weightedTransferVariance_integral H b hb e]
  ring

/-- The complementary high-mode fraction likewise retains every original
pair-Haar Perron weight, not an independent-Haar substitute. -/
theorem p4Q2PZ37ACS_originalHigherModeFraction_eq_weightedTransfer
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    omega b hb e =
      (∫ z : Pair, (P b hb z) ^ 2 * tW b hb e z ∂outer) /
      (∫ z : Pair, (P b hb z) ^ 2 *
        CompactEnergyMismatchMoment.variance μ (U b hb f₀ e z) ∂outer) := by
  unfold p4Q2PZ37ACS_originalHigherModeEnergyFraction
  rw [p4Q2PZ37ACQ_weightedTransferResidual_integral H b hb e,
    p4Q2PZ37ACQ_weightedTransferVariance_integral H b hb e]

/-- The actual two-posterior critical first-four fraction lies strictly
between zero and one whenever b>0. -/
theorem p4Q2PZ37ACS_originalCriticalFraction_pos_lt_one
    (b : ℝ) (hb : 0 < b) :
    0 < critical b ∧ critical b < 1 := by
  have ht := p4Q2PZ37ACP_originalPosteriorExponentGapSq_pos b hb
  have hd : 0 < tau b + 4 := by linarith
  unfold p4Q2PZ37ACS_originalPosteriorCriticalEnergyFraction
  constructor
  · exact div_pos ht hd
  · apply (div_lt_iff₀ hd).mpr
    linarith

/-- EXACT necessary-and-sufficient original physical spectral-fraction
threshold for the ACO POSITIVE MEAN sufficient GI certificate.
The inequality is not asserted to hold in the actual Wilson model. -/
theorem p4Q2PZ37ACS_originalGIMeanBudget_pos_iff_firstFourFraction
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < Budget b hb.le e ↔
      critical b < eta b hb.le e := by
  have hv := p4Q2PZ37ACS_originalMeanReceiverVariance_pos H b hb e
  have hd : 0 < tau b + 4 := by
    have ht := p4Q2PZ37ACP_originalPosteriorExponentGapSq_pos b hb
    linarith
  rw [p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_variance H b hb e]
  unfold p4Q2PZ37ACS_originalPosteriorCriticalEnergyFraction
    p4Q2PZ37ACS_originalFirstFourEnergyFraction
  rw [div_lt_div_iff₀ hd hv]
  constructor <;> intro h <;> nlinarith only [h]

/-- A NONPOSITIVE MEAN CERTIFICATE is exactly a genuine original first-four
spectral fraction at or BELOW the posterior threshold; not GI vanishing. -/
theorem p4Q2PZ37ACS_originalGIMeanBudget_nonpos_iff_fractionObstruction
    (b : ℝ) (hb : 0 < b) (e : Link) :
    Budget b hb.le e ≤ 0 ↔
      eta b hb.le e ≤ critical b := by
  simpa only [not_lt] using
    not_congr (p4Q2PZ37ACS_originalGIMeanBudget_pos_iff_firstFourFraction H b hb e)

/-- The same exact positive-mean criterion as a STRICT UPPER bound on
the fraction occupied by genuine higher SU(2) Haar modes. -/
theorem p4Q2PZ37ACS_originalGIMeanBudget_pos_iff_higherModeFraction
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < Budget b hb.le e ↔
      omega b hb.le e < 4 / (tau b + 4) := by
  have hd : 0 < tau b + 4 := by
    have ht := p4Q2PZ37ACP_originalPosteriorExponentGapSq_pos b hb
    linarith
  have hParts := p4Q2PZ37ACS_originalEnergyFraction_partition H b hb e
  have hCritical : critical b + 4 / (tau b + 4) = 1 := by
    unfold p4Q2PZ37ACS_originalPosteriorCriticalEnergyFraction
    calc
      tau b / (tau b + 4) + 4 / (tau b + 4) =
          (tau b + 4) / (tau b + 4) := by rw [add_div]
      _ = 1 := div_self (ne_of_gt hd)
  rw [p4Q2PZ37ACS_originalGIMeanBudget_pos_iff_firstFourFraction H b hb e]
  constructor <;> intro h <;> linarith only [hParts, hCritical, h]

/-- The exact signed average GI certificate can be expressed as a
normalized ORIGINAL spectral-fraction excess, not only as a sign test. -/
theorem p4Q2PZ37ACS_originalGIMeanBudget_normalizedIdentity
    (b : ℝ) (hb : 0 < b) (e : Link) :
    16 * Budget b hb.le e =
      kappa b * (tau b + 4) * Vbar b hb.le e *
        (eta b hb.le e - critical b) := by
  have hv := p4Q2PZ37ACS_originalMeanReceiverVariance_pos H b hb e
  have hd : 0 < tau b + 4 := by
    have ht := p4Q2PZ37ACP_originalPosteriorExponentGapSq_pos b hb
    linarith
  have hAllocation := p4Q2PZ37ACK_originalVarianceMoment_eq H b hb.le e
  calc
    16 * Budget b hb.le e =
        kappa b * (64 * S b hb.le e - tau b * Wbar b hb.le e) :=
      p4Q2PZ37ACP_originalGIMeanBudget_scaled_exponential H b hb.le e
    _ = kappa b *
        ((tau b + 4) * (16 * S b hb.le e) -
          tau b * Vbar b hb.le e) := by
      rw [hAllocation]
      ring
    _ = kappa b * (tau b + 4) * Vbar b hb.le e *
          (eta b hb.le e - critical b) := by
      unfold p4Q2PZ37ACS_originalFirstFourEnergyFraction
        p4Q2PZ37ACS_originalPosteriorCriticalEnergyFraction
      field_simp [ne_of_gt hv, ne_of_gt hd]

/-- The exact genuine original GI squared orbit margin satisfies a
pointwise spectral identity. It is a CERTIFICATE, not the GI gap itself. -/
theorem p4Q2PZ37ACS_originalPointwiseGISquaredMargin_spectralIdentity
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    16 * Q b hb e z =
      kappa b * ((tau b + 4) * (4 * (A b hb e z) ^ 2) -
        tau b * V b hb e z) := by
  have hAllocation := p4Q2PZ37ACM_originalVariance_eq_amplitude_residual
    H b hb e z
  have hW : W b hb e z = V b hb e z - 4 * (A b hb e z) ^ 2 := by
    linarith
  have hCoeff := p4Q2PZ37ACP_originalPosteriorCoefficient_identity b
  unfold p4Q2PZ37ACO_originalGISquaredMargin
  rw [hW]
  calc
    16 * (kappa b * (A b hb e z) ^ 2 -
      p4Q2PZ37ACI_originalPosteriorResidualEnvelope b *
        (V b hb e z - 4 * (A b hb e z) ^ 2)) =
      16 * kappa b * (A b hb e z) ^ 2 -
      (16 * p4Q2PZ37ACI_originalPosteriorResidualEnvelope b) *
        (V b hb e z - 4 * (A b hb e z) ^ 2) := by ring
    _ = 16 * kappa b * (A b hb e z) ^ 2 -
        (kappa b * tau b) * (V b hb e z - 4 * (A b hb e z) ^ 2) := by
      rw [hCoeff]
    _ = kappa b * ((tau b + 4) * (4 * (A b hb e z) ^ 2) -
        tau b * V b hb e z) := by ring

/-- At each actual boundary with positive physical receiver variance,
its local four-mode fraction is an honest number between 0 and 1. -/
theorem p4Q2PZ37ACS_originalPointwiseFraction_bounds
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair)
    (hV : 0 < V b hb e z) :
    0 ≤ localEta b hb e z ∧ localEta b hb e z ≤ 1 := by
  have hAllocation := p4Q2PZ37ACM_originalVariance_eq_amplitude_residual
    H b hb e z
  have hW := p4Q2PZ37ACK_originalFourModeResidualEnergy_nonneg H b hb e z
  have hA : 0 ≤ 4 * (A b hb e z) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  unfold p4Q2PZ37ACS_originalPointwiseFirstFourFraction
  constructor
  · exact div_nonneg hA hV.le
  · apply (div_le_iff₀ hV).mpr
    nlinarith only [hAllocation, hW]

/-- Exact original same-context criterion: the squared ACM GI certificate
is positive precisely when the local physical first-four spectral fraction
exceeds the SAME original posterior threshold (if actual variance>0). -/
theorem p4Q2PZ37ACS_originalPointwiseGI_pos_iff_localFraction
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Pair)
    (hV : 0 < V b hb.le e z) :
    0 < Q b hb.le e z ↔
      critical b < localEta b hb.le e z := by
  have hk := p4Q2PZ37ACP_originalGISlopeSq_pos b hb
  have hd : 0 < tau b + 4 := by
    have ht := p4Q2PZ37ACP_originalPosteriorExponentGapSq_pos b hb
    linarith
  have hScaled := p4Q2PZ37ACS_originalPointwiseGISquaredMargin_spectralIdentity
    H b hb.le e z
  constructor
  · intro hQ
    have hp : 0 < kappa b *
        ((tau b + 4) * (4 * (A b hb.le e z) ^ 2) -
          tau b * V b hb.le e z) := by
      rw [← hScaled]
      exact mul_pos (by norm_num) hQ
    have hRaw : tau b * V b hb.le e z <
        (tau b + 4) * (4 * (A b hb.le e z) ^ 2) :=
      sub_pos.mp ((mul_pos_iff_of_pos_left hk).mp hp)
    change tau b / (tau b + 4) <
      (4 * (A b hb.le e z) ^ 2) / V b hb.le e z
    exact (div_lt_div_iff₀ hd hV).mpr (by nlinarith only [hRaw])
  · intro h
    change tau b / (tau b + 4) <
      (4 * (A b hb.le e z) ^ 2) / V b hb.le e z at h
    have hRaw : tau b * V b hb.le e z <
        (tau b + 4) * (4 * (A b hb.le e z) ^ 2) := by
      have ht := (div_lt_div_iff₀ hd hV).mp h
      nlinarith only [ht]
    have hp : 0 < 16 * Q b hb.le e z := by
      rw [hScaled]
      exact mul_pos hk (sub_pos.mpr hRaw)
    nlinarith only [hp]

/-- Crossing the still-open ORIGINAL mean fraction threshold really
supplies a positive original GI response on an OPEN positive-Haar mass
region by the previously kernel-checked ACO theorem. -/
theorem p4Q2PZ37ACS_firstFourFraction_gives_open_positiveGIRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hFraction : critical b < eta b hb.le e) :
    ∃ T : Set Pair, IsOpen T ∧
      0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le f₀ e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion H b hb.le e
    ((p4Q2PZ37ACS_originalGIMeanBudget_pos_iff_firstFourFraction H b hb e).mpr
      hFraction)

/-- If the true original fraction fails the mean-certificate threshold,
ACR forces a genuine updated-link/Perron high-mode witness. This does
NOT imply the actual two-posterior GI gap vanishes. -/
theorem p4Q2PZ37ACS_fractionObstruction_has_originalHighModeWitness
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hFraction : eta b hb.le e ≤ critical b) :
    ∃ z : Pair, ∃ g : G,
      CompactFiniteHaarProjection.remainder μ
        (U b hb.le f₀ e z) p4Q2PZ37ACK_fourModeCharacter g ≠ 0 := by
  exact p4Q2PZ37ACR_nonpositiveBudget_has_higherModeWitness H b hb e
    ((p4Q2PZ37ACS_originalGIMeanBudget_nonpos_iff_fractionObstruction
      H b hb e).mpr hFraction)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalMeanReceiverVariance_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalFirstFourFraction_pos_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalHigherModeFraction_nonneg_lt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalEnergyFraction_partition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalFirstFourFraction_eq_weightedTransfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalHigherModeFraction_eq_weightedTransfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalCriticalFraction_pos_lt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalGIMeanBudget_pos_iff_firstFourFraction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalGIMeanBudget_nonpos_iff_fractionObstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalGIMeanBudget_pos_iff_higherModeFraction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalGIMeanBudget_normalizedIdentity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalPointwiseGISquaredMargin_spectralIdentity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalPointwiseFraction_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_originalPointwiseGI_pos_iff_localFraction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_firstFourFraction_gives_open_positiveGIRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACS_fractionObstruction_has_originalHighModeWitness
