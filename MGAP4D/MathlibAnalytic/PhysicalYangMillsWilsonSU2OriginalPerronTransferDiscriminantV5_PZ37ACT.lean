import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSpectralFractionV5_PZ37ACS

/-!
# P4-Q2-PZ37ACT — original Perron-transfer spectral discriminant

An append-only theorem leaf for the SAME genuine interacting finite-volume
Wilson SU(2) receiver, centered physical source, positive ground-state Perron
representative, updated transfer section, two interacting posteriors, pair-Haar
measure, and original physical boundary/link data.

For the actual P_z>0, updated transfer U_z, genuine four-Haar coefficient
squared sum tA2(z), and true higher-character Haar residual tW(z), define
  d_b(z) = 16*tA2(z) - tau(b)*tW(z),
  D_b    = 16*integral(P_z^2*tA2) - tau(b)*integral(P_z^2*tW).
The original mean GI squared CERTIFICATE (not the signed GI response) obeys
  16*Budget_b = kappa(b)*D_b.
The local certificate obeys
  16*Q_b(z) = kappa(b)*P_z^2*d_b(z).
Both factors kappa and P_z^2 are genuinely strictly positive at b>0.

Thus d_b(z)>0 is precisely local certificate positivity, and global
original eta>tau/(tau+4) is precisely D_b>0. Failure of all local
discriminants rules out the positive MEAN certificate; conversely a
positive mean gives an OPEN, positive-pair-Haar-mass region with d_b(z)>0
and an explicit existing FC mass lower bound.

The local discriminant also equals
  4*(tau+4)*tA2 - tau*Var_Haar(U_z),
so it can be evaluated directly from the four genuine SU(2) Haar
coefficients and variance of the original UPDATED Perron transfer section.

No claim that D_b>0 is true of the original physical Wilson data is made.
No independent Haar receiver, dropped Perron weight, hypothesized residual
dominance, volume-uniform floor, GI-response identity, or continuum mass gap
is introduced.
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
local instance p4Q2PZ37ACT_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACT_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACT_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACT_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACT_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACT_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "tA2" => p4Q2PZ37ACQ_transferAmplitudeSq H
local notation "tW" => p4Q2PZ37ACQ_transferResidualEnergy H
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "Vbar" => p4Q2PZ37ACK_originalReceiverVarianceMoment H
local notation "V" => p4Q2PZ37ACL_originalCenteredReceiverVariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Q" => p4Q2PZ37ACO_originalGISquaredMargin H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "kappa" => p4Q2PZ37ACO_originalGISlopeSq
local notation "rho" => p4Q2PZ37ACI_originalPosteriorResidualEnvelope
local notation "tau" => p4Q2PZ37ACP_originalPosteriorExponentGapSq
local notation "eta" => p4Q2PZ37ACS_originalFirstFourEnergyFraction H
local notation "critical" => p4Q2PZ37ACS_originalPosteriorCriticalEnergyFraction
local notation "localEta" => p4Q2PZ37ACS_originalPointwiseFirstFourFraction H
local instance p4Q2PZ37ACT_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACT_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Local unweighted discriminant, computed from the ACTUAL updated
Perron-transfer section of the unchanged finite Wilson SU(2) receiver. -/
def p4Q2PZ37ACT_originalTransferLocalDiscriminant
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  16 * tA2 b hb e z - tau b * tW b hb e z
local notation "d" => p4Q2PZ37ACT_originalTransferLocalDiscriminant H

/-- The same boundary-data test needs only the four genuine Haar
coefficients and the variance of the updated original transfer section. -/
theorem p4Q2PZ37ACT_localDiscriminant_eq_transferVariance
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    d b hb e z =
      4 * (tau b + 4) * tA2 b hb e z -
        tau b * CompactEnergyMismatchMoment.variance μ
          (U b hb f₀ e z) := by
  unfold p4Q2PZ37ACT_originalTransferLocalDiscriminant
  rw [p4Q2PZ37ACQ_transferResidualEnergy_eq H b hb e z]
  ring

/-- Explicit physical pair-Haar signed discriminator. The ORIGINAL P_z^2
is kept in BOTH integrals and never replaced by an independent law. -/
def p4Q2PZ37ACT_originalWeightedTransferDiscriminant
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  16 * (∫ z : Pair, (P b hb z) ^ 2 * tA2 b hb e z ∂outer) -
    tau b * (∫ z : Pair, (P b hb z) ^ 2 * tW b hb e z ∂outer)
local notation "D" => p4Q2PZ37ACT_originalWeightedTransferDiscriminant H

/-- Physical ACQ evaluation in original S and true higher Haar remainder. -/
theorem p4Q2PZ37ACT_weightedDiscriminant_eq_originalMoments
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    D b hb e = 64 * S b hb e - tau b * Wbar b hb e := by
  unfold p4Q2PZ37ACT_originalWeightedTransferDiscriminant
  rw [p4Q2PZ37ACQ_weightedTransferAmplitude_integral H b hb e,
    p4Q2PZ37ACQ_weightedTransferResidual_integral H b hb e]
  ring


/-- Integral of the ACTUAL local updated-transfer discriminator, weighted
by the ORIGINAL Perron P_z^2, is exactly the global discriminator.
The two integrands are integrable by previously proved continuity of the
unchanged physical receiver's amplitude and higher-mode residual. -/
theorem p4Q2PZ37ACT_weightedDiscriminant_eq_integralLocal
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    D b hb e =
      ∫ z : Pair, (P b hb z) ^ 2 * d b hb e z ∂outer := by
  have hA : Integrable
      (fun z : Pair => (P b hb z) ^ 2 * tA2 b hb e z) outer := by
    have hEq :
        (fun z : Pair => (P b hb z) ^ 2 * tA2 b hb e z) =
          (fun z : Pair => (A b hb e z) ^ 2) := by
      funext z
      exact (p4Q2PZ37ACQ_originalAmplitudeSq_eq_transfer H b hb e z).symm
    rw [hEq]
    exact (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b hb e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hW : Integrable
      (fun z : Pair => (P b hb z) ^ 2 * tW b hb e z) outer := by
    have hEq :
        (fun z : Pair => (P b hb z) ^ 2 * tW b hb e z) =
          (fun z : Pair => W b hb e z) := by
      funext z
      exact (p4Q2PZ37ACQ_originalResidualEnergy_eq_transfer H b hb e z).symm
    rw [hEq]
    exact (p4Q2PZ37ACR_originalResidual_continuous H b hb e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    D b hb e =
        ∫ z : Pair,
          (16 * ((P b hb z) ^ 2 * tA2 b hb e z) -
            tau b * ((P b hb z) ^ 2 * tW b hb e z)) ∂outer := by
      unfold p4Q2PZ37ACT_originalWeightedTransferDiscriminant
      rw [integral_sub (hA.const_mul _) (hW.const_mul _),
        integral_const_mul, integral_const_mul]
    _ = ∫ z : Pair, (P b hb z) ^ 2 * d b hb e z ∂outer := by
      apply integral_congr_ae
      filter_upwards with z
      unfold p4Q2PZ37ACT_originalTransferLocalDiscriminant
      ring

/-- Direct variance-only global test of the true original updated Perron
transfer. Evaluation does not require separately expanding its Haar tail;
the original P_z^2 remains in both outer integrals. -/
theorem p4Q2PZ37ACT_weightedDiscriminant_eq_transferVariance
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    D b hb e =
      4 * (tau b + 4) *
        (∫ z : Pair, (P b hb z) ^ 2 * tA2 b hb e z ∂outer) -
      tau b *
        (∫ z : Pair, (P b hb z) ^ 2 *
          CompactEnergyMismatchMoment.variance μ (U b hb f₀ e z) ∂outer) := by
  have hAllocation := p4Q2PZ37ACK_originalVarianceMoment_eq H b hb e
  calc
    D b hb e = 64 * S b hb e - tau b * Wbar b hb e :=
      p4Q2PZ37ACT_weightedDiscriminant_eq_originalMoments H b hb e
    _ = 4 * (tau b + 4) * (4 * S b hb e) -
        tau b * Vbar b hb e := by
      rw [hAllocation]
      ring
    _ = _ := by
      rw [p4Q2PZ37ACQ_weightedTransferAmplitude_integral H b hb e,
        p4Q2PZ37ACQ_weightedTransferVariance_integral H b hb e]

/-- EXACT global original GI mean squared-certificate, as a signed
Perron-weighted boundary-data discriminator; no threshold is presumed. -/
theorem p4Q2PZ37ACT_originalGIMeanBudget_eq_weightedDiscriminant
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    16 * Budget b hb e = kappa b * D b hb e := by
  calc
    16 * Budget b hb e =
        kappa b * (64 * S b hb e - tau b * Wbar b hb e) :=
      p4Q2PZ37ACP_originalGIMeanBudget_scaled_exponential H b hb e
    _ = kappa b * D b hb e := by
      rw [p4Q2PZ37ACT_weightedDiscriminant_eq_originalMoments]

/-- The directly evaluable signed weighted-transfer test is exactly
equivalent to the still-OPEN original four-mode critical fraction. -/
theorem p4Q2PZ37ACT_weightedDiscriminant_pos_iff_fraction
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < D b hb.le e ↔ critical b < eta b hb.le e := by
  have hk := p4Q2PZ37ACP_originalGISlopeSq_pos b hb
  have hIdentity :=
    p4Q2PZ37ACT_originalGIMeanBudget_eq_weightedDiscriminant H b hb.le e
  constructor
  · intro hD
    have hScaled : 0 < 16 * Budget b hb.le e := by
      rw [hIdentity]
      exact mul_pos hk hD
    have hBudget : 0 < Budget b hb.le e := by
      nlinarith only [hScaled]
    exact (p4Q2PZ37ACS_originalGIMeanBudget_pos_iff_firstFourFraction
      H b hb e).mp hBudget
  · intro hFraction
    have hBudget :=
      (p4Q2PZ37ACS_originalGIMeanBudget_pos_iff_firstFourFraction
        H b hb e).mpr hFraction
    have hScaled : 0 < kappa b * D b hb.le e := by
      rw [← hIdentity]
      nlinarith only [hBudget]
    exact (mul_pos_iff_of_pos_left hk).mp hScaled

/-- The sharp signed obstruction in genuine boundary/Perron-transfer data,
not a statement that the interacting GI response vanishes. -/
theorem p4Q2PZ37ACT_weightedDiscriminant_nonpos_iff_obstruction
    (b : ℝ) (hb : 0 < b) (e : Link) :
    D b hb.le e ≤ 0 ↔ eta b hb.le e ≤ critical b := by
  simpa only [not_lt] using
    not_congr (p4Q2PZ37ACT_weightedDiscriminant_pos_iff_fraction H b hb e)

/-- EXACT same-context certificate identity. Every local sign is decided
by the updated transfer's Haar decomposition; Perron P_z^2 is positive. -/
theorem p4Q2PZ37ACT_localGICertificate_eq_transferDiscriminant
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    16 * Q b hb e z = kappa b * (P b hb z) ^ 2 * d b hb e z := by
  have hCoeff := p4Q2PZ37ACP_originalPosteriorCoefficient_identity b
  calc
    16 * Q b hb e z =
        16 * ((P b hb z) ^ 2 *
          (kappa b * tA2 b hb e z - rho b * tW b hb e z)) := by
      rw [p4Q2PZ37ACQ_originalSquaredGIMargin_eq_transfer H b hb e z]
      rfl
    _ = (P b hb z) ^ 2 *
        (16 * kappa b * tA2 b hb e z -
          (16 * rho b) * tW b hb e z) := by ring
    _ = kappa b * (P b hb z) ^ 2 * d b hb e z := by
      rw [hCoeff]
      unfold p4Q2PZ37ACT_originalTransferLocalDiscriminant
      ring

/-- Strict local GI squared-certificate positivity is equivalent to a
strictly favorable TRUE transfer-spectrum balance at that SAME boundary. -/
theorem p4Q2PZ37ACT_localGICertificate_pos_iff_transfer
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Pair) :
    0 < Q b hb.le e z ↔ 0 < d b hb.le e z := by
  have hk := p4Q2PZ37ACP_originalGISlopeSq_pos b hb
  have hp : 0 < (P b hb.le z) ^ 2 :=
    pow_pos (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb.le z) _
  have hFactor : 0 < kappa b * (P b hb.le z) ^ 2 := mul_pos hk hp
  have hIdentity :=
    p4Q2PZ37ACT_localGICertificate_eq_transferDiscriminant H b hb.le e z
  constructor
  · intro hQ
    have hScaled : 0 < (kappa b * (P b hb.le z) ^ 2) * d b hb.le e z := by
      rw [← hIdentity]
      exact mul_pos (by norm_num) hQ
    exact (mul_pos_iff_of_pos_left hFactor).mp hScaled
  · intro hD
    have hScaled : 0 < 16 * Q b hb.le e z := by
      rw [hIdentity]
      exact mul_pos hFactor hD
    nlinarith only [hScaled]

/-- Sharp nonpositive version, purely a squared GI certificate
obstruction, not a no-go theorem for the signed physical response. -/
theorem p4Q2PZ37ACT_localGICertificate_nonpos_iff_transfer
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Pair) :
    Q b hb.le e z ≤ 0 ↔ d b hb.le e z ≤ 0 := by
  simpa only [not_lt] using
    not_congr (p4Q2PZ37ACT_localGICertificate_pos_iff_transfer H b hb e z)

/-- True unweighted SAME-context transfer fraction; the physical Perron
prefactor cancels locally, but NOT inside the outer boundary integral. -/
def p4Q2PZ37ACT_originalPointwiseTransferFraction
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  (4 * tA2 b hb e z) /
    CompactEnergyMismatchMoment.variance μ (U b hb f₀ e z)
local notation "transferEta" => p4Q2PZ37ACT_originalPointwiseTransferFraction H

/-- The ACS true receiver fraction and ACT true transfer fraction coincide
at the SAME actual boundary when local transfer variance is positive. -/
theorem p4Q2PZ37ACT_originalPointwiseFraction_eq_transfer
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair)
    (hV : 0 < CompactEnergyMismatchMoment.variance μ (U b hb f₀ e z)) :
    localEta b hb e z = transferEta b hb e z := by
  have hp : 0 < (P b hb z) ^ 2 :=
    pow_pos (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb z) _
  unfold p4Q2PZ37ACS_originalPointwiseFirstFourFraction
    p4Q2PZ37ACT_originalPointwiseTransferFraction
  rw [p4Q2PZ37ACQ_originalAmplitudeSq_eq_transfer H b hb e z,
    p4Q2PZ37ACA_originalReceiver_variance_eq_transfer H b hb f₀ e z]
  field_simp [ne_of_gt hp, ne_of_gt hV]
  ring

/-- Pointwise direct SU(2) transfer-variance computation of the same sharp
posterior criterion, with no assumption of a receiver variance floor. -/
theorem p4Q2PZ37ACT_transferPointwiseFraction_threshold_iff
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Pair)
    (hV : 0 < CompactEnergyMismatchMoment.variance μ
      (U b hb.le f₀ e z)) :
    critical b < transferEta b hb.le e z ↔ 0 < d b hb.le e z := by
  have hp : 0 < (P b hb.le z) ^ 2 :=
    pow_pos (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb.le z) _
  have hReceiverV : 0 < V b hb.le e z := by
    change 0 < CompactEnergyMismatchMoment.variance μ
      (p4Q2PZ37ABZ_originalReceiverSection H b hb.le f₀ e z)
    rw [p4Q2PZ37ACA_originalReceiver_variance_eq_transfer H b hb.le f₀ e z]
    exact mul_pos hp hV
  calc
    critical b < transferEta b hb.le e z ↔
        critical b < localEta b hb.le e z := by
      rw [p4Q2PZ37ACT_originalPointwiseFraction_eq_transfer H b hb.le e z hV]
    _ ↔ 0 < Q b hb.le e z :=
      (p4Q2PZ37ACS_originalPointwiseGI_pos_iff_localFraction
        H b hb e z hReceiverV).symm
    _ ↔ 0 < d b hb.le e z :=
      p4Q2PZ37ACT_localGICertificate_pos_iff_transfer H b hb e z

/-- If ALL true updated-transfer contexts fail the local posterior
discriminant test, the physical mean four-mode fraction cannot pass the
critical threshold. This is a precise sufficient obstruction only. -/
theorem p4Q2PZ37ACT_allLocalTransferObstructions_block_mean
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hAll : ∀ z : Pair, d b hb.le e z ≤ 0) :
    eta b hb.le e ≤ critical b := by
  have hQ (z : Pair) : Q b hb.le e z ≤ 0 :=
    (p4Q2PZ37ACT_localGICertificate_nonpos_iff_transfer H b hb e z).mpr
      (hAll z)
  have hIntegral : (∫ z : Pair, Q b hb.le e z ∂outer) ≤ 0 :=
    integral_nonpos hQ
  rw [p4Q2PZ37ACO_originalGIMeanBudget_integral] at hIntegral
  exact (p4Q2PZ37ACS_originalGIMeanBudget_nonpos_iff_fractionObstruction
    H b hb e).mp hIntegral

/-- A POSITIVE true original physical mean fraction necessarily entails
at least one boundary with strict original updated-transfer dominance. -/
theorem p4Q2PZ37ACT_positiveFraction_has_localTransferWitness
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hFraction : critical b < eta b hb.le e) :
    ∃ z : Pair, 0 < d b hb.le e z := by
  by_contra hNo
  have hAll (z : Pair) : d b hb.le e z ≤ 0 := by
    by_contra hPos
    exact hNo ⟨z, lt_of_not_ge hPos⟩
  exact (not_le_of_gt hFraction)
    (p4Q2PZ37ACT_allLocalTransferObstructions_block_mean H b hb e hAll)

/-- Stronger exact physical conditional result. If the original
four-mode mean fraction beats the posterior threshold, an OPEN set of
TRUE P_z-normalized transfer contexts has d_b(z)>0, with the established
positive quantitative FC-pair-Haar mass lower bound. -/
theorem p4Q2PZ37ACT_positiveFraction_forces_openTransferRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hFraction : critical b < eta b hb.le e) :
    ∃ T : Set Pair, IsOpen T ∧
      0 < 2 * (kappa b * ((B b hb.le) ^ 2 / 4)) -
        Budget b hb.le e ∧
      Budget b hb.le e /
        (2 * (kappa b * ((B b hb.le) ^ 2 / 4)) -
          Budget b hb.le e) ≤ Measure.real outer T ∧
      0 < Measure.real outer T ∧
      ∀ z ∈ T, 0 < d b hb.le e z := by
  have hBudget :=
    (p4Q2PZ37ACS_originalGIMeanBudget_pos_iff_firstFourFraction
      H b hb e).mpr hFraction
  have ht :=
    p4Q2PZ37ACO_originalGIBudget_tail H b hb.le e hBudget
  let T : Set Pair := {z | Budget b hb.le e / 2 < Q b hb.le e z}
  have hOpen : IsOpen T :=
    isOpen_lt continuous_const
      (p4Q2PZ37ACO_originalGISquaredMargin_continuous H b hb.le e)
  have hMass : 0 < Measure.real outer T :=
    (div_pos hBudget ht.1).trans_le ht.2
  refine ⟨T, hOpen, ht.1, ht.2, hMass, ?_⟩
  intro z hz
  change Budget b hb.le e / 2 < Q b hb.le e z at hz
  have hQ : 0 < Q b hb.le e z := (half_pos hBudget).trans hz
  exact (p4Q2PZ37ACT_localGICertificate_pos_iff_transfer H b hb e z).mp hQ

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_localDiscriminant_eq_transferVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_weightedDiscriminant_eq_originalMoments
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_weightedDiscriminant_eq_integralLocal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_weightedDiscriminant_eq_transferVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_originalGIMeanBudget_eq_weightedDiscriminant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_weightedDiscriminant_pos_iff_fraction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_weightedDiscriminant_nonpos_iff_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_localGICertificate_eq_transferDiscriminant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_localGICertificate_pos_iff_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_localGICertificate_nonpos_iff_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_originalPointwiseFraction_eq_transfer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_transferPointwiseFraction_threshold_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_allLocalTransferObstructions_block_mean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_positiveFraction_has_localTransferWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACT_positiveFraction_forces_openTransferRegion
