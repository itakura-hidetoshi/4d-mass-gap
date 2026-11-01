import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferSectionFourModeV5_PZ37ACQ

/-!
# P4-Q2-PZ37ACR — genuine higher-mode Haar obstruction and open regions

Keep the original interacting Wilson SU(2) receiver F, centered Gauss-law
physical source f0, positive Perron representative and transfer norm,
actual two interacting posteriors, original boundary pair z and original
outer pair-Haar measure. No surrogate receiver or independent Haar law.

ACQ identifies the actual orthogonal higher-character residual
W_F(z) = P_z^2 W_U(z), where P_z>0 and U_z is the exact original transfer
section with the UPDATED joint Perron half-density. ACP gives, for b>0,
  Budget<=0 iff 64*S <= (exp(64*b)-1)^2 * Wbar.
Since S>0 and the exponential gap is positive, failure of the
POSITIVE-MEAN sufficient certificate forces Wbar>0. Actual continuity,
the original FC upper bound W_F(z)<=B^2, and the generic compact positive
mean tail bound force an OPEN original pair-Haar event of explicit
positive probability where the *genuine transfer* higher-mode remainder
has positive squared Haar norm. Such an event is an obstruction witness
to mean-certificate positivity, NOT a no-go for the actual GI response.

Independently of any GI-positivity premise, ACO's mean-adjusted relaxed
residual inequality transfers to the same genuine U_z with P_z^2 exactly
canceled POINTWISE, giving a quantitative open positive-Haar-mass set
where A_U^2>0 and 4*S*W_U < (Wbar+epsilon)*A_U^2.

In particular there is no assumed strict upper bound on Wbar/S, no
uniform control in H, no common support cylinder, no changed endpoint,
no H1-H4 or Wightman/OS reconstruction and no continuum mass-gap claim.
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
local instance p4Q2PZ37ACR_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACR_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACR_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACR_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACR_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACR_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local notation "V" => p4Q2PZ37ACL_originalCenteredReceiverVariance H
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "kappa" => p4Q2PZ37ACO_originalGISlopeSq
local notation "tau" => p4Q2PZ37ACP_originalPosteriorExponentGapSq
local notation "tW" => p4Q2PZ37ACQ_transferResidualEnergy H
local notation "tA2" => p4Q2PZ37ACQ_transferAmplitudeSq H
local instance p4Q2PZ37ACR_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACR_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The actual, not hypothesized, original four-mode residual is continuous
in both original boundary configurations. -/
theorem p4Q2PZ37ACR_originalResidual_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Continuous (W b hb e) := by
  have heq : (fun z : Pair => W b hb e z) =
      (fun z : Pair => V b hb e z - 4 * (A b hb e z) ^ 2) := by
    funext z
    have h := p4Q2PZ37ACM_originalVariance_eq_amplitude_residual H b hb e z
    linarith
  rw [show W b hb e = (fun z : Pair => W b hb e z) from rfl, heq]
  exact (p4Q2PZ37ACD_originalReceiver_variance_continuous H b hb f₀ e).sub
    (continuous_const.mul (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b hb e))

/-- Full higher-mode energy is bounded by the ORIGINAL physical receiver's
FC variance cap, without any favorable GI or receiver regression premise. -/
theorem p4Q2PZ37ACR_originalResidual_le_FC
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    W b hb e z ≤ (B b hb) ^ 2 := by
  have hv := p4Q2PZ37ACA_originalReceiver_variance_le_FC H b hb f₀ e z
  change V b hb e z ≤ (B b hb) ^ 2 at hv
  have hdec := p4Q2PZ37ACM_originalVariance_eq_amplitude_residual H b hb e z
  have hnonneg : 0 ≤ 4 * (A b hb e z) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  linarith

/-- A sharp finite-volume original-Haar upper-tail estimate for the actual
orthogonal receiver remainder. This requires only its ACTUAL positive mean. -/
theorem p4Q2PZ37ACR_originalResidual_halfMean_tail
    (b : ℝ) (hb : 0 ≤ b) (e : Link)
    (hMean : 0 < Wbar b hb e) :
    0 < 2 * (B b hb) ^ 2 - Wbar b hb e ∧
      Wbar b hb e / (2 * (B b hb) ^ 2 - Wbar b hb e) ≤
        Measure.real outer {z : Pair | Wbar b hb e / 2 < W b hb e z} := by
  have hIntegral : 0 < ∫ z : Pair, W b hb e z ∂outer := hMean
  have ht := CompactPositiveMomentTail.half_mean_upper_tail outer
    (W b hb e) (p4Q2PZ37ACR_originalResidual_continuous H b hb e)
    ((B b hb) ^ 2) (p4Q2PZ37ACR_originalResidual_le_FC H b hb e)
    hIntegral
  simpa only [p4Q2PZ37ACK_originalFourModeResidualMoment] using ht

/-- An actual NONPOSITIVE GI mean certificate forces strictly positive
higher-mode energy in the same original interacting-Wilson receiver. -/
theorem p4Q2PZ37ACR_nonpositiveBudget_forces_positiveResidualMean
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpos : Budget b hb.le e ≤ 0) :
    0 < Wbar b hb.le e := by
  have ht := p4Q2PZ37ACP_originalPosteriorExponentGapSq_pos b hb
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hObstruction :=
    (p4Q2PZ37ACP_originalGIMeanBudget_nonpos_iff_exponential_obstruction
      H b hb e).mp hNonpos
  have hProduct : 0 < tau b * Wbar b hb.le e :=
    (mul_pos (by norm_num) hs).trans_le hObstruction
  exact (mul_pos_iff_of_pos_left ht).mp hProduct

/-- The residual mean is not merely positive: the genuine posterior
exponential gap yields an exact lower bound on the ORIGINAL high-mode energy. -/
theorem p4Q2PZ37ACR_nonpositiveBudget_residualMoment_lower
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpos : Budget b hb.le e ≤ 0) :
    0 < 64 * S b hb.le e / tau b ∧
      64 * S b hb.le e / tau b ≤ Wbar b hb.le e := by
  have ht := p4Q2PZ37ACP_originalPosteriorExponentGapSq_pos b hb
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hObstruction :=
    (p4Q2PZ37ACP_originalGIMeanBudget_nonpos_iff_exponential_obstruction
      H b hb e).mp hNonpos
  refine ⟨div_pos (mul_pos (by norm_num) hs) ht, ?_⟩
  exact (div_le_iff₀ ht).mpr (by simpa only [mul_comm] using hObstruction)

/-- Quantitative physical obstruction: if the actual positive-mean GI
certificate fails, an OPEN original pair-Haar region has explicit
positive measured mass and strictly nonzero higher-mode energy in the
SAME genuine Perron-normalized transfer section U_z. No claim of GI
vanishing follows from the obstruction. -/
theorem p4Q2PZ37ACR_nonpositiveBudget_forces_openHigherModeRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpos : Budget b hb.le e ≤ 0) :
    ∃ T : Set Pair, IsOpen T ∧
      0 < 2 * (B b hb.le) ^ 2 - Wbar b hb.le e ∧
      Wbar b hb.le e / (2 * (B b hb.le) ^ 2 - Wbar b hb.le e) ≤
        Measure.real outer T ∧
      0 < Measure.real outer T ∧
      ∀ z ∈ T, 0 < tW b hb.le e z := by
  have hw := p4Q2PZ37ACR_nonpositiveBudget_forces_positiveResidualMean
    H b hb e hNonpos
  have ht := p4Q2PZ37ACR_originalResidual_halfMean_tail H b hb.le e hw
  let T : Set Pair := {z | Wbar b hb.le e / 2 < W b hb.le e z}
  have hOpen : IsOpen T :=
    isOpen_lt continuous_const (p4Q2PZ37ACR_originalResidual_continuous H b hb.le e)
  have hMass : 0 < Measure.real outer T :=
    (div_pos hw ht.1).trans_le ht.2
  refine ⟨T, hOpen, ht.1, ht.2, hMass, ?_⟩
  intro z hz
  change Wbar b hb.le e / 2 < W b hb.le e z at hz
  have hTrue : 0 < W b hb.le e z := (half_pos hw).trans hz
  rw [p4Q2PZ37ACQ_originalResidualEnergy_eq_transfer H b hb.le e z] at hTrue
  have hp : 0 < (P b hb.le z) ^ 2 :=
    pow_pos (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb.le z) _
  exact (mul_pos_iff_of_pos_left hp).mp hTrue

/-- A positive actual squared Haar residual has a genuine SU(2) link
configuration where the ORIGINAL updated Perron transfer is not equal to
its constant-plus-four-character projection. -/
theorem p4Q2PZ37ACR_positiveTransferResidual_has_higherModeWitness
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair)
    (hResidual : 0 < tW b hb e z) :
    ∃ g : G, CompactFiniteHaarProjection.remainder μ
      (U b hb f₀ e z) φ g ≠ 0 := by
  by_contra hn
  have hZero (g : G) :
      CompactFiniteHaarProjection.remainder μ (U b hb f₀ e z) φ g = 0 := by
    by_contra hne
    exact hn ⟨g, hne⟩
  have hIntegralZero : tW b hb e z = 0 := by
    unfold p4Q2PZ37ACQ_transferResidualEnergy
    simp [hZero]
  exact (ne_of_gt hResidual) hIntegralZero

/-- Every obstruction to positivity of the mean certificate forces at
least one REAL updated link and boundary where the true transfer section
has a nonzero higher-character component. -/
theorem p4Q2PZ37ACR_nonpositiveBudget_has_higherModeWitness
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpos : Budget b hb.le e ≤ 0) :
    ∃ z : Pair, ∃ g : G,
      CompactFiniteHaarProjection.remainder μ
        (U b hb.le f₀ e z) φ g ≠ 0 := by
  obtain ⟨T, _hOpen, _hDen, _hFloor, hMass, hOnT⟩ :=
    p4Q2PZ37ACR_nonpositiveBudget_forces_openHigherModeRegion H b hb e hNonpos
  have hNonempty : T.Nonempty := by
    by_contra hn
    have hempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [hempty] at hMass
  obtain ⟨z, hz⟩ := hNonempty
  exact ⟨z, p4Q2PZ37ACR_positiveTransferResidual_has_higherModeWitness
    H b hb.le e z (hOnT z hz)⟩

/-- Separate unconditional positive-mass theorem: for any epsilon>0 the
original adjusted-margin set gives an OPEN quantified region where the
genuine Perron-normalized transfer amplitude is nonzero and its local
higher-character residual meets the relaxed relative comparison.
No positive actual GI certificate is presumed. -/
theorem p4Q2PZ37ACR_relaxedTransferRegion_open_mass_lower
    (b : ℝ) (hb : 0 < b) (e : Link)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ T : Set Pair, IsOpen T ∧
      0 < 2 * (Wbar b hb.le e + epsilon) * ((B b hb.le) ^ 2 / 4) -
        epsilon * (4 * S b hb.le e) ∧
      (epsilon * (4 * S b hb.le e)) /
          (2 * (Wbar b hb.le e + epsilon) * ((B b hb.le) ^ 2 / 4) -
            epsilon * (4 * S b hb.le e)) ≤
        Measure.real outer T ∧
      0 < Measure.real outer T ∧
      ∀ z ∈ T, 0 < tA2 b hb.le e z ∧
        (4 * S b hb.le e) * tW b hb.le e z <
          (Wbar b hb.le e + epsilon) * tA2 b hb.le e z := by
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hNum : 0 < epsilon * (4 * S b hb.le e) :=
    mul_pos hepsilon (mul_pos (by norm_num) hs)
  have ht := p4Q2PZ37ACO_originalRelativeMargin_tail H b hb e epsilon hepsilon
  let T : Set Pair := {z | epsilon * (4 * S b hb.le e) / 2 <
    (Wbar b hb.le e + epsilon) * (A b hb.le e z) ^ 2 -
      (4 * S b hb.le e) * W b hb.le e z}
  have hOpen : IsOpen T :=
    p4Q2PZ37ACO_originalRelativeMargin_region_isOpen H b hb.le e epsilon
  have hMass : 0 < Measure.real outer T :=
    (div_pos hNum ht.1).trans_le ht.2
  refine ⟨T, hOpen, ht.1, ht.2, hMass, ?_⟩
  intro z hz
  change epsilon * (4 * S b hb.le e) / 2 <
    (Wbar b hb.le e + epsilon) * (A b hb.le e z) ^ 2 -
      (4 * S b hb.le e) * W b hb.le e z at hz
  have hMargin : 0 <
      (Wbar b hb.le e + epsilon) * (A b hb.le e z) ^ 2 -
      (4 * S b hb.le e) * W b hb.le e z :=
    (half_pos hNum).trans hz
  rw [p4Q2PZ37ACQ_originalAmplitudeSq_eq_transfer H b hb.le e z,
    p4Q2PZ37ACQ_originalResidualEnergy_eq_transfer H b hb.le e z] at hMargin
  have hRearrange :
      (Wbar b hb.le e + epsilon) * ((P b hb.le z) ^ 2 * tA2 b hb.le e z) -
        (4 * S b hb.le e) * ((P b hb.le z) ^ 2 * tW b hb.le e z) =
      (P b hb.le z) ^ 2 *
        ((Wbar b hb.le e + epsilon) * tA2 b hb.le e z -
          (4 * S b hb.le e) * tW b hb.le e z) := by ring
  rw [hRearrange] at hMargin
  have hp : 0 < (P b hb.le z) ^ 2 :=
    pow_pos (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb.le z) _
  have hTransfer : (4 * S b hb.le e) * tW b hb.le e z <
      (Wbar b hb.le e + epsilon) * tA2 b hb.le e z :=
    sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp hMargin)
  have hW : 0 ≤ tW b hb.le e z :=
    p4Q2PZ37ACQ_transferResidualEnergy_nonneg H b hb.le e z
  have hNonneg : 0 ≤ (4 * S b hb.le e) * tW b hb.le e z :=
    mul_nonneg (mul_nonneg (by norm_num) hs.le) hW
  have hCoeff : 0 < Wbar b hb.le e + epsilon :=
    add_pos_of_nonneg_of_pos
      (p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b hb.le e) hepsilon
  have hAmpPos : 0 < tA2 b hb.le e z :=
    (mul_pos_iff_of_pos_left hCoeff).mp (hNonneg.trans_lt hTransfer)
  exact ⟨hAmpPos, hTransfer⟩

/-- If the true transfer section has no higher-character remainder at
any original boundary pair, ACO's genuine original GI opens a positive-mass
region at every fixed H, b>0 and link. This is a conditional converse, not
an assertion that the physical remainder actually vanishes. -/
theorem p4Q2PZ37ACR_zeroHigherModes_gives_openPositiveGIRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hZero : ∀ z : Pair, tW b hb.le e z = 0) :
    ∃ T : Set Pair, IsOpen T ∧
      0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le f₀ e z| := by
  have hI : (∫ z : Pair, (P b hb.le z) ^ 2 * tW b hb.le e z ∂outer) = 0 := by
    simp [hZero]
  have hw := p4Q2PZ37ACQ_weightedTransferResidual_integral H b hb.le e
  rw [hI] at hw
  have hWbar : Wbar b hb.le e = 0 := hw.symm
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hk := p4Q2PZ37ACP_originalGISlopeSq_pos b hb
  have hBudget : 0 < Budget b hb.le e := by
    change 0 < (4 * S b hb.le e) * kappa b -
      p4Q2PZ37ACI_originalPosteriorResidualEnvelope b * Wbar b hb.le e
    rw [hWbar]
    simp only [mul_zero, sub_zero]
    exact mul_pos (mul_pos (by norm_num) hs) hk
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    H b hb.le e hBudget

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACR_originalResidual_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACR_originalResidual_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACR_originalResidual_halfMean_tail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACR_nonpositiveBudget_forces_positiveResidualMean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACR_nonpositiveBudget_residualMoment_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACR_nonpositiveBudget_forces_openHigherModeRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACR_positiveTransferResidual_has_higherModeWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACR_nonpositiveBudget_has_higherModeWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACR_relaxedTransferRegion_open_mass_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACR_zeroHigherModes_gives_openPositiveGIRegion
