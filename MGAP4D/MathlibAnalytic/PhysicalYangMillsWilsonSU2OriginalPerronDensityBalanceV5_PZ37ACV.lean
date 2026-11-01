import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPerronSignedEnergyBalanceV5_PZ37ACU

/-!
# P4-Q2-PZ37ACV — original Perron-density boundary balance

Append-only physical theorem leaf for the SAME interacting Wilson SU(2)
receiver, centered Gauss-law source, genuine positive Perron representative,
updated transfer U_z, actual two-posterior laws and original pair-Haar
measure. This is not a change of physical receiver or of Haar law.

The original ABZ physical prefactor satisfies
 P_z = ||T_b||^{-1} * sqrtDensity_b(z) > 0.
Only the SAME global positive transfer-norm scalar can be factored
out of the pair-Haar integral. The ORIGINAL boundary-dependent Perron
square density sqrtDensity_b(z)^2 MUST remain inside both integrals.
Define c=||T_b||^{-2}>0 and R(z)=sqrtDensity_b(z)^2.
For ACT's ORIGINAL updated-transfer discriminant
 d_b(z)=16 A_U(z)^2-tau(b) W_U(z), let
 I_+ = integral R(z) * max(d_b(z),0),
 I_- = integral R(z) * max(-d_b(z),0),
 I   = integral R(z) * d_b(z).
Then E_+=c I_+, E_-=c I_-, D_ACT=c I, and I=I_+-I_-.
In particular the exact original ACO GI mean squared CERTIFICATE
is positive iff I_+>I_-; this is a test on the true original
Perron-density boundary data and the original updated transfer.

Moreover I=16 integral R A_U^2 - tau integral R W_U.
A separate exact FC obstruction gives
  E_- <= tau(b) * B_b^2
for the ORIGINAL bounded receiver. Hence the (not established)
physical condition E_+>tau B_b^2 suffices for the true original
positive mean squared certificate, and failure of the mean
certificate forces E_+<=tau B_b^2.

No assumption or conclusion that either strict energy balance holds
for the actual Wilson model, no replacement by an independent Haar
model, no deletion of boundary Perron weights, no volume-uniform
coercivity, and no continuum Yang-Mills mass gap.
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
local instance p4Q2PZ37ACV_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACV_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACV_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACV_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACV_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACV_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "transfer" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num)
local notation "sqrtD" => continuousJointSqrtDensity H 2 (by norm_num)
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local notation "tA2" => p4Q2PZ37ACQ_transferAmplitudeSq H
local notation "tW" => p4Q2PZ37ACQ_transferResidualEnergy H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "tau" => p4Q2PZ37ACP_originalPosteriorExponentGapSq
local notation "kappa" => p4Q2PZ37ACO_originalGISlopeSq
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "eta" => p4Q2PZ37ACS_originalFirstFourEnergyFraction H
local notation "critical" => p4Q2PZ37ACS_originalPosteriorCriticalEnergyFraction
local notation "d" => p4Q2PZ37ACT_originalTransferLocalDiscriminant H
local notation "D" => p4Q2PZ37ACT_originalWeightedTransferDiscriminant H
local notation "w" => p4Q2PZ37ACU_weightedLocalDiscriminant H
local notation "Eplus" => p4Q2PZ37ACU_positiveTransferContribution H
local notation "Eminus" => p4Q2PZ37ACU_negativeTransferContribution H
local instance p4Q2PZ37ACV_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACV_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Original finite-volume transfer norm: ONLY its strictly positive
global reciprocal square can be removed from the outer Haar comparison. -/
def p4Q2PZ37ACV_transferNormScaleSq (b : ℝ) (hb : 0 ≤ b) : ℝ :=
  (‖transfer b hb‖⁻¹) ^ 2
local notation "c" => p4Q2PZ37ACV_transferNormScaleSq H

/-- The true spatial BOUNDARY-DEPENDENT Perron joint half-density square,
not a uniform constant and not an independent posterior probability law. -/
def p4Q2PZ37ACV_originalBoundaryPerronDensitySq
    (b : ℝ) (hb : 0 ≤ b) (z : Pair) : ℝ :=
  (sqrtD b hb z) ^ 2
local notation "R" => p4Q2PZ37ACV_originalBoundaryPerronDensitySq H

/-- Original updated-transfer ACT local discriminator weighted by the
true, varying, nonnegative Perron density square. -/
def p4Q2PZ37ACV_densityLocalDiscriminant
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  R b hb z * d b hb e z
local notation "v" => p4Q2PZ37ACV_densityLocalDiscriminant H

/-- True raw Perron-density positive contribution on original boundary
pairs before the COMMON transfer norm factor. -/
def p4Q2PZ37ACV_densityPositiveContribution
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  ∫ z : Pair, max (v b hb e z) 0 ∂outer
local notation "Iplus" => p4Q2PZ37ACV_densityPositiveContribution H

/-- True raw Perron-density negative contribution on original boundary
pairs, with the SAME updated transfer and Haar measure. -/
def p4Q2PZ37ACV_densityNegativeContribution
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  ∫ z : Pair, max (-(v b hb e z)) 0 ∂outer
local notation "Iminus" => p4Q2PZ37ACV_densityNegativeContribution H

/-- The unnormalized but genuine original Perron-density signed balance. -/
def p4Q2PZ37ACV_densitySignedBalance
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  ∫ z : Pair, v b hb e z ∂outer
local notation "I" => p4Q2PZ37ACV_densitySignedBalance H

/-- The four true SU(2) Haar modes of the updated transfer, weighed by
the original spatial Perron density square. -/
def p4Q2PZ37ACV_densityFourModeMoment
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  ∫ z : Pair, R b hb z * tA2 b hb e z ∂outer
local notation "I4" => p4Q2PZ37ACV_densityFourModeMoment H

/-- Genuine higher-character energy from the same transfer weighted by
the very same original spatial Perron density. -/
def p4Q2PZ37ACV_densityHigherModeMoment
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  ∫ z : Pair, R b hb z * tW b hb e z ∂outer
local notation "Ih" => p4Q2PZ37ACV_densityHigherModeMoment H

/-- Original Wilson physical transfer norm is positive even without
any H-uniform numerical norm estimate or additional assumptions. -/
theorem p4Q2PZ37ACV_transferNormScaleSq_pos
    (b : ℝ) (hb : 0 ≤ b) : 0 < c b hb := by
  unfold p4Q2PZ37ACV_transferNormScaleSq
  exact pow_pos (inv_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b hb)) _

/-- Raw original joint Perron density square is positive at every actual
boundary pair; its profile must NOT be discarded in an integral. -/
theorem p4Q2PZ37ACV_originalBoundaryPerronDensitySq_pos
    (b : ℝ) (hb : 0 ≤ b) (z : Pair) : 0 < R b hb z := by
  unfold p4Q2PZ37ACV_originalBoundaryPerronDensitySq
  exact pow_pos (continuousJointSqrtDensity_pos H 2 (by norm_num) b hb z) _

/-- Exact original ABZ prefactor factorization, not an estimate. -/
theorem p4Q2PZ37ACV_originalPrefactorSq_eq_norm_times_density
    (b : ℝ) (hb : 0 ≤ b) (z : Pair) :
    (P b hb z) ^ 2 = c b hb * R b hb z := by
  unfold p4Q2PZ37ABZ_originalTransferSectionPrefactor
    p4Q2PZ37ACV_transferNormScaleSq
    p4Q2PZ37ACV_originalBoundaryPerronDensitySq
  ring

/-- Weighted ACT original boundary discriminator equals its raw
density-weighted presentation times one global strictly positive
transfer norm factor. -/
theorem p4Q2PZ37ACV_weightedLocal_eq_norm_times_density
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    w b hb e z = c b hb * v b hb e z := by
  unfold p4Q2PZ37ACU_weightedLocalDiscriminant
    p4Q2PZ37ACV_densityLocalDiscriminant
  rw [p4Q2PZ37ACV_originalPrefactorSq_eq_norm_times_density H b hb z]
  ring

/-- Reuse of an elementary identity: a positive common scalar commutes
with the positive/negative part without changing either sign. -/
private theorem p4Q2PZ37ACV_max_mul_nonneg (a x : ℝ) (ha : 0 ≤ a) :
    max (a * x) 0 = a * max x 0 := by
  by_cases hx : 0 ≤ x
  · have hax : 0 ≤ a * x := mul_nonneg ha hx
    rw [max_eq_left hax, max_eq_left hx]
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have hax : a * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hx'
    rw [max_eq_right hax, max_eq_right hx']
    simp

/-- Original Perron-weighted positive contribution differs from the
density-only boundary contribution by exactly one GLOBAL factor c>0. -/
theorem p4Q2PZ37ACV_positiveContribution_eq_norm_times_density
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Eplus b hb e = c b hb * Iplus b hb e := by
  have hc := (p4Q2PZ37ACV_transferNormScaleSq_pos H b hb).le
  unfold p4Q2PZ37ACU_positiveTransferContribution
  calc
    (∫ z : Pair, max (w b hb e z) 0 ∂outer) =
        ∫ z : Pair, c b hb * max (v b hb e z) 0 ∂outer := by
      apply integral_congr_ae
      filter_upwards with z
      rw [p4Q2PZ37ACV_weightedLocal_eq_norm_times_density H b hb e z]
      exact p4Q2PZ37ACV_max_mul_nonneg
        (c b hb) (v b hb e z) hc
    _ = c b hb * Iplus b hb e := by
      rw [integral_const_mul]
      rfl

/-- The exact SAME common norm factor multiplies the truly negative
original pair-Haar boundary contribution. -/
theorem p4Q2PZ37ACV_negativeContribution_eq_norm_times_density
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Eminus b hb e = c b hb * Iminus b hb e := by
  have hc := (p4Q2PZ37ACV_transferNormScaleSq_pos H b hb).le
  unfold p4Q2PZ37ACU_negativeTransferContribution
  calc
    (∫ z : Pair, max (-(w b hb e z)) 0 ∂outer) =
        ∫ z : Pair, c b hb * max (-(v b hb e z)) 0 ∂outer := by
      apply integral_congr_ae
      filter_upwards with z
      rw [p4Q2PZ37ACV_weightedLocal_eq_norm_times_density H b hb e z]
      have hNeg : -(c b hb * v b hb e z) =
          c b hb * (-(v b hb e z)) := by ring
      rw [hNeg]
      exact p4Q2PZ37ACV_max_mul_nonneg
        (c b hb) (-(v b hb e z)) hc
    _ = c b hb * Iminus b hb e := by
      rw [integral_const_mul]
      rfl

/-- Original weighted signed discriminator separates only the
constant global normalization; the spatial density remains integrated. -/
theorem p4Q2PZ37ACV_weightedDiscriminant_eq_norm_times_density
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    D b hb e = c b hb * I b hb e := by
  rw [p4Q2PZ37ACT_weightedDiscriminant_eq_integralLocal H b hb e]
  calc
    (∫ z : Pair, (P b hb z) ^ 2 * d b hb e z ∂outer) =
        ∫ z : Pair, c b hb * v b hb e z ∂outer := by
      apply integral_congr_ae
      filter_upwards with z
      exact p4Q2PZ37ACV_weightedLocal_eq_norm_times_density H b hb e z
    _ = c b hb * I b hb e := by
      rw [integral_const_mul]
      rfl

/-- Unnormalized TRUE Perron-density positive/negative contributions are
nonnegative, without any assumption of favorable physical dominance. -/
theorem p4Q2PZ37ACV_densityContributions_nonneg
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    0 ≤ Iplus b hb e ∧ 0 ≤ Iminus b hb e := by
  constructor
  · unfold p4Q2PZ37ACV_densityPositiveContribution
    exact integral_nonneg (fun z => le_max_right _ _)
  · unfold p4Q2PZ37ACV_densityNegativeContribution
    exact integral_nonneg (fun z => le_max_right _ _)

/-- The ORIGINAL global transfer norm cancels exactly between the
two density signed contributions. No spatial Perron weights cancel. -/
theorem p4Q2PZ37ACV_densitySignedBalance_eq_positive_sub_negative
    (b : ℝ) (hb : 0 < b) (e : Link) :
    I b hb.le e = Iplus b hb.le e - Iminus b hb.le e := by
  have hc := (p4Q2PZ37ACV_transferNormScaleSq_pos H b hb.le).ne'
  have hOriginal :=
    p4Q2PZ37ACU_weightedDiscriminant_eq_positive_sub_negative H b hb e
  rw [p4Q2PZ37ACV_weightedDiscriminant_eq_norm_times_density H b hb.le e,
    p4Q2PZ37ACV_positiveContribution_eq_norm_times_density H b hb.le e,
    p4Q2PZ37ACV_negativeContribution_eq_norm_times_density H b hb.le e] at hOriginal
  have hFactored :
      c b hb.le * I b hb.le e =
        c b hb.le * (Iplus b hb.le e - Iminus b hb.le e) := by
    calc
      _ = c b hb.le * Iplus b hb.le e -
          c b hb.le * Iminus b hb.le e := hOriginal
      _ = _ := by ring
  exact mul_left_cancel₀ hc hFactored

/-- Exact original Perron-density SU(2) four-mode mean, before ONLY
the global transfer normalization is factored out. -/
theorem p4Q2PZ37ACV_weightedFourMode_eq_norm_times_density
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    (∫ z : Pair, (P b hb z) ^ 2 * tA2 b hb e z ∂outer) =
      c b hb * I4 b hb e := by
  calc
    _ = ∫ z : Pair, c b hb * (R b hb z * tA2 b hb e z) ∂outer := by
      apply integral_congr_ae
      filter_upwards with z
      rw [p4Q2PZ37ACV_originalPrefactorSq_eq_norm_times_density H b hb z]
      ring
    _ = c b hb * I4 b hb e := by
      rw [integral_const_mul]
      rfl

/-- Exact original Perron-density SU(2) HIGHER-mode mean; the
boundary-dependent squared half-density remains in this integral. -/
theorem p4Q2PZ37ACV_weightedHigherMode_eq_norm_times_density
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    (∫ z : Pair, (P b hb z) ^ 2 * tW b hb e z ∂outer) =
      c b hb * Ih b hb e := by
  calc
    _ = ∫ z : Pair, c b hb * (R b hb z * tW b hb e z) ∂outer := by
      apply integral_congr_ae
      filter_upwards with z
      rw [p4Q2PZ37ACV_originalPrefactorSq_eq_norm_times_density H b hb z]
      ring
    _ = c b hb * Ih b hb e := by
      rw [integral_const_mul]
      rfl

/-- Division-free exact original Perron density and updated transfer
balance: 16 first-four genuine Haar energy minus tau higher-mode energy. -/
theorem p4Q2PZ37ACV_densitySignedBalance_eq_fourMode_sub_higherMode
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    I b hb e = 16 * I4 b hb e - tau b * Ih b hb e := by
  have hc := (p4Q2PZ37ACV_transferNormScaleSq_pos H b hb).ne'
  have hOriginal := p4Q2PZ37ACV_weightedDiscriminant_eq_norm_times_density H b hb e
  rw [show D b hb e =
      16 * (∫ z : Pair, (P b hb z) ^ 2 * tA2 b hb e z ∂outer) -
      tau b * (∫ z : Pair, (P b hb z) ^ 2 * tW b hb e z ∂outer)
      from rfl] at hOriginal
  rw [p4Q2PZ37ACV_weightedFourMode_eq_norm_times_density H b hb e,
    p4Q2PZ37ACV_weightedHigherMode_eq_norm_times_density H b hb e] at hOriginal
  have hFactored :
      c b hb * I b hb e =
        c b hb * (16 * I4 b hb e - tau b * Ih b hb e) := by
    calc
      _ = 16 * (c b hb * I4 b hb e) -
          tau b * (c b hb * Ih b hb e) := hOriginal.symm
      _ = _ := by ring
  exact mul_left_cancel₀ hc hFactored

/-- At positive b, positivity of the original signed GI *certificate*
is EXACTLY positive dominance of the genuine squared Perron-density
boundary contribution, without transfer-norm normalization. -/
theorem p4Q2PZ37ACV_originalGIMeanBudget_pos_iff_densityDominance
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < Budget b hb.le e ↔ Iminus b hb.le e < Iplus b hb.le e := by
  have hc := p4Q2PZ37ACV_transferNormScaleSq_pos H b hb.le
  rw [p4Q2PZ37ACU_originalGIMeanBudget_pos_iff_positiveDominates H b hb e,
    p4Q2PZ37ACV_negativeContribution_eq_norm_times_density H b hb.le e,
    p4Q2PZ37ACV_positiveContribution_eq_norm_times_density H b hb.le e]
  exact mul_lt_mul_left hc

/-- Equivalent raw true Perron-density comparison of the ACS spectral
threshold for the actual interacting Wilson SU(2) receiver. -/
theorem p4Q2PZ37ACV_originalFirstFourThreshold_iff_densityMoments
    (b : ℝ) (hb : 0 < b) (e : Link) :
    critical b < eta b hb.le e ↔
      tau b * Ih b hb.le e < 16 * I4 b hb.le e := by
  have hc := p4Q2PZ37ACV_transferNormScaleSq_pos H b hb.le
  rw [← p4Q2PZ37ACT_weightedDiscriminant_pos_iff_fraction H b hb e]
  rw [p4Q2PZ37ACV_weightedDiscriminant_eq_norm_times_density H b hb.le e,
    p4Q2PZ37ACV_densitySignedBalance_eq_fourMode_sub_higherMode H b hb.le e]
  constructor
  · intro h
    have hd : 0 < 16 * I4 b hb.le e - tau b * Ih b hb.le e :=
      (mul_pos_iff_of_pos_left hc).mp h
    linarith
  · intro h
    exact mul_pos hc (sub_pos.mpr h)

/-- Exact squared-mean GI certificate in original Perron-density
boundary moments; no hypothesized physical sign is inserted. -/
theorem p4Q2PZ37ACV_originalGIMeanBudget_densityIdentity
    (b : ℝ) (hb : 0 < b) (e : Link) :
    16 * Budget b hb.le e =
      kappa b * c b hb.le *
        (Iplus b hb.le e - Iminus b hb.le e) := by
  rw [p4Q2PZ37ACT_originalGIMeanBudget_eq_weightedDiscriminant H b hb.le e,
    p4Q2PZ37ACV_weightedDiscriminant_eq_norm_times_density H b hb.le e,
    p4Q2PZ37ACV_densitySignedBalance_eq_positive_sub_negative H b hb e]
  ring

/-- The original FOUR-MODE receiver's physical energy remains nonnegative
after the true unnormalized Perron-density weighting. -/
theorem p4Q2PZ37ACV_densityMoments_nonneg
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    0 ≤ I4 b hb e ∧ 0 ≤ Ih b hb e := by
  constructor
  · unfold p4Q2PZ37ACV_densityFourModeMoment
    exact integral_nonneg (fun z =>
      mul_nonneg (sq_nonneg _) (p4Q2PZ37ACQ_transferAmplitudeSq_nonneg H b hb e z))
  · unfold p4Q2PZ37ACV_densityHigherModeMoment
    exact integral_nonneg (fun z =>
      mul_nonneg (sq_nonneg _) (p4Q2PZ37ACQ_transferResidualEnergy_nonneg H b hb e z))

/-- Original ACR receiver FC variance cap bounds the negative PART of the
same ACT Perron-weighted discriminator at every genuine boundary. -/
theorem p4Q2PZ37ACV_negativeWeightedPart_le_originalFC
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    max (-(w b hb e z)) 0 ≤ tau b * (B b hb) ^ 2 := by
  have ht : 0 ≤ tau b := by
    unfold p4Q2PZ37ACP_originalPosteriorExponentGapSq
    exact sq_nonneg _
  have hW : (P b hb z) ^ 2 * tW b hb e z ≤ (B b hb) ^ 2 := by
    rw [← p4Q2PZ37ACQ_originalResidualEnergy_eq_transfer H b hb e z]
    exact p4Q2PZ37ACR_originalResidual_le_FC H b hb e z
  have hWA := mul_le_mul_of_nonneg_left hW ht
  have hA : 0 ≤ (P b hb z) ^ 2 * tA2 b hb e z :=
    mul_nonneg (sq_nonneg _)
      (p4Q2PZ37ACQ_transferAmplitudeSq_nonneg H b hb e z)
  have hNeg : -(w b hb e z) ≤ tau b * (B b hb) ^ 2 := by
    unfold p4Q2PZ37ACU_weightedLocalDiscriminant
      p4Q2PZ37ACT_originalTransferLocalDiscriminant
    nlinarith only [hWA, hA]
  exact max_le hNeg (mul_nonneg ht (sq_nonneg _))

/-- The original finite-volume FC envelope bounds the entire negative
part of the genuine Perron-weighted two-posterior GI squared certificate. -/
theorem p4Q2PZ37ACV_originalNegativeContribution_le_FC
    (b : ℝ) (hb : 0 < b) (e : Link) :
    Eminus b hb.le e ≤ tau b * (B b hb.le) ^ 2 := by
  have hMinus := (p4Q2PZ37ACU_signedParts_integrable H b hb e).2
  unfold p4Q2PZ37ACU_negativeTransferContribution
  calc
    (∫ z : Pair, max (-(w b hb.le e z)) 0 ∂outer) ≤
        ∫ _z : Pair, tau b * (B b hb.le) ^ 2 ∂outer :=
      integral_mono hMinus (integrable_const _)
        (fun z => p4Q2PZ37ACV_negativeWeightedPart_le_originalFC H b hb.le e z)
    _ = tau b * (B b hb.le) ^ 2 := by simp

/-- A directly checkable sufficient (not established) inequality on
positive original Perron-transfer boundary contribution defeats ALL
negative contribution by the genuine FC envelope. -/
theorem p4Q2PZ37ACV_originalPositiveContribution_aboveFC_gives_positiveBudget
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hSufficient : tau b * (B b hb.le) ^ 2 < Eplus b hb.le e) :
    0 < Budget b hb.le e := by
  have hNegative := p4Q2PZ37ACV_originalNegativeContribution_le_FC H b hb e
  exact (p4Q2PZ37ACU_originalGIMeanBudget_pos_iff_positiveDominates H b hb e).mpr
    (lt_of_le_of_lt hNegative hSufficient)

/-- Conversely: physical failure of the ACO positive mean certificate
forces the original positive Perron-transfer boundary contribution BELOW
the explicit genuine FC obstruction. This does NOT imply GI vanishing. -/
theorem p4Q2PZ37ACV_nonpositiveBudget_forces_positivePart_FC_obstruction
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpositive : Budget b hb.le e ≤ 0) :
    Eplus b hb.le e ≤ tau b * (B b hb.le) ^ 2 := by
  have hNonpositiveBalance :=
    (p4Q2PZ37ACU_weightedDiscriminant_nonpos_iff_negativeDominates
      H b hb e).mp
      ((p4Q2PZ37ACT_weightedDiscriminant_nonpos_iff_obstruction
        H b hb e).mpr
        ((p4Q2PZ37ACS_originalGIMeanBudget_nonpos_iff_fractionObstruction
          H b hb e).mp hNonpositive))
  exact hNonpositiveBalance.trans
    (p4Q2PZ37ACV_originalNegativeContribution_le_FC H b hb e)

/-- The unnormalized true Perron-density boundary balance, if strictly
positive, implies actual nonzero signed two-posterior GI response on
an OPEN region of genuine original pair-Haar positive mass via ACO.
The certificate, not the GI response, is what has been computed here. -/
theorem p4Q2PZ37ACV_densityDominance_gives_open_originalGIRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hDensity : Iminus b hb.le e < Iplus b hb.le e) :
    ∃ T : Set Pair, IsOpen T ∧
      0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le f₀ e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    H b hb.le e
    ((p4Q2PZ37ACV_originalGIMeanBudget_pos_iff_densityDominance
      H b hb e).mpr hDensity)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_transferNormScaleSq_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_originalBoundaryPerronDensitySq_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_originalPrefactorSq_eq_norm_times_density
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_weightedLocal_eq_norm_times_density
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_positiveContribution_eq_norm_times_density
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_negativeContribution_eq_norm_times_density
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_weightedDiscriminant_eq_norm_times_density
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_densityContributions_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_densitySignedBalance_eq_positive_sub_negative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_weightedFourMode_eq_norm_times_density
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_weightedHigherMode_eq_norm_times_density
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_densitySignedBalance_eq_fourMode_sub_higherMode
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_originalGIMeanBudget_pos_iff_densityDominance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_originalFirstFourThreshold_iff_densityMoments
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_originalGIMeanBudget_densityIdentity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_densityMoments_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_negativeWeightedPart_le_originalFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_originalNegativeContribution_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_originalPositiveContribution_aboveFC_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_nonpositiveBudget_forces_positivePart_FC_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACV_densityDominance_gives_open_originalGIRegion
