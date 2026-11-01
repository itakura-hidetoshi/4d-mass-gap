import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPerronTransferDiscriminantV5_PZ37ACT

/-!
# P4-Q2-PZ37ACU — exact positive/negative original Perron-transfer balance

An append-only exact original physical Wilson SU(2) theorem leaf. Preserve the
same centered Gauss-law source, unchanged original FF receiver, positive
Perron ground representative P_z, UPDATED original transfer U_z, original
boundary pair and SU(2) pair-Haar measure, two interacting posteriors and
the exact original four Haar modes.

ACT defines d_b(z)=16*A_U(z)^2-tau(b)*W_U(z) and
D_b=integral P_z^2*d_b(z) d(nu_H). Here x_+=max(x,0) and x_-=max(-x,0).
We establish the original positively and negatively weighted contributions
 E_plus  = integral P_z^2*(d_b(z))_+ d(nu_H),
 E_minus = integral P_z^2*(d_b(z))_- d(nu_H).
They are separately nonnegative and finite at every b>0 and satisfy
 D_b = E_plus - E_minus,
 16*M_GI = kappa(b)*(E_plus-E_minus).
Thus positivity of the original ACO GI mean squared CERTIFICATE is
EXACTLY the strict dominance E_plus>E_minus. In the opposite strict case
D_b<0, a nonempty OPEN region of positive original pair-Haar mass has
d_b(z)<0, strictly positive ORIGINAL updated-transfer higher SU(2)
Haar remainder, and an actual nonzero higher-mode character witness.

No positive global balance is assumed or proved for the actual Wilson
model; no fabricated residual dominance, removed Perron weight,
volume-uniform bound, signed GI-response equality, or continuum
four-dimensional Yang-Mills mass gap is claimed.
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
local instance p4Q2PZ37ACU_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACU_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACU_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACU_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACU_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACU_probability : IsProbabilityMeasure μ :=
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
local notation "tA2" => p4Q2PZ37ACQ_transferAmplitudeSq H
local notation "tW" => p4Q2PZ37ACQ_transferResidualEnergy H
local notation "tau" => p4Q2PZ37ACP_originalPosteriorExponentGapSq
local notation "kappa" => p4Q2PZ37ACO_originalGISlopeSq
local notation "Q" => p4Q2PZ37ACO_originalGISquaredMargin H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "eta" => p4Q2PZ37ACS_originalFirstFourEnergyFraction H
local notation "critical" => p4Q2PZ37ACS_originalPosteriorCriticalEnergyFraction
local notation "d" => p4Q2PZ37ACT_originalTransferLocalDiscriminant H
local notation "D" => p4Q2PZ37ACT_originalWeightedTransferDiscriminant H
local instance p4Q2PZ37ACU_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACU_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- ORIGINAL boundary/Perron weighted ACT local discriminant. -/
def p4Q2PZ37ACU_weightedLocalDiscriminant
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  (P b hb z) ^ 2 * d b hb e z
local notation "w" => p4Q2PZ37ACU_weightedLocalDiscriminant H

/-- Genuine positive contribution; the max acts at each ORIGINAL pair of
boundary configurations before the original pair-Haar integration. -/
def p4Q2PZ37ACU_positiveTransferContribution
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  ∫ z : Pair, max (w b hb e z) 0 ∂outer
local notation "Eplus" => p4Q2PZ37ACU_positiveTransferContribution H

/-- Genuine negative contribution; an independently weighted negative
part of exactly the SAME updated physical Perron transfer section. -/
def p4Q2PZ37ACU_negativeTransferContribution
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  ∫ z : Pair, max (-(w b hb e z)) 0 ∂outer
local notation "Eminus" => p4Q2PZ37ACU_negativeTransferContribution H

/-- The actual weighted discriminator is continuous on original boundary
pairs at b>0, deduced from the already proved continuous original local
GI squared certificate; no continuity of an invented receiver is used. -/
theorem p4Q2PZ37ACU_weightedLocalDiscriminant_continuous
    (b : ℝ) (hb : 0 < b) (e : Link) :
    Continuous (w b hb.le e) := by
  have hk : kappa b ≠ 0 :=
    (p4Q2PZ37ACP_originalGISlopeSq_pos b hb).ne'
  have hEq : (fun z : Pair => w b hb.le e z) =
      (fun z : Pair => (16 * Q b hb.le e z) / kappa b) := by
    funext z
    unfold p4Q2PZ37ACU_weightedLocalDiscriminant
    apply (eq_div_iff hk).mpr
    calc
      ((P b hb.le z) ^ 2 * d b hb.le e z) * kappa b =
          kappa b * (P b hb.le z) ^ 2 * d b hb.le e z := by ring
      _ = 16 * Q b hb.le e z :=
        (p4Q2PZ37ACT_localGICertificate_eq_transferDiscriminant
          H b hb.le e z).symm
  rw [show w b hb.le e = (fun z : Pair => w b hb.le e z) from rfl, hEq]
  exact (continuous_const.mul
    (p4Q2PZ37ACO_originalGISquaredMargin_continuous H b hb.le e)).div_const _

/-- The positive and negative true weighted signed contributions are both
integrable from the original receiver's continuity and compact boundary. -/
theorem p4Q2PZ37ACU_signedParts_integrable
    (b : ℝ) (hb : 0 < b) (e : Link) :
    Integrable (fun z : Pair => max (w b hb.le e z) 0) outer ∧
    Integrable (fun z : Pair => max (-(w b hb.le e z)) 0) outer := by
  have hc := p4Q2PZ37ACU_weightedLocalDiscriminant_continuous H b hb e
  constructor
  · exact (hc.max continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hc.neg.max continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Algebraic nonnegative-scalar positive-part identity, requiring no
division, no uniform lower bound, and no additional physical assumption. -/
private theorem p4Q2PZ37ACU_max_mul_nonneg
    (p x : ℝ) (hp : 0 ≤ p) :
    max (p * x) 0 = p * max x 0 := by
  by_cases hx : 0 ≤ x
  · have hpx : 0 ≤ p * x := mul_nonneg hp hx
    rw [max_eq_left hpx, max_eq_left hx]
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have hpx : p * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp hx'
    rw [max_eq_right hpx, max_eq_right hx']
    simp

/-- Perron factor stays INSIDE the positive integrand, not dropped from
the outer pair-Haar expectation. -/
theorem p4Q2PZ37ACU_positivePart_eq_Perron_weighted
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    max (w b hb e z) 0 =
      (P b hb z) ^ 2 * max (d b hb e z) 0 := by
  unfold p4Q2PZ37ACU_weightedLocalDiscriminant
  exact p4Q2PZ37ACU_max_mul_nonneg
    ((P b hb z) ^ 2) (d b hb e z) (sq_nonneg _)

/-- The same true Perron square weights the negative integrand. -/
theorem p4Q2PZ37ACU_negativePart_eq_Perron_weighted
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    max (-(w b hb e z)) 0 =
      (P b hb z) ^ 2 * max (-(d b hb e z)) 0 := by
  have heq : -(w b hb e z) = (P b hb z) ^ 2 * (-(d b hb e z)) := by
    unfold p4Q2PZ37ACU_weightedLocalDiscriminant
    ring
  rw [heq]
  exact p4Q2PZ37ACU_max_mul_nonneg
    ((P b hb z) ^ 2) (-(d b hb e z)) (sq_nonneg _)

/-- BOTH true Perron factors remain in the integrated positive/negative
contributions (no replacement by independent Haar sampling). -/
theorem p4Q2PZ37ACU_signedContributions_eq_originalPerronIntegrals
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Eplus b hb e =
        (∫ z : Pair, (P b hb z) ^ 2 * max (d b hb e z) 0 ∂outer) ∧
    Eminus b hb e =
        (∫ z : Pair, (P b hb z) ^ 2 * max (-(d b hb e z)) 0 ∂outer) := by
  constructor
  · unfold p4Q2PZ37ACU_positiveTransferContribution
    apply integral_congr_ae
    filter_upwards with z
    exact p4Q2PZ37ACU_positivePart_eq_Perron_weighted H b hb e z
  · unfold p4Q2PZ37ACU_negativeTransferContribution
    apply integral_congr_ae
    filter_upwards with z
    exact p4Q2PZ37ACU_negativePart_eq_Perron_weighted H b hb e z

/-- Both true signed-mass contributions are nonnegative, regardless of
the UNKNOWN sign of their difference in the real Wilson model. -/
theorem p4Q2PZ37ACU_signedContributions_nonneg
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    0 ≤ Eplus b hb e ∧ 0 ≤ Eminus b hb e := by
  constructor
  · unfold p4Q2PZ37ACU_positiveTransferContribution
    exact integral_nonneg (fun z => le_max_right _ _)
  · unfold p4Q2PZ37ACU_negativeTransferContribution
    exact integral_nonneg (fun z => le_max_right _ _)

/-- Exact positive-minus-negative original boundary/Perron transfer
decomposition. Both separately integrable at b>0. -/
theorem p4Q2PZ37ACU_weightedDiscriminant_eq_positive_sub_negative
    (b : ℝ) (hb : 0 < b) (e : Link) :
    D b hb.le e = Eplus b hb.le e - Eminus b hb.le e := by
  obtain ⟨hPlus, hMinus⟩ :=
    p4Q2PZ37ACU_signedParts_integrable H b hb e
  rw [p4Q2PZ37ACT_weightedDiscriminant_eq_integralLocal H b hb.le e]
  change (∫ z : Pair, w b hb.le e z ∂outer) =
    (∫ z : Pair, max (w b hb.le e z) 0 ∂outer) -
    (∫ z : Pair, max (-(w b hb.le e z)) 0 ∂outer)
  rw [← integral_sub hPlus hMinus]
  apply integral_congr_ae
  filter_upwards with z
  exact (max_zero_sub_max_neg_zero_eq_self (w b hb.le e z)).symm

/-- EXACT strict original positive-mean certificate criterion, with its
true ORIGINAL Perron-weighted positive and negative signed energies. -/
theorem p4Q2PZ37ACU_weightedDiscriminant_pos_iff_positiveDominates
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < D b hb.le e ↔ Eminus b hb.le e < Eplus b hb.le e := by
  rw [p4Q2PZ37ACU_weightedDiscriminant_eq_positive_sub_negative H b hb e]
  exact sub_pos

/-- Exact obstruction: the negative genuine contribution is at least the
positive one. This does NOT assert vanishing of the actual signed GI gap. -/
theorem p4Q2PZ37ACU_weightedDiscriminant_nonpos_iff_negativeDominates
    (b : ℝ) (hb : 0 < b) (e : Link) :
    D b hb.le e ≤ 0 ↔ Eplus b hb.le e ≤ Eminus b hb.le e := by
  rw [p4Q2PZ37ACU_weightedDiscriminant_eq_positive_sub_negative H b hb e]
  constructor <;> intro h <;> linarith

/-- Strictly negative mean squared-certificate discriminator corresponds to
a strict surplus of the actual negative Perron-weighted contribution. -/
theorem p4Q2PZ37ACU_weightedDiscriminant_neg_iff_strictNegativeDominates
    (b : ℝ) (hb : 0 < b) (e : Link) :
    D b hb.le e < 0 ↔ Eplus b hb.le e < Eminus b hb.le e := by
  rw [p4Q2PZ37ACU_weightedDiscriminant_eq_positive_sub_negative H b hb e]
  constructor <;> intro h <;> linarith

/-- Exact genuine GI MEAN SQUARED CERTIFICATE balance, keeping the
original physical receiver and Perron-updated transfer. -/
theorem p4Q2PZ37ACU_originalGIMeanBudget_signedBalance_identity
    (b : ℝ) (hb : 0 < b) (e : Link) :
    16 * Budget b hb.le e =
      kappa b * (Eplus b hb.le e - Eminus b hb.le e) := by
  rw [p4Q2PZ37ACT_originalGIMeanBudget_eq_weightedDiscriminant H b hb.le e,
    p4Q2PZ37ACU_weightedDiscriminant_eq_positive_sub_negative H b hb e]

/-- The ACO positive mean GI squared certificate is EXACTLY a strict
positive-vs-negative Perron transfer energy dominance test. -/
theorem p4Q2PZ37ACU_originalGIMeanBudget_pos_iff_positiveDominates
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < Budget b hb.le e ↔ Eminus b hb.le e < Eplus b hb.le e := by
  have hBudget := p4Q2PZ37ACS_originalGIMeanBudget_pos_iff_firstFourFraction
    H b hb e
  have hD := p4Q2PZ37ACT_weightedDiscriminant_pos_iff_fraction H b hb e
  exact (hBudget.trans hD.symm).trans
    (p4Q2PZ37ACU_weightedDiscriminant_pos_iff_positiveDominates H b hb e)

/-- A sharpened original ACS spectral criterion, now expressed as the
direct sign balance of the true updated Perron-transfer boundary data. -/
theorem p4Q2PZ37ACU_originalFirstFourThreshold_iff_signedBalance
    (b : ℝ) (hb : 0 < b) (e : Link) :
    critical b < eta b hb.le e ↔
      Eminus b hb.le e < Eplus b hb.le e := by
  exact (p4Q2PZ37ACT_weightedDiscriminant_pos_iff_fraction H b hb e).symm.trans
    (p4Q2PZ37ACU_weightedDiscriminant_pos_iff_positiveDominates H b hb e)

/-- A numerical lower bound on the true positive-minus-negative
Perron-transfer margin yields a quantitative original GI squared-mean
certificate bound, retaining the original b-dependent coefficient. -/
theorem p4Q2PZ37ACU_originalQuantitativePositiveBalance
    (b : ℝ) (hb : 0 < b) (e : Link) (epsilon : ℝ)
    (hDominance : Eminus b hb.le e + epsilon ≤ Eplus b hb.le e) :
    kappa b * epsilon ≤ 16 * Budget b hb.le e := by
  have hk := p4Q2PZ37ACP_originalGISlopeSq_pos b hb
  have hD : epsilon ≤ D b hb.le e := by
    rw [p4Q2PZ37ACU_weightedDiscriminant_eq_positive_sub_negative H b hb e]
    linarith only [hDominance]
  calc
    kappa b * epsilon ≤ kappa b * D b hb.le e :=
      mul_le_mul_of_nonneg_left hD hk.le
    _ = 16 * Budget b hb.le e :=
      (p4Q2PZ37ACT_originalGIMeanBudget_eq_weightedDiscriminant H b hb.le e).symm

/-- Strictly positive discriminator gives an explicitly positive genuine
Perron-weighted positive contribution. -/
theorem p4Q2PZ37ACU_positiveBalance_forces_positiveContribution
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hD : 0 < D b hb.le e) :
    0 < Eplus b hb.le e := by
  have hn := (p4Q2PZ37ACU_signedContributions_nonneg H b hb.le e).2
  have hSplit := p4Q2PZ37ACU_weightedDiscriminant_eq_positive_sub_negative H b hb e
  rw [hSplit] at hD
  linarith only [hn, hD]

/-- Strictly negative discriminator gives a strictly positive genuine
negative contribution, without interpreting the signed GI response. -/
theorem p4Q2PZ37ACU_negativeBalance_forces_negativeContribution
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hD : D b hb.le e < 0) :
    0 < Eminus b hb.le e := by
  have hp := (p4Q2PZ37ACU_signedContributions_nonneg H b hb.le e).1
  have hSplit := p4Q2PZ37ACU_weightedDiscriminant_eq_positive_sub_negative H b hb e
  rw [hSplit] at hD
  linarith only [hp, hD]

/-- ACT's positive balance forces an OPEN positive-Haar-mass set of
strictly favorable ACT boundary discriminants; this remains conditional
on the still-OPEN true physical mean positive balance. -/
theorem p4Q2PZ37ACU_positiveBalance_forces_openPositiveTransferRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hBalance : Eminus b hb.le e < Eplus b hb.le e) :
    ∃ T : Set Pair, IsOpen T ∧
      0 < Measure.real outer T ∧
      ∀ z ∈ T, 0 < d b hb.le e z := by
  have hD :=
    (p4Q2PZ37ACU_weightedDiscriminant_pos_iff_positiveDominates
      H b hb e).mpr hBalance
  have hFraction :=
    (p4Q2PZ37ACT_weightedDiscriminant_pos_iff_fraction H b hb e).mp hD
  obtain ⟨T, hOpen, _hDen, _hFloor, hMass, hOnT⟩ :=
    p4Q2PZ37ACT_positiveFraction_forces_openTransferRegion
      H b hb e hFraction
  exact ⟨T, hOpen, hMass, hOnT⟩

/-- Novel STRICT NEGATIVE balance consequence: an OPEN original pair-Haar
positive-mass region consists of genuinely unfavorable updated-transfer
boundary pairs, each with strictly positive actual higher SU(2) Haar
residual and a nonzero higher-character witness. The sign of the actual
signed two-posterior GI response is deliberately NOT inferred. -/
theorem p4Q2PZ37ACU_strictNegativeBalance_forces_openHigherModeRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hBalance : Eplus b hb.le e < Eminus b hb.le e) :
    ∃ T : Set Pair, IsOpen T ∧
      0 < Measure.real outer T ∧
      ∀ z ∈ T, d b hb.le e z < 0 ∧
        0 < tW b hb.le e z ∧
        ∃ g : G, CompactFiniteHaarProjection.remainder μ
          (U b hb.le f₀ e z) p4Q2PZ37ACK_fourModeCharacter g ≠ 0 := by
  have hD :=
    (p4Q2PZ37ACU_weightedDiscriminant_neg_iff_strictNegativeDominates
      H b hb e).mpr hBalance
  have hNegative : 0 < Eminus b hb.le e :=
    p4Q2PZ37ACU_negativeBalance_forces_negativeContribution H b hb e hD
  let T : Set Pair := {z : Pair | w b hb.le e z < 0}
  have hOpen : IsOpen T :=
    isOpen_lt (p4Q2PZ37ACU_weightedLocalDiscriminant_continuous H b hb e)
      continuous_const
  have hNonempty : T.Nonempty := by
    by_contra hEmpty
    have hNonneg (z : Pair) : 0 ≤ w b hb.le e z := by
      by_contra hn
      exact hEmpty ⟨z, lt_of_not_ge hn⟩
    have hZero : (fun z : Pair => max (-(w b hb.le e z)) 0) =
        (fun _ : Pair => (0 : ℝ)) := by
      funext z
      exact max_eq_right (neg_nonpos.mpr (hNonneg z))
    have hI : Eminus b hb.le e = 0 := by
      unfold p4Q2PZ37ACU_negativeTransferContribution
      rw [hZero]
      simp
    exact (ne_of_gt hNegative) hI
  letI : Measure.IsOpenPosMeasure outer := by
    letI : (normalizedCompactHaar G).IsOpenPosMeasure := by
      unfold normalizedCompactHaar
      infer_instance
    letI : (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
      unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
      infer_instance
    unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    infer_instance
  have hMass : 0 < Measure.real outer T :=
    ENNReal.toReal_pos (hOpen.measure_pos outer hNonempty).ne' (measure_ne_top _ _)
  refine ⟨T, hOpen, hMass, ?_⟩
  intro z hz
  have hp : 0 < (P b hb.le z) ^ 2 :=
    pow_pos (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb.le z) _
  have hWeighted : (P b hb.le z) ^ 2 * d b hb.le e z < 0 := hz
  have hd : d b hb.le e z < 0 := by
    by_contra hn
    have hnonneg : 0 ≤ d b hb.le e z := le_of_not_gt hn
    exact (not_lt_of_ge (mul_nonneg hp.le hnonneg)) hWeighted
  have ha := p4Q2PZ37ACQ_transferAmplitudeSq_nonneg H b hb.le e z
  have ht := p4Q2PZ37ACP_originalPosteriorExponentGapSq_pos b hb
  have hProduct : 0 < tau b * tW b hb.le e z := by
    change 16 * tA2 b hb.le e z - tau b * tW b hb.le e z < 0 at hd
    nlinarith only [hd, ha]
  have hw : 0 < tW b hb.le e z :=
    (mul_pos_iff_of_pos_left ht).mp hProduct
  exact ⟨hd, hw,
    p4Q2PZ37ACR_positiveTransferResidual_has_higherModeWitness
      H b hb.le e z hw⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_weightedLocalDiscriminant_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_signedParts_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_positivePart_eq_Perron_weighted
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_negativePart_eq_Perron_weighted
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_signedContributions_eq_originalPerronIntegrals
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_signedContributions_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_weightedDiscriminant_eq_positive_sub_negative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_weightedDiscriminant_pos_iff_positiveDominates
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_weightedDiscriminant_nonpos_iff_negativeDominates
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_weightedDiscriminant_neg_iff_strictNegativeDominates
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_originalGIMeanBudget_signedBalance_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_originalGIMeanBudget_pos_iff_positiveDominates
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_originalFirstFourThreshold_iff_signedBalance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_originalQuantitativePositiveBalance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_positiveBalance_forces_positiveContribution
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_negativeBalance_forces_negativeContribution
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_positiveBalance_forces_openPositiveTransferRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACU_strictNegativeBalance_forces_openHigherModeRegion
