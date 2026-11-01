import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPerronDensityBalanceV5_PZ37ACV

/-!
# P4-Q2-PZ37ACW — genuine original Perron-positive region/complement balance

Same original interacting Wilson SU(2), physical Gauss-law centered source,
FF receiver, positive Perron ground-state representative, true updated
transfer section, two interacting posteriors and original pair-Haar measure.

ACT/ACU/ACV proved for b>0 that the local genuinely Perron-weighted
discriminant w_b(z)=P_z²*(16 A_U(z)²-tau(b)*W_U(z)) is continuous and
 D_b=integral w_b = Eplus_b-Eminus_b,
 16*M_GI=kappa(b)*D_b.
ACV's original receiver FC cap gives max(-w_b(z),0)<=C_b,
where C_b=tau(b)*B_b²>=0. The new original threshold region is
 T_delta={z : original boundary pair | delta < w_b(z)}.
It is OPEN for each delta, without any newly assumed Perron floor.

For delta>=0, the original pair-Haar mass m_delta=nu_H(T_delta)
controls BOTH separately Perron-weighted contributions:
  delta*m_delta <= Eplus_b,
  Eminus_b <= C_b*(1-m_delta),
  delta*m_delta-C_b*(1-m_delta) <= D_b.
Thus m_delta>C_b/(delta+C_b), delta>0, is a sufficient *conditional*
criterion for positive ACO mean squared-GI certificate, retaining all true
P_z² factors. Conversely failure of that positive mean certificate
forces delta*m_delta <= C_b*(1-m_delta) for every delta>=0.

Moreover the established ORIGINAL positive FC squared-certificate cap
implies w_b(z)<=4*B_b², so if D_b>0, the genuine OPEN half-mean
Perron-threshold region satisfies the explicit Haar-mass floor
 D_b/(8*B_b²-D_b) <= nu_H{z : D_b/2 < w_b(z)}.
This is conditional, not an assertion that physical D_b>0 holds.

No new or independent Haar law, no lost Perron density, no volume-uniform
bound, no identification of the mean certificate with the signed actual
two-posterior GI response, and no continuum Yang-Mills mass-gap claim.
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
local instance p4Q2PZ37ACW_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACW_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACW_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACW_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACW_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACW_probability : IsProbabilityMeasure μ :=
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
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Q" => p4Q2PZ37ACO_originalGISquaredMargin H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "D" => p4Q2PZ37ACT_originalWeightedTransferDiscriminant H
local notation "d" => p4Q2PZ37ACT_originalTransferLocalDiscriminant H
local notation "w" => p4Q2PZ37ACU_weightedLocalDiscriminant H
local notation "Eplus" => p4Q2PZ37ACU_positiveTransferContribution H
local notation "Eminus" => p4Q2PZ37ACU_negativeTransferContribution H
local instance p4Q2PZ37ACW_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACW_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Finite-volume ORIGINAL physical FC cap on the negative Perron-weighted
local contribution, with no assumed volume-uniform positive floor. -/
def p4Q2PZ37ACW_originalNegativeFCBudget
    (b : ℝ) (hb : 0 ≤ b) : ℝ :=
  tau b * (B b hb) ^ 2
local notation "C" => p4Q2PZ37ACW_originalNegativeFCBudget H

/-- At threshold delta, the ORIGINAL open boundary region where the
genuinely Perron-weighted transfer discriminator exceeds delta. -/
def p4Q2PZ37ACW_originalPositiveWeightThresholdRegion
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (delta : ℝ) : Set Pair :=
  {z | delta < w b hb e z}
local notation "T" => p4Q2PZ37ACW_originalPositiveWeightThresholdRegion H

/-- The true physical negative FC budget is always nonnegative. -/
theorem p4Q2PZ37ACW_originalNegativeFCBudget_nonneg
    (b : ℝ) (hb : 0 ≤ b) :
    0 ≤ C b hb := by
  unfold p4Q2PZ37ACW_originalNegativeFCBudget
    p4Q2PZ37ACP_originalPosteriorExponentGapSq
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- True original negative local Perron-weighted energy is pointwise
bounded by the original FF receiver's existing FC envelope. -/
theorem p4Q2PZ37ACW_originalNegativePart_le_FC
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    max (-(w b hb e z)) 0 ≤ C b hb := by
  exact p4Q2PZ37ACV_negativeWeightedPart_le_originalFC H b hb e z

/-- ACT's weighted local discriminator has a pointwise lower FC floor,
without dropping any spatial Perron factor. -/
theorem p4Q2PZ37ACW_originalWeightedDiscriminant_ge_negFC
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    -C b hb ≤ w b hb e z := by
  have hCap := p4Q2PZ37ACW_originalNegativePart_le_FC H b hb e z
  have hNeg : -(w b hb e z) ≤ C b hb :=
    (le_max_left _ _).trans hCap
  linarith only [hNeg]

/-- Original favorable weighted boundary region is OPEN, not a measurable
set created by replacing the physical posterior or transfer. -/
theorem p4Q2PZ37ACW_originalThresholdRegion_isOpen
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ) :
    IsOpen (T b hb.le e delta) := by
  unfold p4Q2PZ37ACW_originalPositiveWeightThresholdRegion
  exact isOpen_lt continuous_const
    (p4Q2PZ37ACU_weightedLocalDiscriminant_continuous H b hb e)

/-- Positive weighted threshold implies a genuinely positive original
transfer discriminator at the SAME physical boundary pair. -/
theorem p4Q2PZ37ACW_originalThresholdRegion_has_localFourModeDominance
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (hdelta : 0 ≤ delta) (z : Pair)
    (hz : z ∈ T b hb.le e delta) :
    0 < d b hb.le e z ∧ 0 < tA2 b hb.le e z := by
  have hw : 0 < w b hb.le e z := lt_of_le_of_lt hdelta hz
  have hp : 0 < (P b hb.le z) ^ 2 :=
    pow_pos (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb.le z) _
  have hd : 0 < d b hb.le e z := by
    change 0 < (P b hb.le z) ^ 2 * d b hb.le e z at hw
    exact (mul_pos_iff_of_pos_left hp).mp hw
  have hW := p4Q2PZ37ACQ_transferResidualEnergy_nonneg H b hb.le e z
  have ht : 0 ≤ tau b := sq_nonneg _
  have hProduct : 0 ≤ tau b * tW b hb.le e z := mul_nonneg ht hW
  have ha : 0 < tA2 b hb.le e z := by
    change 0 < 16 * tA2 b hb.le e z - tau b * tW b hb.le e z at hd
    nlinarith only [hd, hProduct]
  exact ⟨hd, ha⟩

/-- Explicit region-measure floor for the genuine first-four energy's
positive Perron-weighted part. delta is not asserted to exist uniformly. -/
theorem p4Q2PZ37ACW_originalPositiveContribution_regionMass_lower
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ) :
    delta * Measure.real outer (T b hb.le e delta) ≤ Eplus b hb.le e := by
  have hMeas : MeasurableSet (T b hb.le e delta) :=
    (p4Q2PZ37ACW_originalThresholdRegion_isOpen H b hb e delta).measurableSet
  have hInd : Integrable
      ((T b hb.le e delta).indicator (fun _ : Pair => (1 : ℝ))) outer :=
    (integrable_const _).indicator hMeas
  have hLow : Integrable
      (fun z : Pair =>
        delta * (T b hb.le e delta).indicator (fun _ => (1 : ℝ)) z) outer :=
    hInd.const_mul delta
  have hPos := (p4Q2PZ37ACU_signedParts_integrable H b hb e).1
  have hPoint (z : Pair) :
      delta * (T b hb.le e delta).indicator (fun _ => (1 : ℝ)) z ≤
        max (w b hb.le e z) 0 := by
    by_cases hz : z ∈ T b hb.le e delta
    · rw [Set.indicator_of_mem hz]
      have hzi : delta < w b hb.le e z := hz
      simpa only [mul_one] using
        (le_of_lt hzi).trans (le_max_left (w b hb.le e z) 0)
    · rw [Set.indicator_of_notMem hz]
      simp only [mul_zero]
      exact le_max_right (w b hb.le e z) 0
  have hIntegral := integral_mono hLow hPos hPoint
  change (∫ z : Pair,
    delta * (T b hb.le e delta).indicator (fun _ => (1 : ℝ)) z ∂outer) ≤
      Eplus b hb.le e at hIntegral
  calc
    delta * Measure.real outer (T b hb.le e delta) =
        (∫ z : Pair,
          delta * (T b hb.le e delta).indicator (fun _ => (1 : ℝ)) z ∂outer) := by
      rw [integral_const_mul, integral_indicator_const (1 : ℝ) hMeas]
      simp
    _ ≤ Eplus b hb.le e := hIntegral

/-- The complementary original boundary region has its negative
Perron-weighted contribution bounded by its Haar mass times the true FC
budget. No global Perron-density floor or substitute receiver is used. -/
theorem p4Q2PZ37ACW_originalNegativeContribution_complementMass_upper
    (b : ℝ) (hb : 0 < b) (e : Link)
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    Eminus b hb.le e ≤
      C b hb.le * (1 - Measure.real outer (T b hb.le e delta)) := by
  have hMeas : MeasurableSet (T b hb.le e delta) :=
    (p4Q2PZ37ACW_originalThresholdRegion_isOpen H b hb e delta).measurableSet
  have hInd : Integrable
      ((T b hb.le e delta).indicator (fun _ : Pair => (1 : ℝ))) outer :=
    (integrable_const _).indicator hMeas
  have hConst : Integrable (fun _z : Pair => C b hb.le) outer :=
    integrable_const _
  have hEnvelope : Integrable (fun z : Pair =>
      C b hb.le -
        C b hb.le * (T b hb.le e delta).indicator (fun _ => (1 : ℝ)) z)
      outer := hConst.sub (hInd.const_mul _)
  have hNeg := (p4Q2PZ37ACU_signedParts_integrable H b hb e).2
  have hPoint (z : Pair) :
      max (-(w b hb.le e z)) 0 ≤
        C b hb.le -
          C b hb.le * (T b hb.le e delta).indicator (fun _ => (1 : ℝ)) z := by
    by_cases hz : z ∈ T b hb.le e delta
    · rw [Set.indicator_of_mem hz]
      have hzi : delta < w b hb.le e z := hz
      have hw : 0 < w b hb.le e z := lt_of_le_of_lt hdelta hzi
      rw [max_eq_right (by linarith : -(w b hb.le e z) ≤ (0 : ℝ))]
      simp
    · rw [Set.indicator_of_notMem hz]
      simpa using p4Q2PZ37ACW_originalNegativePart_le_FC H b hb.le e z
  have hBound := integral_mono hNeg hEnvelope hPoint
  calc
    Eminus b hb.le e =
        (∫ z : Pair, max (-(w b hb.le e z)) 0 ∂outer) := rfl
    _ ≤ ∫ z : Pair,
        C b hb.le -
          C b hb.le * (T b hb.le e delta).indicator (fun _ => (1 : ℝ)) z
          ∂outer := hBound
    _ = C b hb.le * (1 - Measure.real outer (T b hb.le e delta)) := by
      rw [integral_sub hConst (hInd.const_mul _),
        integral_const_mul, integral_indicator_const (1 : ℝ) hMeas]
      simp
      ring

/-- Exact ACT weighted global signed budget has a locally quantified
positive-region-minus-complement lower bound under original pair-Haar. -/
theorem p4Q2PZ37ACW_originalDiscriminant_regionMass_lower
    (b : ℝ) (hb : 0 < b) (e : Link)
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    delta * Measure.real outer (T b hb.le e delta) -
        C b hb.le * (1 - Measure.real outer (T b hb.le e delta)) ≤
      D b hb.le e := by
  have hPlus :=
    p4Q2PZ37ACW_originalPositiveContribution_regionMass_lower H b hb e delta
  have hMinus :=
    p4Q2PZ37ACW_originalNegativeContribution_complementMass_upper
      H b hb e delta hdelta
  rw [p4Q2PZ37ACU_weightedDiscriminant_eq_positive_sub_negative H b hb e]
  linarith only [hPlus, hMinus]

/-- Quantitative original mean GI SQUARED certificate bound directly from
the positive original Perron threshold-region mass and its complement. -/
theorem p4Q2PZ37ACW_originalGIMeanBudget_regionMass_lower
    (b : ℝ) (hb : 0 < b) (e : Link)
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    kappa b * (
      delta * Measure.real outer (T b hb.le e delta) -
        C b hb.le * (1 - Measure.real outer (T b hb.le e delta))) ≤
      16 * Budget b hb.le e := by
  have hk := p4Q2PZ37ACP_originalGISlopeSq_pos b hb
  have hD :=
    p4Q2PZ37ACW_originalDiscriminant_regionMass_lower H b hb e delta hdelta
  calc
    _ ≤ kappa b * D b hb.le e :=
      mul_le_mul_of_nonneg_left hD hk.le
    _ = 16 * Budget b hb.le e :=
      (p4Q2PZ37ACT_originalGIMeanBudget_eq_weightedDiscriminant H b hb.le e).symm

/-- Strict positivity of the original threshold-region mass surplus
is sufficient (not established) for the true physical positive mean
GI squared certificate, without any volume-uniform lower bound. -/
theorem p4Q2PZ37ACW_originalRegionMass_surplus_gives_positiveBudget
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hSurplus :
      C b hb.le * (1 - Measure.real outer (T b hb.le e delta)) <
        delta * Measure.real outer (T b hb.le e delta)) :
    0 < Budget b hb.le e := by
  have hD :=
    p4Q2PZ37ACW_originalDiscriminant_regionMass_lower H b hb e delta hdelta
  have hDpos : 0 < D b hb.le e := by linarith only [hSurplus, hD]
  have hBalance :=
    (p4Q2PZ37ACU_weightedDiscriminant_pos_iff_positiveDominates
      H b hb e).mp hDpos
  exact (p4Q2PZ37ACU_originalGIMeanBudget_pos_iff_positiveDominates
    H b hb e).mpr hBalance

/-- A directly interpretable conditional Haar-mass threshold:
m(T_delta) > C/(C+delta), delta>0, suffices for the true positive
mean certificate. The inequality is OPEN for the original Wilson data. -/
theorem p4Q2PZ37ACW_originalRegionMass_ratio_gives_positiveBudget
    (b : ℝ) (hb : 0 < b) (e : Link)
    (delta : ℝ) (hdelta : 0 < delta)
    (hMass :
      C b hb.le / (C b hb.le + delta) <
        Measure.real outer (T b hb.le e delta)) :
    0 < Budget b hb.le e := by
  have hc := p4Q2PZ37ACW_originalNegativeFCBudget_nonneg H b hb.le
  have hDen : 0 < C b hb.le + delta := by linarith only [hc, hdelta]
  have hProduct :
      C b hb.le <
        Measure.real outer (T b hb.le e delta) * (C b hb.le + delta) :=
    (div_lt_iff₀ hDen).mp hMass
  apply p4Q2PZ37ACW_originalRegionMass_surplus_gives_positiveBudget
    H b hb e delta hdelta.le
  nlinarith only [hProduct]

/-- If the original physical mean certificate actually FAILS the
positive test, EVERY nonnegative threshold-region mass must obey the
explicit region/complement obstruction (not actual GI vanishing). -/
theorem p4Q2PZ37ACW_nonpositiveBudget_regionMass_obstruction
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpos : Budget b hb.le e ≤ 0)
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    delta * Measure.real outer (T b hb.le e delta) ≤
      C b hb.le * (1 - Measure.real outer (T b hb.le e delta)) := by
  have hFraction :=
    (p4Q2PZ37ACS_originalGIMeanBudget_nonpos_iff_fractionObstruction
      H b hb e).mp hNonpos
  have hD :=
    (p4Q2PZ37ACT_weightedDiscriminant_nonpos_iff_obstruction H b hb e).mpr
      hFraction
  have hRegion :=
    p4Q2PZ37ACW_originalDiscriminant_regionMass_lower H b hb e delta hdelta
  linarith only [hD, hRegion]

/-- Crossing the ACT/ACW true original favorable region-mass threshold
implies that the ACTUAL signed two-interacting-posterior GI response is
nonzero on an OPEN positive original pair-Haar-mass region. The trigger
is a sufficient condition on the squared certificate, not an identity
with the signed GI response. -/
theorem p4Q2PZ37ACW_originalRegionMass_surplus_gives_openGIRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hSurplus :
      C b hb.le * (1 - Measure.real outer (T b hb.le e delta)) <
        delta * Measure.real outer (T b hb.le e delta)) :
    ∃ Uset : Set Pair, IsOpen Uset ∧
      0 < Measure.real outer Uset ∧
      ∀ z ∈ Uset,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le f₀ e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    H b hb.le e
    (p4Q2PZ37ACW_originalRegionMass_surplus_gives_positiveBudget
      H b hb e delta hdelta hSurplus)

/-- Exact FC UPPER bound on the original weighted local discriminator,
using the SAME original ACO local GI squared-certificate and its
strictly positive genuine kappa(b). No favorable sign is assumed. -/
theorem p4Q2PZ37ACW_originalWeightedDiscriminant_le_FC
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Pair) :
    w b hb.le e z ≤ 4 * (B b hb.le) ^ 2 := by
  have hk := p4Q2PZ37ACP_originalGISlopeSq_pos b hb
  have hQ :=
    p4Q2PZ37ACO_originalGISquaredMargin_le_FC H b hb.le e z
  have hIdentity :=
    p4Q2PZ37ACT_localGICertificate_eq_transferDiscriminant H b hb.le e z
  have hScale : kappa b * w b hb.le e z = 16 * Q b hb.le e z := by
    unfold p4Q2PZ37ACU_weightedLocalDiscriminant
    calc
      kappa b * ((P b hb.le z) ^ 2 * d b hb.le e z) =
          kappa b * (P b hb.le z) ^ 2 * d b hb.le e z := by ring
      _ = 16 * Q b hb.le e z := hIdentity.symm
  have hBound : kappa b * w b hb.le e z ≤
      kappa b * (4 * (B b hb.le) ^ 2) := by
    rw [hScale]
    calc
      16 * Q b hb.le e z ≤
          16 * (kappa b * ((B b hb.le) ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left hQ (by norm_num)
      _ = kappa b * (4 * (B b hb.le) ^ 2) := by ring
  by_contra hNot
  have hStrict : 4 * (B b hb.le) ^ 2 < w b hb.le e z :=
    lt_of_not_ge hNot
  have hProduct := mul_lt_mul_of_pos_left hStrict hk
  exact (not_lt_of_ge hBound) hProduct

/-- When the still OPEN actual ORIGINAL mean discriminator is positive,
the Perron-weighted threshold region at half its mean is OPEN and has
an explicit ORIGINAL pair-Haar positive mass lower bound. -/
theorem p4Q2PZ37ACW_positiveMean_halfThreshold_open_mass_lower
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hD : 0 < D b hb.le e) :
    IsOpen (T b hb.le e (D b hb.le e / 2)) ∧
    0 < 2 * (4 * (B b hb.le) ^ 2) - D b hb.le e ∧
    D b hb.le e /
        (2 * (4 * (B b hb.le) ^ 2) - D b hb.le e) ≤
      Measure.real outer (T b hb.le e (D b hb.le e / 2)) := by
  have hEq : (∫ z : Pair, w b hb.le e z ∂outer) = D b hb.le e :=
    (p4Q2PZ37ACT_weightedDiscriminant_eq_integralLocal H b hb.le e).symm
  have hMean : 0 < (∫ z : Pair, w b hb.le e z ∂outer) := by
    rw [hEq]
    exact hD
  have hTail := CompactPositiveMomentTail.half_mean_upper_tail outer
    (w b hb.le e)
    (p4Q2PZ37ACU_weightedLocalDiscriminant_continuous H b hb e)
    (4 * (B b hb.le) ^ 2)
    (p4Q2PZ37ACW_originalWeightedDiscriminant_le_FC H b hb e)
    hMean
  rw [hEq] at hTail
  refine ⟨p4Q2PZ37ACW_originalThresholdRegion_isOpen H b hb e _, hTail.1, ?_⟩
  simpa only [p4Q2PZ37ACW_originalPositiveWeightThresholdRegion] using hTail.2

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalNegativeFCBudget_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalNegativePart_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalWeightedDiscriminant_ge_negFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalThresholdRegion_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalThresholdRegion_has_localFourModeDominance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalPositiveContribution_regionMass_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalNegativeContribution_complementMass_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalDiscriminant_regionMass_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalGIMeanBudget_regionMass_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalRegionMass_surplus_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalRegionMass_ratio_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_nonpositiveBudget_regionMass_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalRegionMass_surplus_gives_openGIRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_originalWeightedDiscriminant_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACW_positiveMean_halfThreshold_open_mass_lower
