import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalThresholdRegionMassBalanceV5_PZ37ACW

/-!
# P4-Q2-PZ37ACX — original Perron threshold-mass profile from physical moments

Append-only, SAME finite interacting Wilson SU(2) receiver, centered
Gauss-law physical source, positive ground-state Perron representative,
updated transfer section U_z, interacting posterior pair, and original
boundary pair-Haar law. No new receiver, Haar independence, or weakening.

ACT–ACW give the TRUE Perron-weighted local spectral discriminator
  w(z)=P_z²*(16 A_U(z)²-tau(b)*W_U(z)),
  D=integral w=64*S-tau(b)*Wbar,
and the genuine ORIGINAL receiver FC caps
  -C <= w(z) <= U, C=tau(b)*B², U=4*B².
For EVERY real delta and threshold T_delta={z:delta<w(z)}, ACX proves
  -C+(delta+C)*nu_H(T_delta) <= D
  D <= delta+(U-delta)*nu_H(T_delta).
For 0<delta<U, the actual pair-Haar mass has sharp two-sided bounds
  (D-delta)/(U-delta) <= nu_H(T_delta) <= (D+C)/(delta+C).
No independence, a.e.-only source substitution, or new variance floor.

Moreover actual higher Haar residual mean obeys Wbar<=B², hence
  64*S-tau(b)*B² <= D.
Thus if delta < 64*S-tau(b)*B², a directly ORIGINAL physical-moment
lower bound on nu_H(T_delta) is established, and the strict positive
Haar mass yields a true favorable updated-transfer boundary witness.
The condition is not asserted to hold for the physical Wilson data.
If the ACO positive mean GI squared CERTIFICATE fails, the exact
threshold mass obstruction is nu_H(T_delta)<=C/(C+delta), delta>0.

We never identify the squared certificate with actual signed two-posterior
GI response, and assert no uniform H estimate or continuum 4D mass gap.
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
local instance p4Q2PZ37ACX_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACX_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACX_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACX_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACX_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACX_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local notation "tA2" => p4Q2PZ37ACQ_transferAmplitudeSq H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "tau" => p4Q2PZ37ACP_originalPosteriorExponentGapSq
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "D" => p4Q2PZ37ACT_originalWeightedTransferDiscriminant H
local notation "d" => p4Q2PZ37ACT_originalTransferLocalDiscriminant H
local notation "w" => p4Q2PZ37ACU_weightedLocalDiscriminant H
local notation "C" => p4Q2PZ37ACW_originalNegativeFCBudget H
local notation "T" => p4Q2PZ37ACW_originalPositiveWeightThresholdRegion H
local instance p4Q2PZ37ACX_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACX_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The ORIGINAL Wilson receiver gives a uniform-in-boundary (not H)
FC cap on its true Perron-weighted discriminator, at this fixed b,H. -/
def p4Q2PZ37ACX_originalPositiveFCBudget
    (b : ℝ) (hb : 0 ≤ b) : ℝ :=
  4 * (B b hb) ^ 2
local notation "Ucap" => p4Q2PZ37ACX_originalPositiveFCBudget H

/-- A direct ORIGINAL physical-moment lower test with no guessed
higher-character cancellation: 64*S-tau*B². -/
def p4Q2PZ37ACX_originalMomentFCFloor
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  64 * S b hb e - C b hb
local notation "L" => p4Q2PZ37ACX_originalMomentFCFloor H

/-- The actual ORIGINAL positive FC cap for w is just the ACO/ACW cap,
not an invented transfer-section norm inequality. -/
theorem p4Q2PZ37ACX_originalWeightedDiscriminant_le_positiveFC
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Pair) :
    w b hb.le e z ≤ Ucap b hb.le := by
  exact p4Q2PZ37ACW_originalWeightedDiscriminant_le_FC H b hb e z

/-- Upper affine envelope on the TRUE threshold distribution.
For every delta, no positivity premise on D or uniform Perron floor. -/
theorem p4Q2PZ37ACX_originalThresholdMass_upperAffine
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ) :
    D b hb.le e ≤
      delta + (Ucap b hb.le - delta) *
        Measure.real outer (T b hb.le e delta) := by
  have hMeas : MeasurableSet (T b hb.le e delta) :=
    (p4Q2PZ37ACW_originalThresholdRegion_isOpen H b hb e delta).measurableSet
  have hInd : Integrable
      ((T b hb.le e delta).indicator (fun _ : Pair => (1 : ℝ))) outer :=
    (integrable_const _).indicator hMeas
  have hW : Integrable (w b hb.le e) outer :=
    (p4Q2PZ37ACU_weightedLocalDiscriminant_continuous H b hb e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hUpperI : Integrable
      (fun z : Pair =>
        delta + (Ucap b hb.le - delta) *
          (T b hb.le e delta).indicator (fun _ : Pair => (1 : ℝ)) z) outer :=
    (integrable_const _).add (hInd.const_mul _)
  have hPoint (z : Pair) :
      w b hb.le e z ≤
        delta + (Ucap b hb.le - delta) *
          (T b hb.le e delta).indicator (fun _ : Pair => (1 : ℝ)) z := by
    by_cases hz : z ∈ T b hb.le e delta
    · rw [Set.indicator_of_mem hz]
      have hCap :=
        p4Q2PZ37ACX_originalWeightedDiscriminant_le_positiveFC H b hb e z
      simp only [mul_one]
      linarith only [hCap]
    · rw [Set.indicator_of_notMem hz]
      have hNot : w b hb.le e z ≤ delta := le_of_not_gt hz
      simpa using hNot
  calc
    D b hb.le e = (∫ z : Pair, w b hb.le e z ∂outer) :=
      p4Q2PZ37ACT_weightedDiscriminant_eq_integralLocal H b hb.le e
    _ ≤ ∫ z : Pair,
          delta + (Ucap b hb.le - delta) *
            (T b hb.le e delta).indicator (fun _ : Pair => (1 : ℝ)) z
          ∂outer := integral_mono hW hUpperI hPoint
    _ = delta + (Ucap b hb.le - delta) *
          Measure.real outer (T b hb.le e delta) := by
      rw [integral_add (integrable_const _) (hInd.const_mul _),
        integral_const_mul, integral_indicator_const (1 : ℝ) hMeas]
      simp

/-- Symmetric LOWER affine envelope: on the true favorable boundary
region w>delta, outside it w>=-tau B², with SAME Perron weight. -/
theorem p4Q2PZ37ACX_originalThresholdMass_lowerAffine
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ) :
    -C b hb.le + (delta + C b hb.le) *
        Measure.real outer (T b hb.le e delta) ≤ D b hb.le e := by
  have hMeas : MeasurableSet (T b hb.le e delta) :=
    (p4Q2PZ37ACW_originalThresholdRegion_isOpen H b hb e delta).measurableSet
  have hInd : Integrable
      ((T b hb.le e delta).indicator (fun _ : Pair => (1 : ℝ))) outer :=
    (integrable_const _).indicator hMeas
  have hW : Integrable (w b hb.le e) outer :=
    (p4Q2PZ37ACU_weightedLocalDiscriminant_continuous H b hb e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLowerI : Integrable
      (fun z : Pair =>
        -C b hb.le + (delta + C b hb.le) *
          (T b hb.le e delta).indicator (fun _ : Pair => (1 : ℝ)) z) outer :=
    (integrable_const _).add (hInd.const_mul _)
  have hPoint (z : Pair) :
      -C b hb.le + (delta + C b hb.le) *
          (T b hb.le e delta).indicator (fun _ : Pair => (1 : ℝ)) z ≤
        w b hb.le e z := by
    by_cases hz : z ∈ T b hb.le e delta
    · rw [Set.indicator_of_mem hz]
      have hActual : delta < w b hb.le e z := hz
      simp only [mul_one]
      linarith only [hActual]
    · rw [Set.indicator_of_notMem hz]
      have hFloor :=
        p4Q2PZ37ACW_originalWeightedDiscriminant_ge_negFC H b hb.le e z
      simpa using hFloor
  calc
    -C b hb.le + (delta + C b hb.le) *
        Measure.real outer (T b hb.le e delta) =
        (∫ z : Pair,
          -C b hb.le + (delta + C b hb.le) *
            (T b hb.le e delta).indicator (fun _ : Pair => (1 : ℝ)) z
          ∂outer) := by
      rw [integral_add (integrable_const _) (hInd.const_mul _),
        integral_const_mul, integral_indicator_const (1 : ℝ) hMeas]
      simp
    _ ≤ (∫ z : Pair, w b hb.le e z ∂outer) :=
      integral_mono hLowerI hW hPoint
    _ = D b hb.le e :=
      (p4Q2PZ37ACT_weightedDiscriminant_eq_integralLocal H b hb.le e).symm

/-- Original bounded weighted-discriminator mean cannot exceed its
true original Wilson receiver's same-b,H FC envelope. -/
theorem p4Q2PZ37ACX_originalMeanDiscriminant_le_FC
    (b : ℝ) (hb : 0 < b) (e : Link) :
    D b hb.le e ≤ Ucap b hb.le := by
  have h := p4Q2PZ37ACX_originalThresholdMass_upperAffine
    H b hb e (Ucap b hb.le)
  simpa only [sub_self, zero_mul, add_zero] using h

/-- Sharp finite-volume ORIGINAL pair-Haar lower threshold profile,
using only the true mean D and the genuine receiver upper FC cap. -/
theorem p4Q2PZ37ACX_originalThresholdMass_lower_of_delta_lt_cap
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (hDelta : delta < Ucap b hb.le) :
    (D b hb.le e - delta) / (Ucap b hb.le - delta) ≤
      Measure.real outer (T b hb.le e delta) := by
  have hDen : 0 < Ucap b hb.le - delta := sub_pos.mpr hDelta
  have hBound :=
    p4Q2PZ37ACX_originalThresholdMass_upperAffine H b hb e delta
  apply (div_le_iff₀ hDen).mpr
  linarith only [hBound]

/-- At any positive threshold the original pair-Haar tail has an
UPPER profile from the true negative FC budget and actual mean. -/
theorem p4Q2PZ37ACX_originalThresholdMass_upper_of_delta_pos
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (hDelta : 0 < delta) :
    Measure.real outer (T b hb.le e delta) ≤
      (D b hb.le e + C b hb.le) / (delta + C b hb.le) := by
  have hc := p4Q2PZ37ACW_originalNegativeFCBudget_nonneg H b hb.le
  have hDen : 0 < delta + C b hb.le := by linarith only [hc, hDelta]
  have hBound :=
    p4Q2PZ37ACX_originalThresholdMass_lowerAffine H b hb e delta
  apply (le_div_iff₀ hDen).mpr
  linarith only [hBound]

/-- Two-sided exact finite-volume Haar threshold MASS bracket:
the true original Perron spectrum, not any surrogate Haar receiver. -/
theorem p4Q2PZ37ACX_originalThresholdMass_twoSided
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (hDelta : 0 < delta) (hCap : delta < Ucap b hb.le) :
    (D b hb.le e - delta) / (Ucap b hb.le - delta) ≤
        Measure.real outer (T b hb.le e delta) ∧
      Measure.real outer (T b hb.le e delta) ≤
        (D b hb.le e + C b hb.le) / (delta + C b hb.le) := by
  exact ⟨p4Q2PZ37ACX_originalThresholdMass_lower_of_delta_lt_cap
    H b hb e delta hCap,
    p4Q2PZ37ACX_originalThresholdMass_upper_of_delta_pos
      H b hb e delta hDelta⟩

/-- A verified mean spectral margin D>delta forces a genuine open,
positive-PAIR-Haar-mass original boundary threshold region. -/
theorem p4Q2PZ37ACX_originalMeanExceedsThreshold_open_positiveMass
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (hAbove : delta < D b hb.le e) :
    IsOpen (T b hb.le e delta) ∧
      0 < Measure.real outer (T b hb.le e delta) := by
  have hMeanCap := p4Q2PZ37ACX_originalMeanDiscriminant_le_FC H b hb e
  have hCap : delta < Ucap b hb.le := lt_of_lt_of_le hAbove hMeanCap
  have hFloor := p4Q2PZ37ACX_originalThresholdMass_lower_of_delta_lt_cap
    H b hb e delta hCap
  have hDen : 0 < Ucap b hb.le - delta := sub_pos.mpr hCap
  have hNumer : 0 < (D b hb.le e - delta) /
      (Ucap b hb.le - delta) :=
    div_pos (sub_pos.mpr hAbove) hDen
  exact ⟨p4Q2PZ37ACW_originalThresholdRegion_isOpen H b hb e delta,
    hNumer.trans_le hFloor⟩

/-- The same mean margin at a nonnegative threshold gives an ACTUAL
updated-transfer boundary with nonzero first-four Haar signal. -/
theorem p4Q2PZ37ACX_originalMeanExceedsThreshold_has_transferWitness
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (hDelta : 0 ≤ delta) (hAbove : delta < D b hb.le e) :
    ∃ z : Pair, z ∈ T b hb.le e delta ∧
      0 < d b hb.le e z ∧ 0 < tA2 b hb.le e z := by
  have hMass :=
    (p4Q2PZ37ACX_originalMeanExceedsThreshold_open_positiveMass
      H b hb e delta hAbove).2
  have hNonempty : (T b hb.le e delta).Nonempty := by
    by_contra hn
    have hEmpty : T b hb.le e delta = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hn
    simp [hEmpty] at hMass
  obtain ⟨z, hz⟩ := hNonempty
  obtain ⟨hd, ha⟩ :=
    p4Q2PZ37ACW_originalThresholdRegion_has_localFourModeDominance
      H b hb e delta hDelta z hz
  exact ⟨z, hz, hd, ha⟩

/-- The actual higher-character SU(2) Haar remainder MEAN cannot exceed
the ORIGINAL FF receiver's previously certified finite-volume FC cap. -/
theorem p4Q2PZ37ACX_originalResidualMoment_le_FC
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Wbar b hb e ≤ (B b hb) ^ 2 := by
  change (∫ z : Pair, W b hb e z ∂outer) ≤ (B b hb) ^ 2
  have hI : Integrable (W b hb e) outer :=
    (p4Q2PZ37ACR_originalResidual_continuous H b hb e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ z : Pair, W b hb e z ∂outer) ≤
        ∫ _z : Pair, (B b hb) ^ 2 ∂outer :=
      integral_mono hI (integrable_const _)
        (p4Q2PZ37ACR_originalResidual_le_FC H b hb e)
    _ = (B b hb) ^ 2 := by simp

/-- Physical no-new-assumption MOMENT floor for actual GI signed
discriminator: use original covariance S>0, true posterior tau and FC. -/
theorem p4Q2PZ37ACX_originalDiscriminant_ge_explicitMomentFloor
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    L b hb e ≤ D b hb e := by
  have ht : 0 ≤ tau b := sq_nonneg _
  have hw := p4Q2PZ37ACX_originalResidualMoment_le_FC H b hb e
  have hProd := mul_le_mul_of_nonneg_left hw ht
  rw [p4Q2PZ37ACT_weightedDiscriminant_eq_originalMoments H b hb e]
  unfold p4Q2PZ37ACX_originalMomentFCFloor
    p4Q2PZ37ACW_originalNegativeFCBudget
  linarith only [hProd]

/-- Explicit true ORIGINAL physical inputs S,tau,B already force a
Haar mass lower bound whenever delta is below the actual proven moment
floor. This does not assume or invent an H-uniform spectral floor. -/
theorem p4Q2PZ37ACX_originalThresholdMass_lower_from_physicalMoments
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (hFloor : delta < L b hb.le e) :
    (L b hb.le e - delta) / (Ucap b hb.le - delta) ≤
      Measure.real outer (T b hb.le e delta) := by
  have hLD := p4Q2PZ37ACX_originalDiscriminant_ge_explicitMomentFloor
    H b hb.le e
  have hDU := p4Q2PZ37ACX_originalMeanDiscriminant_le_FC H b hb e
  have hDelta : delta < Ucap b hb.le := lt_of_lt_of_le
    (lt_of_lt_of_le hFloor hLD) hDU
  have hDen : 0 < Ucap b hb.le - delta := sub_pos.mpr hDelta
  have hAffine := p4Q2PZ37ACX_originalThresholdMass_upperAffine
    H b hb e delta
  apply (div_le_iff₀ hDen).mpr
  linarith only [hLD, hAffine]

/-- Under an actual certified source/FC-moment gap, the original
threshold region necessarily has positive true pair-Haar mass. -/
theorem p4Q2PZ37ACX_originalPhysicalMomentFloor_forces_positiveMass
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (hFloor : delta < L b hb.le e) :
    0 < Measure.real outer (T b hb.le e delta) := by
  have hLD := p4Q2PZ37ACX_originalDiscriminant_ge_explicitMomentFloor
    H b hb.le e
  exact (p4Q2PZ37ACX_originalMeanExceedsThreshold_open_positiveMass
    H b hb e delta (lt_of_lt_of_le hFloor hLD)).2

/-- NO-GO on the positive-mean squared GI certificate converts directly
to a sharp UPPER bound on every positive-threshold original pair-Haar
mass, with no new physical estimate whatsoever. -/
theorem p4Q2PZ37ACX_nonpositiveBudget_thresholdMass_upper
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (hDelta : 0 < delta)
    (hNonpos : Budget b hb.le e ≤ 0) :
    Measure.real outer (T b hb.le e delta) ≤
      C b hb.le / (delta + C b hb.le) := by
  have hc := p4Q2PZ37ACW_originalNegativeFCBudget_nonneg H b hb.le
  have hDen : 0 < delta + C b hb.le := by linarith only [hc, hDelta]
  have hReg :=
    p4Q2PZ37ACW_nonpositiveBudget_regionMass_obstruction
      H b hb e hNonpos delta hDelta.le
  apply (le_div_iff₀ hDen).mpr
  nlinarith only [hReg]

/-- A failure of the actual mean certificate forces the explicit
original source covariance to fit INSIDE the physical FC residual cap.
This is an obstruction on the SAME original Wilson data, not GI vanishing. -/
theorem p4Q2PZ37ACX_nonpositiveBudget_forces_originalMomentObstruction
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpos : Budget b hb.le e ≤ 0) :
    64 * S b hb.le e ≤ C b hb.le := by
  have hFraction :=
    (p4Q2PZ37ACS_originalGIMeanBudget_nonpos_iff_fractionObstruction
      H b hb e).mp hNonpos
  have hD :=
    (p4Q2PZ37ACT_weightedDiscriminant_nonpos_iff_obstruction H b hb e).mpr
      hFraction
  have hLD := p4Q2PZ37ACX_originalDiscriminant_ge_explicitMomentFloor
    H b hb.le e
  unfold p4Q2PZ37ACX_originalMomentFCFloor at hLD
  linarith only [hD, hLD]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalWeightedDiscriminant_le_positiveFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalThresholdMass_upperAffine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalThresholdMass_lowerAffine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalMeanDiscriminant_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalThresholdMass_lower_of_delta_lt_cap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalThresholdMass_upper_of_delta_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalThresholdMass_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalMeanExceedsThreshold_open_positiveMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalMeanExceedsThreshold_has_transferWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalResidualMoment_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalDiscriminant_ge_explicitMomentFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalThresholdMass_lower_from_physicalMoments
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_originalPhysicalMomentFloor_forces_positiveMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_nonpositiveBudget_thresholdMass_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACX_nonpositiveBudget_forces_originalMomentObstruction
