import MGAP4D.MathlibAnalytic.CompactPositiveMomentTail
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOptimizedGICertificateV5_PZ37ACM

/-!
# P4-Q2-PZ37ACN — unconditional original four-mode amplitude moment regions

In the SAME original interacting Wilson SU(2) model, ACK already establishes
that each of the four physical Haar coefficients has outer square moment S.
Consequently the actual ACM squared orbit amplitude has outer mean 4*S > 0
at every finite H (including 0), positive b and chosen genuine link.

The unchanged physical FC envelope B supplies the pointwise cap A^2 <= B^2/4.
A general sharp first-moment upper-tail estimate gives an explicit lower
outer pair-Haar mass of the region A^2 > 2*S:
  4*S / (B^2/2 - 4*S).
The denominator is proved positive, not assumed.

At any such genuine configuration, the ACM joint SU(2) optimizer has
  C > sqrt(2*S),  D = W < B^2 - 8*S.
Continuity and support of the ORIGINAL outer Haar law give a positive-mass
open region satisfying BOTH strict bounds. This improves the simultaneously
usable covariance floor and residual ceiling without assuming any physical
GI positivity margin, H-uniform estimate, or alternate receiver/model.
The strict GI certificate inequality remains an unresolved actual check.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ACN_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACN_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACN_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACN_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACN_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACN_probability : IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "V" => p4Q2PZ37ACL_originalCenteredReceiverVariance H
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "m" => p4Q2PZ37ACK_originalFourModeCoefficient H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Γ" => p4Q2PZ37ACK_originalGaugePair H
local notation "q" => p4Q2PZ35B_quaternionFamily
local instance p4Q2PZ37ACN_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACN_probability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

private theorem p4Q2PZ37ACN_coefficient_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (j : Fin 4) :
    Continuous (fun z : Pair => m b hb e z j) := by
  have hEq : (fun z : Pair => m b hb e z j) =
      (fun z : Pair => -C b hb e (Γ e (q j) z)) := by
    funext z
    exact p4Q2PZ37ACK_originalFourModeCoefficient_eq_gaugeCovariance H b hb e z j
  rw [hEq]
  exact ((p4Q2PZ37ACD_originalReceiver_covariance_continuous H b hb f₀ e).comp
    (p4Q2PZ37ACK_originalGaugePair_continuous_z H e (q j))).neg

/-- The genuine finite-volume squared amplitude is continuous in both
outer configurations; no auxiliary gauge-coordinate presentation is used. -/
theorem p4Q2PZ37ACN_originalAmplitude_sq_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Continuous (fun z : Pair => (A b hb e z) ^ 2) := by
  have hEq : (fun z : Pair => (A b hb e z) ^ 2) =
      (fun z : Pair => ∑ j : Fin 4, (m b hb e z j) ^ 2) := by
    funext z
    exact p4Q2PZ37ACM_originalCovarianceAmplitude_sq H b hb e z
  rw [hEq]
  exact continuous_finset_sum _ fun j _ =>
    (p4Q2PZ37ACN_coefficient_continuous H b hb e j).pow 2

/-- Exact original outer second moment of the attainable covariance
amplitude: four genuinely equal physical coefficient moments. -/
theorem p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    (∫ z : Pair, (A b hb e z) ^ 2 ∂outer) = 4 * S b hb e := by
  have hi (j : Fin 4) : Integrable (fun z : Pair => (m b hb e z j) ^ 2) outer :=
    ((p4Q2PZ37ACN_coefficient_continuous H b hb e j).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ z : Pair, (A b hb e z) ^ 2 ∂outer) =
        ∫ z : Pair, (∑ j : Fin 4, (m b hb e z j) ^ 2) ∂outer := by
      apply integral_congr_ae
      filter_upwards with z
      exact p4Q2PZ37ACM_originalCovarianceAmplitude_sq H b hb e z
    _ = ∑ j : Fin 4, (∫ z : Pair, (m b hb e z j) ^ 2 ∂outer) := by
      rw [integral_finset_sum _ (fun j _ => hi j)]
    _ = ∑ _j : Fin 4, S b hb e := by
      apply Finset.sum_congr rfl
      intro j _
      exact p4Q2PZ37ACK_originalFourModeCoefficient_outerSquare H b hb e j
    _ = 4 * S b hb e := by simp

/-- Positive genuine squared orbit-amplitude mean at every finite volume,
positive coupling and chosen original spatial link. -/
theorem p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral_pos
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < ∫ z : Pair, (A b hb.le e z) ^ 2 ∂outer := by
  rw [p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral]
  exact mul_pos (by norm_num) (p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e)

/-- A pointwise upper bound from the original FC variance envelope and
the actual nonnegative ACK four-mode residual. -/
theorem p4Q2PZ37ACN_originalAmplitude_sq_le_FC
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    (A b hb e z) ^ 2 ≤ (B b hb) ^ 2 / 4 := by
  have hVar := p4Q2PZ37ACA_originalReceiver_variance_le_FC H b hb f₀ e z
  change V b hb e z ≤ (B b hb) ^ 2 at hVar
  have hW := p4Q2PZ37ACK_originalFourModeResidualEnergy_nonneg H b hb e z
  have hEq := p4Q2PZ37ACM_originalVariance_eq_amplitude_residual H b hb e z
  nlinarith

/-- The ACTUAL original outer high-amplitude set has a quantitative Haar
mass floor. Neither its mass nor S is replaced by an assumed constant. -/
theorem p4Q2PZ37ACN_highAmplitudeRegion_mass_lower
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < (B b hb.le) ^ 2 / 2 - 4 * S b hb.le e ∧
      (4 * S b hb.le e) / ((B b hb.le) ^ 2 / 2 - 4 * S b hb.le e) ≤
        Measure.real outer {z : Pair | 2 * S b hb.le e < (A b hb.le e z) ^ 2} := by
  have hTail := CompactPositiveMomentTail.half_mean_upper_tail outer
    (fun z : Pair => (A b hb.le e z) ^ 2)
    (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b hb.le e)
    ((B b hb.le) ^ 2 / 4)
    (p4Q2PZ37ACN_originalAmplitude_sq_le_FC H b hb.le e)
    (p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral_pos H b hb e)
  rw [p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral] at hTail
  have hDenEq :
      2 * ((B b hb.le) ^ 2 / 4) - 4 * S b hb.le e =
        (B b hb.le) ^ 2 / 2 - 4 * S b hb.le e := by ring
  have hThresholdEq : (4 * S b hb.le e) / 2 = 2 * S b hb.le e := by ring
  rw [hDenEq, hThresholdEq] at hTail
  exact hTail

/-- The positive actual amplitude moment forces a concrete high-amplitude
context, without a hypothetical favorable configuration premise. -/
theorem p4Q2PZ37ACN_exists_highAmplitude
    (b : ℝ) (hb : 0 < b) (e : Link) :
    ∃ z : Pair, 2 * S b hb.le e < (A b hb.le e z) ^ 2 := by
  have hS := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  by_contra hNo
  push Not at hNo
  have hConstI : Integrable (fun _z : Pair => 2 * S b hb.le e) outer :=
    integrable_const _
  have hI : (∫ z : Pair, (A b hb.le e z) ^ 2 ∂outer) ≤
      (∫ _z : Pair, 2 * S b hb.le e ∂outer) :=
    integral_mono
      ((p4Q2PZ37ACN_originalAmplitude_sq_continuous H b hb.le e).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      hConstI hNo
  have hConst : (∫ _z : Pair, 2 * S b hb.le e ∂outer) = 2 * S b hb.le e := by
    simp
  rw [p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral, hConst] at hI
  linarith

/-- Unconditional SAME-context selected region:
a positive covariance floor sqrt(2*S) AND an improved residual ceiling
B^2-8*S hold on one nonempty open set of positive original outer Haar mass.
No GI sign or strict certificate is assumed or concluded. -/
theorem p4Q2PZ37ACN_strongSelectedRegion_mass_pos
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < Measure.real outer {w : Pair |
      Real.sqrt (2 * S b hb.le e) < C b hb.le e w ∧
        p4Q2PZ37ACL_originalCenteredRegressionDefect H b hb.le e w <
          (B b hb.le) ^ 2 - 8 * S b hb.le e} := by
  obtain ⟨z, hz⟩ := p4Q2PZ37ACN_exists_highAmplitude H b hb e
  have hS := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hA := p4Q2PZ37ACM_originalCovarianceAmplitude_nonneg H b hb.le e z
  have hRoot : (Real.sqrt (2 * S b hb.le e)) ^ 2 = 2 * S b hb.le e :=
    Real.sq_sqrt (by positivity)
  have hc : Real.sqrt (2 * S b hb.le e) < A b hb.le e z := by
    nlinarith [Real.sqrt_nonneg (2 * S b hb.le e)]
  have hV := p4Q2PZ37ACA_originalReceiver_variance_le_FC H b hb.le f₀ e z
  change V b hb.le e z ≤ (B b hb.le) ^ 2 at hV
  have hEq := p4Q2PZ37ACM_originalVariance_eq_amplitude_residual H b hb.le e z
  have hd : W b hb.le e z < (B b hb.le) ^ 2 - 8 * S b hb.le e := by
    nlinarith
  exact p4Q2PZ37ACM_selectedRegion_mass_pos H b hb.le e z
    (Real.sqrt (2 * S b hb.le e))
    ((B b hb.le) ^ 2 - 8 * S b hb.le e) hc hd

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACN_originalAmplitude_sq_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACN_originalAmplitude_sq_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACN_highAmplitudeRegion_mass_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACN_exists_highAmplitude
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACN_strongSelectedRegion_mass_pos
