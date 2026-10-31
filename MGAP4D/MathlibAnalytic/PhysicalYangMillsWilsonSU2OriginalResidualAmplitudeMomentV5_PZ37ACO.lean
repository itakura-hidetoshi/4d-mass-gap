import MGAP4D.MathlibAnalytic.CompactPositiveMeanRelativeResidual
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAmplitudeMomentRegionsV5_PZ37ACN

/-!
# P4-Q2-PZ37ACO — genuine same-context amplitude/residual ratio and GI budget

For the original interacting Wilson SU(2) model, preserve the SAME centered
Gauss-law physical source, FF receiver, positive Perron representative,
transfer norm, genuine two-posterior GI and original outer pair-Haar measure.

Write S = E_outer[C^2] > 0, A^2 = sum of four ACK coefficients squared,
W(z) = actual orthogonal four-mode residual, and Wbar = E_outer[W].
ACK/ACN prove E_outer[A^2] = 4*S > 0 and Wbar >= 0.
For every epsilon > 0 an actual original region has positive Haar mass and
  4*S*W(z) < (Wbar+epsilon)*A(z)^2;
even its stronger half-mean-margin region has an explicit quantitative
Haar-mass floor from the physical FC cap B.

For the original ACM GI certificate let kappa(b) =
(2*b*exp(-32*b))^2 and rho(b) the genuine ACI posterior error envelope.
The exact mean of the actual squared GI orbit margin is
  E_outer[kappa*A^2-rho*W] = 4*S*kappa-rho*Wbar.
If this ACTUAL observed mean is strictly positive, a quantitative
positive-Haar mass of favorable orbit-margin configurations and a positive
original GI certificate region follow. This budget inequality remains an
OPEN PHYSICAL OBLIGATION. Nothing in this file assumes it is satisfied.

No volume-uniform constants, all-context GI, support-cylinder, H1-H4,
continuum reconstruction or Yang-Mills mass gap is inferred.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ACO_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACO_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACO_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACO_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACO_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACO_probability : IsProbabilityMeasure (normalizedCompactHaar G) :=
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
local notation "D" => p4Q2PZ37ACL_originalCenteredRegressionDefect H
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Γ" => p4Q2PZ37ACK_originalGaugePair H
local notation "L" => p4Q2PZ37ACM_originalGICertificate H
local notation "rho" => p4Q2PZ37ACI_originalPosteriorResidualEnvelope
local instance p4Q2PZ37ACO_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACO_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

private theorem p4Q2PZ37ACO_residual_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Continuous (fun z : Pair => W b hb e z) := by
  have hEq : (fun z : Pair => W b hb e z) =
      (fun z : Pair => V b hb e z - 4 * (A b hb e z) ^ 2) := by
    funext z
    have h := p4Q2PZ37ACM_originalVariance_eq_amplitude_residual H b hb e z
    linarith
  rw [hEq]
  have hV : Continuous (V b hb e) :=
    p4Q2PZ37ACD_originalReceiver_variance_continuous H b hb f₀ e
  exact hV.sub (continuous_const.mul
    (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b hb e))

/-- Actual residual/signal comparison at every finite H and positive b,
with NO favorable GI certificate premise. The mean is exactly 4*S*epsilon. -/
theorem p4Q2PZ37ACO_originalRelativeMargin_integral
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (epsilon : ℝ) :
    (∫ z : Pair,
      (Wbar b hb e + epsilon) * (A b hb e z) ^ 2 -
        (4 * S b hb e) * W b hb e z ∂outer) =
      (4 * S b hb e) * epsilon := by
  have ht := CompactPositiveMeanRelativeResidual.adjustedMargin_integral outer
    (fun z : Pair => (A b hb e z) ^ 2) (fun z : Pair => W b hb e z)
    (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b hb e)
    (p4Q2PZ37ACO_residual_continuous H b hb e) epsilon
  rw [p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral] at ht
  change (∫ z : Pair,
      (Wbar b hb e + epsilon) * (A b hb e z) ^ 2 -
        (4 * S b hb e) * W b hb e z ∂outer) =
        epsilon * (4 * S b hb e) at ht
  calc
    _ = epsilon * (4 * S b hb e) := ht
    _ = (4 * S b hb e) * epsilon := by ring

/-- An explicit positive original-Haar floor for the high relaxed
signal/residual ratio event at every epsilon>0, with no unproved ratio
assumption and no volume-uniform substitute for the actual S,B,Wbar. -/
theorem p4Q2PZ37ACO_originalRelativeMargin_tail
    (b : ℝ) (hb : 0 < b) (e : Link)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    0 < 2 * (Wbar b hb.le e + epsilon) * ((B b hb.le) ^ 2 / 4) -
        epsilon * (4 * S b hb.le e) ∧
      (epsilon * (4 * S b hb.le e)) /
        (2 * (Wbar b hb.le e + epsilon) * ((B b hb.le) ^ 2 / 4) -
          epsilon * (4 * S b hb.le e)) ≤
        Measure.real outer {z : Pair |
          epsilon * (4 * S b hb.le e) / 2 <
            (Wbar b hb.le e + epsilon) * (A b hb.le e z) ^ 2 -
              (4 * S b hb.le e) * W b hb.le e z} := by
  have ht := CompactPositiveMeanRelativeResidual.adjustedMargin_half_mean_tail outer
    (fun z : Pair => (A b hb.le e z) ^ 2)
    (fun z : Pair => W b hb.le e z)
    (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b hb.le e)
    (p4Q2PZ37ACO_residual_continuous H b hb.le e)
    ((B b hb.le) ^ 2 / 4)
    (p4Q2PZ37ACN_originalAmplitude_sq_le_FC H b hb.le e)
    (p4Q2PZ37ACK_originalFourModeResidualEnergy_nonneg H b hb.le e)
    (p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral_pos H b hb e)
    epsilon hepsilon
  rw [p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral] at ht
  change 0 < 2 * (Wbar b hb.le e + epsilon) * ((B b hb.le) ^ 2 / 4) -
        epsilon * (4 * S b hb.le e) ∧
      (epsilon * (4 * S b hb.le e)) /
        (2 * (Wbar b hb.le e + epsilon) * ((B b hb.le) ^ 2 / 4) -
          epsilon * (4 * S b hb.le e)) ≤
        Measure.real outer {z : Pair |
          epsilon * (4 * S b hb.le e) / 2 <
            (Wbar b hb.le e + epsilon) * (A b hb.le e z) ^ 2 -
              (4 * S b hb.le e) * W b hb.le e z} at ht
  exact ht

/-- The same quantitatively bounded original region has strictly
positive mass. The optimized orbit is not presumed to have positive mass. -/
theorem p4Q2PZ37ACO_originalRelativeMargin_region_mass_pos
    (b : ℝ) (hb : 0 < b) (e : Link)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    0 < Measure.real outer {z : Pair |
      epsilon * (4 * S b hb.le e) / 2 <
        (Wbar b hb.le e + epsilon) * (A b hb.le e z) ^ 2 -
          (4 * S b hb.le e) * W b hb.le e z} := by
  have h := p4Q2PZ37ACO_originalRelativeMargin_tail H b hb e epsilon hepsilon
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hNum : 0 < epsilon * (4 * S b hb.le e) :=
    mul_pos hepsilon (mul_pos (by norm_num) hs)
  exact (div_pos hNum h.1).trans_le h.2

/-- The relaxed ratio region is genuinely open in the original outer
configuration topology (in addition to having positive measured mass). -/
theorem p4Q2PZ37ACO_originalRelativeMargin_region_isOpen
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (epsilon : ℝ) :
    IsOpen {z : Pair |
      epsilon * (4 * S b hb e) / 2 <
        (Wbar b hb e + epsilon) * (A b hb e z) ^ 2 -
          (4 * S b hb e) * W b hb e z} := by
  have hc : Continuous (fun z : Pair =>
      (Wbar b hb e + epsilon) * (A b hb e z) ^ 2 -
        (4 * S b hb e) * W b hb e z) :=
    (continuous_const.mul
      (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b hb e)).sub
      (continuous_const.mul (p4Q2PZ37ACO_residual_continuous H b hb e))
  exact isOpen_lt continuous_const hc

/-- The same actual physical configuration has positive orbit amplitude
and W/A^2 bounded by its genuine outer mean ratio plus any epsilon.
The strict statement avoids dividing by a possibly zero pointwise A. -/
theorem p4Q2PZ37ACO_exists_sameContext_relativeResidual
    (b : ℝ) (hb : 0 < b) (e : Link)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ z : Pair, 0 < A b hb.le e z ∧
      (4 * S b hb.le e) * W b hb.le e z <
        (Wbar b hb.le e + epsilon) * (A b hb.le e z) ^ 2 := by
  have hmass :=
    p4Q2PZ37ACO_originalRelativeMargin_region_mass_pos H b hb e epsilon hepsilon
  let U : Set Pair := {z |
    epsilon * (4 * S b hb.le e) / 2 <
      (Wbar b hb.le e + epsilon) * (A b hb.le e z) ^ 2 -
        (4 * S b hb.le e) * W b hb.le e z}
  have hne : U.Nonempty := by
    by_contra hn
    have hempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    change 0 < Measure.real outer U at hmass
    simp [hempty] at hmass
  obtain ⟨z, hz⟩ := hne
  change epsilon * (4 * S b hb.le e) / 2 <
    (Wbar b hb.le e + epsilon) * (A b hb.le e z) ^ 2 -
      (4 * S b hb.le e) * W b hb.le e z at hz
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hW := p4Q2PZ37ACK_originalFourModeResidualEnergy_nonneg H b hb.le e z
  have hNum : 0 < epsilon * (4 * S b hb.le e) :=
    mul_pos hepsilon (mul_pos (by norm_num) hs)
  have hMargin : 0 <
      (Wbar b hb.le e + epsilon) * (A b hb.le e z) ^ 2 -
        (4 * S b hb.le e) * W b hb.le e z :=
    (half_pos hNum).trans hz
  have hAmpSq : 0 < (A b hb.le e z) ^ 2 := by
    by_contra hzero
    have hsqzero : (A b hb.le e z) ^ 2 = 0 :=
      le_antisymm (le_of_not_gt hzero) (sq_nonneg _)
    rw [hsqzero, mul_zero, zero_sub] at hMargin
    have hres : 0 ≤ (4 * S b hb.le e) * W b hb.le e z :=
      mul_nonneg (mul_nonneg (by norm_num) hs.le) hW
    linarith
  have hAmp : 0 < A b hb.le e z := by
    have hnonneg := p4Q2PZ37ACM_originalCovarianceAmplitude_nonneg H b hb.le e z
    nlinarith
  exact ⟨z, hAmp, sub_pos.mp hMargin⟩

/-- The exact actual ACM GI coefficient, squared, retaining original b. -/
def p4Q2PZ37ACO_originalGISlopeSq (b : ℝ) : ℝ :=
  (2 * b * Real.exp (-32 * b)) ^ 2
local notation "kappa" => p4Q2PZ37ACO_originalGISlopeSq

/-- Unconditional pointwise squared GI certificate margin, not GI itself. -/
def p4Q2PZ37ACO_originalGISquaredMargin
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  kappa b * (A b hb e z) ^ 2 - rho b * W b hb e z
local notation "Q" => p4Q2PZ37ACO_originalGISquaredMargin H

/-- Exact actual outer mean of the squared GI orbit margin; this real
number is NOT asserted to be positive for the original Wilson receiver. -/
def p4Q2PZ37ACO_originalGIMeanBudget
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  (4 * S b hb e) * kappa b - rho b * Wbar b hb e
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H

/-- Exact signal-minus-residual averaged GI budget for the unchanged
interacting model and genuine two-posterior error envelope. -/
theorem p4Q2PZ37ACO_originalGIMeanBudget_integral
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    (∫ z : Pair, Q b hb e z ∂outer) = Budget b hb e := by
  have hA : Integrable (fun z : Pair => (A b hb e z) ^ 2) outer :=
    (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b hb e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hW : Integrable (fun z : Pair => W b hb e z) outer :=
    (p4Q2PZ37ACO_residual_continuous H b hb e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold p4Q2PZ37ACO_originalGISquaredMargin
    p4Q2PZ37ACO_originalGIMeanBudget
  rw [integral_sub (hA.const_mul _) (hW.const_mul _),
    integral_const_mul, integral_const_mul,
    p4Q2PZ37ACN_originalAmplitude_sq_outerIntegral]
  change kappa b * (4 * S b hb e) - rho b * Wbar b hb e =
    (4 * S b hb e) * kappa b - rho b * Wbar b hb e
  ring

/-- The squared GI margin is continuous under the SAME original outer law. -/
theorem p4Q2PZ37ACO_originalGISquaredMargin_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Continuous (Q b hb e) := by
  unfold p4Q2PZ37ACO_originalGISquaredMargin
  exact (continuous_const.mul
    (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b hb e)).sub
    (continuous_const.mul (p4Q2PZ37ACO_residual_continuous H b hb e))

/-- The unchanged FC cap also controls the true squared GI margin
above, without assuming positivity or favorable cancellation. -/
theorem p4Q2PZ37ACO_originalGISquaredMargin_le_FC
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    Q b hb e z ≤ kappa b * ((B b hb) ^ 2 / 4) := by
  have hk : 0 ≤ kappa b := sq_nonneg _
  have hrho := p4Q2PZ37ACI_originalPosteriorResidualEnvelope_nonneg b
  have hW := p4Q2PZ37ACK_originalFourModeResidualEnergy_nonneg H b hb e z
  have hA := p4Q2PZ37ACN_originalAmplitude_sq_le_FC H b hb e z
  change kappa b * (A b hb e z) ^ 2 - rho b * W b hb e z ≤
    kappa b * ((B b hb) ^ 2 / 4)
  exact (sub_le_self _ (mul_nonneg hrho hW)).trans
    (mul_le_mul_of_nonneg_left hA hk)

/-- Conditional but quantitative: IF the actual original mean budget is
positive, an explicit original-Haar mass of squared-GI-favorable orbits
is forced. The budget premise has not been discharged. -/
theorem p4Q2PZ37ACO_originalGIBudget_tail
    (b : ℝ) (hb : 0 ≤ b) (e : Link)
    (hBudget : 0 < Budget b hb e) :
    0 < 2 * (kappa b * ((B b hb) ^ 2 / 4)) - Budget b hb e ∧
      Budget b hb e /
        (2 * (kappa b * ((B b hb) ^ 2 / 4)) - Budget b hb e) ≤
        Measure.real outer {z : Pair | Budget b hb e / 2 < Q b hb e z} := by
  have hMean : 0 < ∫ z : Pair, Q b hb e z ∂outer := by
    rw [p4Q2PZ37ACO_originalGIMeanBudget_integral]
    exact hBudget
  have ht := CompactPositiveMomentTail.half_mean_upper_tail outer
    (Q b hb e)
    (p4Q2PZ37ACO_originalGISquaredMargin_continuous H b hb e)
    (kappa b * ((B b hb) ^ 2 / 4))
    (p4Q2PZ37ACO_originalGISquaredMargin_le_FC H b hb e) hMean
  rw [p4Q2PZ37ACO_originalGIMeanBudget_integral] at ht
  exact ht

/-- The physical budget positivity, IF established, forces a genuine
orbit with strict original GI certificate by the exact ACM equivalence.
No independent-Haar or surrogate signed receiver is substituted. -/
theorem p4Q2PZ37ACO_originalGIBudget_gives_orbitCertificate
    (b : ℝ) (hb : 0 ≤ b) (e : Link)
    (hBudget : 0 < Budget b hb e) :
    ∃ z : Pair, ∃ a : G, 0 < L b hb e (Γ e a z) := by
  by_contra hNo
  have hNonpos (z : Pair) : Q b hb e z ≤ 0 := by
    by_contra hQ
    have hQpos : 0 < Q b hb e z := lt_of_not_ge hQ
    have hPow : kappa b * (A b hb e z) ^ 2 =
        (2 * b * Real.exp (-32 * b) * A b hb e z) ^ 2 := by
      unfold p4Q2PZ37ACO_originalGISlopeSq
      ring
    have hCriterion :
        W b hb e z * rho b <
          (2 * b * Real.exp (-32 * b) * A b hb e z) ^ 2 := by
      calc
        W b hb e z * rho b = rho b * W b hb e z := by ring
        _ < kappa b * (A b hb e z) ^ 2 := by
          exact sub_pos.mp hQpos
        _ = _ := hPow
    have hOrbit :=
      (p4Q2PZ37ACM_originalGICertificate_orbit_pos_iff H b hb e z).mpr hCriterion
    exact hNo ⟨z, hOrbit⟩
  have hI : (∫ z : Pair, Q b hb e z ∂outer) ≤
      (∫ _z : Pair, (0 : ℝ) ∂outer) := by
    apply integral_mono
      ((p4Q2PZ37ACO_originalGISquaredMargin_continuous H b hb e).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (integrable_const _)
    exact hNonpos
  have hZero : (∫ _z : Pair, (0 : ℝ) ∂outer) = 0 := by simp
  rw [p4Q2PZ37ACO_originalGIMeanBudget_integral, hZero] at hI
  exact (not_le_of_gt hBudget) hI

private theorem p4Q2PZ37ACO_certificate_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Continuous (L b hb e) := by
  have hC : Continuous (C b hb e) :=
    p4Q2PZ37ACD_originalReceiver_covariance_continuous H b hb f₀ e
  have hV : Continuous (V b hb e) :=
    p4Q2PZ37ACD_originalReceiver_variance_continuous H b hb f₀ e
  have hD : Continuous (D b hb e) := by
    unfold p4Q2PZ37ACL_originalCenteredRegressionDefect
    exact hV.sub (continuous_const.mul (hC.pow 2))
  unfold p4Q2PZ37ACM_originalGICertificate
  exact (continuous_const.mul hC.abs).sub
    (Real.continuous_sqrt.comp (hD.mul continuous_const))

private theorem p4Q2PZ37ACO_outerOpenPos : Measure.IsOpenPosMeasure outer := by
  letI : (normalizedCompactHaar G).IsOpenPosMeasure := by
    unfold normalizedCompactHaar
    infer_instance
  letI : (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
    unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    infer_instance
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- If the still-open actual positive mean GI budget is discharged, there
is an OPEN original outer-Haar set of positive actual GI response, not
merely a point or an optimizer orbit with unknown Haar measure. -/
theorem p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    (b : ℝ) (hb : 0 ≤ b) (e : Link)
    (hBudget : 0 < Budget b hb e) :
    ∃ U : Set Pair, IsOpen U ∧
      0 < Measure.real outer U ∧
      ∀ w ∈ U,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb f₀ e w| := by
  letI : Measure.IsOpenPosMeasure outer := p4Q2PZ37ACO_outerOpenPos H
  obtain ⟨z, a, ha⟩ :=
    p4Q2PZ37ACO_originalGIBudget_gives_orbitCertificate H b hb e hBudget
  let U : Set Pair := {w | 0 < L b hb e w}
  have hOpen : IsOpen U :=
    isOpen_lt continuous_const (p4Q2PZ37ACO_certificate_continuous H b hb e)
  have hNonempty : U.Nonempty := ⟨Γ e a z, ha⟩
  have hMass : 0 < Measure.real outer U :=
    ENNReal.toReal_pos (hOpen.measure_pos outer hNonempty).ne' (measure_ne_top _ _)
  refine ⟨U, hOpen, hMass, ?_⟩
  intro w hw
  exact hw.trans_le (p4Q2PZ37ACM_originalGICertificate_le_abs H b hb e w)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACO_originalRelativeMargin_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACO_originalRelativeMargin_tail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACO_originalRelativeMargin_region_mass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACO_originalRelativeMargin_region_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACO_exists_sameContext_relativeResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACO_originalGIMeanBudget_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACO_originalGISquaredMargin_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACO_originalGISquaredMargin_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACO_originalGIBudget_tail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACO_originalGIBudget_gives_orbitCertificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
