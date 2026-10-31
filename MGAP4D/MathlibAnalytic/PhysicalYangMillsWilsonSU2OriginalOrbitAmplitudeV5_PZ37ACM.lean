import MGAP4D.MathlibAnalytic.FiniteRealSphereAmplitude
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoFourModeSynthesisV5_PZ37ACM
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalZeroCovarianceResidualObstructionV5_PZ37ACL

/-!
# P4-Q2-PZ37ACM — exact amplitude and residual on the original SU(2) orbit

The four ACK coefficients of the SAME original centered physical receiver
give its exact covariance amplitude A = sqrt(sum m_j^2). Actual SU(2)
coordinate synthesis attains A. The ACL center path then fills the entire
covariance interval [-A,A]. The unchanged receiver variance is constant
on that orbit, so the actual scalar regression defect ranges over [W,V],
where W is ACK's original four-mode residual square integral.

An actual optimizer has both C=A and D=W. Every strict covariance floor
c<A and residual ceiling d>W therefore holds on one open set of positive
ORIGINAL outer pair-Haar mass. ACI discharges positive amplitude for some
actual context at every finite H, positive b, and genuine link e.

The original GI regression error at the optimizer is bounded by W*rho(b).
No favorable sign of the resulting GI margin is asserted. No numerical or
volume-uniform amplitude, event mass, or residual ratio is assumed. All
original physical data and all earlier obstruction theorems are retained.
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
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "φ" => p4Q2PZ37ACK_fourModeCharacter
local notation "center" => p4Q2PZ35D4_centralMinusOne
local notation "path" => p4Q2PZ37ACL_originalCenterPath
local instance p4Q2PZ37ACM_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACM_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACM_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACM_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACM_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACM_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "V" => p4Q2PZ37ACL_originalCenteredReceiverVariance H
local notation "D" => p4Q2PZ37ACL_originalCenteredRegressionDefect H
local notation "m" => p4Q2PZ37ACK_originalFourModeCoefficient H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "Γ" => p4Q2PZ37ACK_originalGaugePair H
local instance p4Q2PZ37ACM_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACM_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The Euclidean amplitude of the four actual original receiver coefficients. -/
def p4Q2PZ37ACM_originalCovarianceAmplitude
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  FiniteRealSphereAmplitude.amplitude (m b hb e z)
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H

/-- Nonnegativity includes the zero-amplitude orbit. -/
theorem p4Q2PZ37ACM_originalCovarianceAmplitude_nonneg
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : 0 ≤ A b hb e z :=
  FiniteRealSphereAmplitude.amplitude_nonneg _

/-- Exact amplitude square in the original four Haar coefficients. -/
theorem p4Q2PZ37ACM_originalCovarianceAmplitude_sq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    (A b hb e z) ^ 2 = ∑ j : Fin 4, (m b hb e z j) ^ 2 :=
  FiniteRealSphereAmplitude.amplitude_sq _

/-- The actual orbit covariance is the four-coefficient linear form, with
the inverse and sign fixed by the original character transport. -/
theorem p4Q2PZ37ACM_originalCovariance_gauge_fourMode
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (a : G) :
    C b hb e (Γ e a z) =
      -(∑ j : Fin 4, m b hb e z j * φ j (a⁻¹)) := by
  have hF := p4Q2PZ37ACK_centeredReceiver_continuous H b hb e z
  have hTerm (j : Fin 4) :
      Integrable (fun g : G => φ j (a⁻¹) * (F b hb f₀ e z g * φ j g)) μ :=
    ((hF.mul (p4Q2PZ37ACK_fourModeCharacter_continuous j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  calc
    _ = -(∫ g : G, F b hb f₀ e z g * χ (a * g) ∂μ) :=
      p4Q2PZ37ACK_centeredReceiver_covariance_gauge H b hb e a z
    _ = -(∫ g : G, ∑ j : Fin 4,
        φ j (a⁻¹) * (F b hb f₀ e z g * φ j g) ∂μ) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with g
      rw [p4Q2PZ37ACM_fourModeCharacter_translate, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = -(∑ j : Fin 4, φ j (a⁻¹) * m b hb e z j) := by
      rw [integral_finset_sum _ (fun j _ => hTerm j)]
      simp only [integral_const_mul, p4Q2PZ37ACK_originalFourModeCoefficient,
        CompactFiniteHaarProjection.coefficient]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _

/-- Every genuine gauge element obeys the exact four-mode amplitude bound. -/
theorem p4Q2PZ37ACM_originalCovariance_gauge_abs_le
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (a : G) :
    |C b hb e (Γ e a z)| ≤ A b hb e z := by
  rw [p4Q2PZ37ACM_originalCovariance_gauge_fourMode, abs_neg]
  exact FiniteRealSphereAmplitude.abs_sum_mul_le_amplitude
    (m b hb e z) (fun j => φ j (a⁻¹))
    (p4Q2PZ37ACK_fourModeCharacter_sum_sq (a⁻¹))

/-- Squared covariance cannot exceed the actual squared amplitude. -/
theorem p4Q2PZ37ACM_originalCovariance_gauge_sq_le
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (a : G) :
    (C b hb e (Γ e a z)) ^ 2 ≤ (A b hb e z) ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg (C b hb e (Γ e a z)))
    (p4Q2PZ37ACM_originalCovariance_gauge_abs_le H b hb e z a) 2
  simpa only [sq_abs] using h

/-- A literal original SU(2) gauge transformation attains the positive
amplitude; coordinate synthesis also handles a zero coefficient vector. -/
theorem p4Q2PZ37ACM_originalCovariance_amplitude_attained
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    ∃ a : G, C b hb e (Γ e a z) = A b hb e z := by
  obtain ⟨x, hx, hmx⟩ :=
    FiniteRealSphereAmplitude.exists_unit_dot_eq_neg_amplitude (m b hb e z)
  obtain ⟨a, ha⟩ := p4Q2PZ37ACM_exists_fourModeCharacter_coordinates x hx
  refine ⟨a, ?_⟩
  rw [p4Q2PZ37ACM_originalCovariance_gauge_fourMode]
  simp_rw [ha]
  rw [hmx, neg_neg]
  rfl

/-- Exact pointwise variance allocation, with the actual ACK residual. -/
theorem p4Q2PZ37ACM_originalVariance_eq_amplitude_residual
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    V b hb e z = 4 * (A b hb e z) ^ 2 + W b hb e z := by
  have h := p4Q2PZ37ACK_originalFourModeResidualEnergy_eq H b hb e z
  change W b hb e z = V b hb e z - 4 * ∑ j : Fin 4, (m b hb e z j) ^ 2 at h
  rw [← p4Q2PZ37ACM_originalCovarianceAmplitude_sq H b hb e z] at h
  linarith

/-- Along the original orbit, only the covariance term in the scalar
regression defect changes; the actual variance is preserved. -/
theorem p4Q2PZ37ACM_originalDefect_gauge_eq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (a : G) :
    D b hb e (Γ e a z) = V b hb e z - 4 * (C b hb e (Γ e a z)) ^ 2 := by
  unfold p4Q2PZ37ACL_originalCenteredRegressionDefect
  rw [show V b hb e (Γ e a z) = V b hb e z from
    p4Q2PZ37ACK_centeredReceiver_variance_gauge H b hb e a z]

/-- The exact four-mode residual is a lower bound on EVERY scalar
energy-regression defect on the same genuine orbit. -/
theorem p4Q2PZ37ACM_originalDefect_gauge_bounds
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (a : G) :
    W b hb e z ≤ D b hb e (Γ e a z) ∧
      D b hb e (Γ e a z) ≤ V b hb e z := by
  rw [p4Q2PZ37ACM_originalDefect_gauge_eq]
  have hV := p4Q2PZ37ACM_originalVariance_eq_amplitude_residual H b hb e z
  have hC := p4Q2PZ37ACM_originalCovariance_gauge_sq_le H b hb e z a
  constructor
  · linarith
  · exact sub_le_self _ (mul_nonneg (by norm_num) (sq_nonneg _))

/-- One actual gauge element simultaneously maximizes positive covariance
and minimizes the scalar regression residual. -/
theorem p4Q2PZ37ACM_originalOrbit_joint_optimizer
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    ∃ a : G, C b hb e (Γ e a z) = A b hb e z ∧
      D b hb e (Γ e a z) = W b hb e z := by
  obtain ⟨a, ha⟩ := p4Q2PZ37ACM_originalCovariance_amplitude_attained H b hb e z
  refine ⟨a, ha, ?_⟩
  rw [p4Q2PZ37ACM_originalDefect_gauge_eq, ha,
    p4Q2PZ37ACM_originalVariance_eq_amplitude_residual]
  ring

private theorem p4Q2PZ37ACM_covariance_center_mul
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (a : G) :
    C b hb e (Γ e (center * a) z) = -C b hb e (Γ e a z) := by
  change CompactEnergyMismatchMoment.covariance μ (F b hb f₀ e (Γ e (center * a) z)) E =
    -CompactEnergyMismatchMoment.covariance μ (F b hb f₀ e (Γ e a z)) E
  rw [p4Q2PZ37ACK_centeredReceiver_covariance_gauge,
    p4Q2PZ37ACK_centeredReceiver_covariance_gauge]
  simp_rw [mul_assoc, p4Q2PZ35D4_originalCharacter_centralFlip, mul_neg]
  rw [integral_neg]

/-- The ACL actual center path fills the full covariance interval between
the attained endpoints. This includes degenerate zero-amplitude orbits. -/
theorem p4Q2PZ37ACM_originalOrbit_covariance_range
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    Set.range (fun a : G => C b hb e (Γ e a z)) =
      Set.Icc (-A b hb e z) (A b hb e z) := by
  ext c
  constructor
  · rintro ⟨a, rfl⟩
    exact abs_le.mp (p4Q2PZ37ACM_originalCovariance_gauge_abs_le H b hb e z a)
  · intro hc
    obtain ⟨a, ha⟩ := p4Q2PZ37ACM_originalCovariance_amplitude_attained H b hb e z
    let h : ℝ → ℝ := fun t => C b hb e (Γ e (path t * a) z)
    have hOrbit : Continuous (fun u : G => C b hb e (Γ e u z)) :=
      (p4Q2PZ37ACD_originalReceiver_covariance_continuous H b hb f₀ e).comp
        (p4Q2PZ37ACK_originalGaugePair_continuous_a H e z)
    have hCont : Continuous h := hOrbit.comp
      (p4Q2PZ37ACL_originalCenterPath_continuous.mul continuous_const)
    have hZero : h 0 = A b hb e z := by
      dsimp only [h]
      rw [p4Q2PZ37ACL_originalCenterPath_zero, one_mul, ha]
    have hPi : h Real.pi = -A b hb e z := by
      dsimp only [h]
      rw [p4Q2PZ37ACL_originalCenterPath_pi,
        p4Q2PZ37ACM_covariance_center_mul, ha]
    have hc' : c ∈ Set.Icc (h Real.pi) (h 0) := by
      rw [hPi, hZero]
      exact hc
    obtain ⟨t, _ht, ht⟩ :=
      intermediate_value_Icc' Real.pi_pos.le hCont.continuousOn hc'
    exact ⟨path t * a, ht⟩

/-- Every and only defect value between the actual four-mode residual
and the preserved variance occurs on the original SU(2) orbit. -/
theorem p4Q2PZ37ACM_originalOrbit_defect_range
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    Set.range (fun a : G => D b hb e (Γ e a z)) =
      Set.Icc (W b hb e z) (V b hb e z) := by
  ext d
  constructor
  · rintro ⟨a, rfl⟩
    exact p4Q2PZ37ACM_originalDefect_gauge_bounds H b hb e z a
  · intro hd
    let c : ℝ := Real.sqrt ((V b hb e z - d) / 4)
    have hc0 : 0 ≤ c := Real.sqrt_nonneg _
    have hcsq : c ^ 2 = (V b hb e z - d) / 4 :=
      Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hd.2) (by norm_num))
    have hA := p4Q2PZ37ACM_originalCovarianceAmplitude_nonneg H b hb e z
    have hV := p4Q2PZ37ACM_originalVariance_eq_amplitude_residual H b hb e z
    have hc : c ∈ Set.Icc (-A b hb e z) (A b hb e z) := by
      constructor
      · linarith
      · nlinarith [hd.1]
    rw [← p4Q2PZ37ACM_originalOrbit_covariance_range H b hb e z] at hc
    obtain ⟨a, ha⟩ := hc
    change C b hb e (Γ e a z) = c at ha
    refine ⟨a, ?_⟩
    change D b hb e (Γ e a z) = d
    rw [p4Q2PZ37ACM_originalDefect_gauge_eq, ha, hcsq]
    ring

private theorem p4Q2PZ37ACM_covariance_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : Continuous (C b hb e) :=
  p4Q2PZ37ACD_originalReceiver_covariance_continuous H b hb f₀ e

private theorem p4Q2PZ37ACM_defect_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : Continuous (D b hb e) :=
  (p4Q2PZ37ACD_originalReceiver_variance_continuous H b hb f₀ e).sub
    (continuous_const.mul ((p4Q2PZ37ACM_covariance_continuous H b hb e).pow 2))

private theorem p4Q2PZ37ACM_outerOpenPos : Measure.IsOpenPosMeasure outer := by
  letI : (normalizedCompactHaar G).IsOpenPosMeasure := by
    unfold normalizedCompactHaar
    infer_instance
  letI : (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
    unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    infer_instance
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- A SAME-context covariance floor and scalar residual ceiling define
an open event in the original outer configuration space. -/
theorem p4Q2PZ37ACM_selectedRegion_isOpen
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (c d : ℝ) :
    IsOpen {w : Pair | c < C b hb e w ∧ D b hb e w < d} :=
  (isOpen_lt continuous_const (p4Q2PZ37ACM_covariance_continuous H b hb e)).inter
    (isOpen_lt (p4Q2PZ37ACM_defect_continuous H b hb e) continuous_const)

/-- Every strict relaxation of the actual simultaneous orbit optimum
has positive ORIGINAL outer Haar mass. No hypothetical good point is assumed. -/
theorem p4Q2PZ37ACM_selectedRegion_mass_pos
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (c d : ℝ)
    (hc : c < A b hb e z) (hd : W b hb e z < d) :
    0 < Measure.real outer {w : Pair | c < C b hb e w ∧ D b hb e w < d} := by
  letI : Measure.IsOpenPosMeasure outer := p4Q2PZ37ACM_outerOpenPos H
  obtain ⟨a, hC, hD⟩ := p4Q2PZ37ACM_originalOrbit_joint_optimizer H b hb e z
  have hNonempty : {w : Pair | c < C b hb e w ∧ D b hb e w < d}.Nonempty := by
    refine ⟨Γ e a z, ?_⟩
    change c < C b hb e (Γ e a z) ∧ D b hb e (Γ e a z) < d
    rw [hC, hD]
    exact ⟨hc, hd⟩
  exact ENNReal.toReal_pos
    ((p4Q2PZ37ACM_selectedRegion_isOpen H b hb e c d).measure_pos outer hNonempty).ne'
    (measure_ne_top _ _)

/-- ACI supplies a positive actual orbit amplitude for every genuine link
at every finite volume and positive coupling. -/
theorem p4Q2PZ37ACM_exists_positiveAmplitude
    (b : ℝ) (hb : 0 < b) (e : Link) : ∃ z : Pair, 0 < A b hb.le e z := by
  obtain ⟨z, _zNeg, hz, _hzNeg⟩ :=
    p4Q2PZ37ACI_centeredEnergyCovariance_both_signs
      H b hb e (originalWilsonExplicitIdentityBoundary H)
  have hz' : 0 < C b hb.le e z := hz
  have hBound := p4Q2PZ37ACM_originalCovariance_gauge_abs_le H b hb.le e z (1 : G)
  rw [p4Q2PZ37ACK_originalGaugePair_one, abs_of_pos hz'] at hBound
  exact ⟨z, hz'.trans_le hBound⟩

/-- One actual positive-amplitude context supplies selected positive-mass
regions arbitrarily close to its minimal residual, retaining half its amplitude.
The event and its qualitative mass may depend on epsilon. -/
theorem p4Q2PZ37ACM_exists_nearOptimal_regions
    (b : ℝ) (hb : 0 < b) (e : Link) :
    ∃ z : Pair, 0 < A b hb.le e z ∧ ∀ epsilon : ℝ, 0 < epsilon →
      0 < Measure.real outer {w : Pair |
        A b hb.le e z / 2 < C b hb.le e w ∧
          D b hb.le e w < W b hb.le e z + epsilon} := by
  obtain ⟨z, hz⟩ := p4Q2PZ37ACM_exists_positiveAmplitude H b hb e
  refine ⟨z, hz, ?_⟩
  intro epsilon hepsilon
  exact p4Q2PZ37ACM_selectedRegion_mass_pos H b hb.le e z
    (A b hb.le e z / 2) (W b hb.le e z + epsilon) (by linarith) (by linarith)

/-- At the actual joint optimizer the ORIGINAL two-posterior GI regression
error is controlled by the minimal residual W and the proved ACI envelope.
This proves an error estimate, not positivity of its unresolved GI margin. -/
theorem p4Q2PZ37ACM_originalGI_optimizedRegression_sq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    ∃ a : G, C b hb e (Γ e a z) = A b hb e z ∧
      D b hb e (Γ e a z) = W b hb e z ∧
      (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb f₀ e (Γ e a z) +
        4 * p4Q2PZ37ACH_originalPosteriorEnergyContrast H b hb (Γ e a z).2 e *
          A b hb e z) ^ 2 ≤
        W b hb e z * p4Q2PZ37ACI_originalPosteriorResidualEnvelope b := by
  obtain ⟨a, hC, hD⟩ := p4Q2PZ37ACM_originalOrbit_joint_optimizer H b hb e z
  refine ⟨a, hC, hD, ?_⟩
  have h := p4Q2PZ37ACI_originalGI_energyRegression_explicit_sq
    H b hb f₀ e (Γ e a z)
  change (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb f₀ e (Γ e a z) +
    4 * p4Q2PZ37ACH_originalPosteriorEnergyContrast H b hb (Γ e a z).2 e *
      C b hb e (Γ e a z)) ^ 2 ≤
    D b hb e (Γ e a z) * p4Q2PZ37ACI_originalPosteriorResidualEnvelope b at h
  rw [hC, hD] at h
  exact h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalCovarianceAmplitude_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalCovarianceAmplitude_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalCovariance_gauge_fourMode
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalCovariance_gauge_abs_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalCovariance_gauge_sq_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalCovariance_amplitude_attained
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalVariance_eq_amplitude_residual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalDefect_gauge_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalDefect_gauge_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalOrbit_joint_optimizer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalOrbit_covariance_range
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalOrbit_defect_range
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_selectedRegion_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_selectedRegion_mass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_exists_positiveAmplitude
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_exists_nearOptimal_regions
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalGI_optimizedRegression_sq
