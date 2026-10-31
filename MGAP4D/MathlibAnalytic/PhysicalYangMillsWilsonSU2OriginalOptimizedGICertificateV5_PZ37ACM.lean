import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOrbitAmplitudeV5_PZ37ACM

/-!
# P4-Q2-PZ37ACM — exact optimum of an original GI lower certificate

The actual ACH posterior energy contrast and the ACI squared regression
error give the unconditional pointwise lower certificate
  L = 2*b*exp(-32*b)*abs(C) - sqrt(D*rho(b)) <= abs(GI).
The ACM joint orbit optimizer makes its exact maximum
  Lstar = 2*b*exp(-32*b)*A - sqrt(W*rho(b)).

A positive certificate occurs on this genuine orbit if and only if
  W*rho(b) < (2*b*exp(-32*b)*A)^2.
This characterizes the certificate, not nonvanishing of the actual GI.
The criterion is not assumed or asserted to hold for a physical context.
Zero coupling and zero amplitude are included. No positive uniform
margin, original outer mass, or volume-independent coercivity is inferred.
-/

namespace MGAP4D.MathlibAnalytic

open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "D" => p4Q2PZ37ACL_originalCenteredRegressionDefect H
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "Γ" => p4Q2PZ37ACK_originalGaugePair H
local notation "k" => p4Q2PZ37ACH_originalPosteriorEnergyContrast H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H
local notation "rho" => p4Q2PZ37ACI_originalPosteriorResidualEnvelope
local instance p4Q2PZ37ACM_certificateLinks : Fintype Link := Fintype.ofFinite _

/-- A pointwise lower certificate for the SAME original absolute GI response. -/
def p4Q2PZ37ACM_originalGICertificate
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  2 * b * Real.exp (-32 * b) * |C b hb e z| -
    Real.sqrt (D b hb e z * rho b)
local notation "L" => p4Q2PZ37ACM_originalGICertificate H

/-- The exact optimum of this certificate on the genuine original gauge orbit. -/
def p4Q2PZ37ACM_originalOptimizedGICertificate
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  2 * b * Real.exp (-32 * b) * A b hb e z -
    Real.sqrt (W b hb e z * rho b)
local notation "Lstar" => p4Q2PZ37ACM_originalOptimizedGICertificate H

/-- The true posterior coefficient floor and true regression error imply
the certificate bound without any favorable-sign or residual premise. -/
theorem p4Q2PZ37ACM_originalGICertificate_le_abs
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    L b hb e z ≤ |gap b hb f₀ e z| := by
  have hSq := p4Q2PZ37ACI_originalGI_energyRegression_explicit_sq H b hb f₀ e z
  change (gap b hb f₀ e z + 4 * k b hb z.2 e * C b hb e z) ^ 2 ≤
    D b hb e z * rho b at hSq
  have hErr := abs_le.mp (Real.abs_le_sqrt hSq)
  have hk := (p4Q2PZ37ACH_originalEnergyContrast_twoSided H b hb z.2 e).1
  have hScale : 2 * b * Real.exp (-32 * b) ≤ 4 * k b hb z.2 e := by
    nlinarith only [hk]
  unfold p4Q2PZ37ACM_originalGICertificate
  by_cases hC : 0 ≤ C b hb e z
  · rw [abs_of_nonneg hC]
    have hMul := mul_le_mul_of_nonneg_right hScale hC
    nlinarith only [hMul, hErr.2, neg_le_abs (gap b hb f₀ e z)]
  · have hC0 : C b hb e z ≤ 0 := (lt_of_not_ge hC).le
    rw [abs_of_nonpos hC0]
    have hMul := mul_le_mul_of_nonneg_right hScale (neg_nonneg.mpr hC0)
    nlinarith only [hMul, hErr.1, le_abs_self (gap b hb f₀ e z)]

/-- Every actual gauge transformation has certificate at most the exact
amplitude/minimal-residual value of the original context. -/
theorem p4Q2PZ37ACM_originalGICertificate_gauge_le
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (a : G) :
    L b hb e (Γ e a z) ≤ Lstar b hb e z := by
  have hScale : 0 ≤ 2 * b * Real.exp (-32 * b) := by positivity
  have hLinear := mul_le_mul_of_nonneg_left
    (p4Q2PZ37ACM_originalCovariance_gauge_abs_le H b hb e z a) hScale
  have hRoot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
    (p4Q2PZ37ACM_originalDefect_gauge_bounds H b hb e z a).1
    (p4Q2PZ37ACI_originalPosteriorResidualEnvelope_nonneg b))
  exact sub_le_sub hLinear hRoot

/-- The bound is attained by an actual SU(2) gauge element, including
zero-amplitude orbits. No hypothetical optimizing context is assumed. -/
theorem p4Q2PZ37ACM_originalOptimizedGICertificate_attained
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    ∃ a : G, L b hb e (Γ e a z) = Lstar b hb e z := by
  obtain ⟨a, hC, hD⟩ := p4Q2PZ37ACM_originalOrbit_joint_optimizer H b hb e z
  refine ⟨a, ?_⟩
  unfold p4Q2PZ37ACM_originalGICertificate p4Q2PZ37ACM_originalOptimizedGICertificate
  rw [hC, hD, abs_of_nonneg (p4Q2PZ37ACM_originalCovarianceAmplitude_nonneg H b hb e z)]

/-- Exact positivity test for the optimized certificate. This equivalence
does not assert that the physical residual passes the test. -/
theorem p4Q2PZ37ACM_originalOptimizedGICertificate_pos_iff
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    0 < Lstar b hb e z ↔
      W b hb e z * rho b < (2 * b * Real.exp (-32 * b) * A b hb e z) ^ 2 := by
  have hA := p4Q2PZ37ACM_originalCovarianceAmplitude_nonneg H b hb e z
  have hW := p4Q2PZ37ACK_originalFourModeResidualEnergy_nonneg H b hb e z
  have hRho := p4Q2PZ37ACI_originalPosteriorResidualEnvelope_nonneg b
  unfold p4Q2PZ37ACM_originalOptimizedGICertificate
  rw [sub_pos]
  exact Real.sqrt_lt (mul_nonneg hW hRho) (by positivity)

/-- A positive lower certificate occurs somewhere on this SAME orbit
exactly when the actual four-mode residual satisfies the squared test. -/
theorem p4Q2PZ37ACM_originalGICertificate_orbit_pos_iff
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    (∃ a : G, 0 < L b hb e (Γ e a z)) ↔
      W b hb e z * rho b < (2 * b * Real.exp (-32 * b) * A b hb e z) ^ 2 := by
  constructor
  · rintro ⟨a, ha⟩
    exact (p4Q2PZ37ACM_originalOptimizedGICertificate_pos_iff H b hb e z).mp
      (ha.trans_le (p4Q2PZ37ACM_originalGICertificate_gauge_le H b hb e z a))
  · intro h
    obtain ⟨a, ha⟩ := p4Q2PZ37ACM_originalOptimizedGICertificate_attained H b hb e z
    refine ⟨a, ?_⟩
    rw [ha]
    exact (p4Q2PZ37ACM_originalOptimizedGICertificate_pos_iff H b hb e z).mpr h

/-- Zero coupling gives a zero optimized certificate, never a positive floor. -/
theorem p4Q2PZ37ACM_originalOptimizedGICertificate_zero
    (e : Link) (z : Pair) : Lstar 0 (le_refl 0) e z = 0 := by
  simp [p4Q2PZ37ACM_originalOptimizedGICertificate,
    p4Q2PZ37ACI_originalPosteriorResidualEnvelope]

/-- Zero orbit amplitude cannot supply a positive certificate. -/
theorem p4Q2PZ37ACM_originalOptimizedGICertificate_nonpos_of_amplitude_zero
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (hA : A b hb e z = 0) :
    Lstar b hb e z ≤ 0 := by
  unfold p4Q2PZ37ACM_originalOptimizedGICertificate
  rw [hA, mul_zero, zero_sub]
  exact neg_nonpos.mpr (Real.sqrt_nonneg _)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalGICertificate_le_abs
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalGICertificate_gauge_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalOptimizedGICertificate_attained
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalOptimizedGICertificate_pos_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalGICertificate_orbit_pos_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalOptimizedGICertificate_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACM_originalOptimizedGICertificate_nonpos_of_amplitude_zero
