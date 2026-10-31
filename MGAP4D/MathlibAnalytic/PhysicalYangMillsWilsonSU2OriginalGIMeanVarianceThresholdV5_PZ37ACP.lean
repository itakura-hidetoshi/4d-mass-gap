import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalResidualAmplitudeMomentV5_PZ37ACO

/-!
# P4-Q2-PZ37ACP — exact original Wilson GI variance threshold

Keep the SAME original centered Gauss-law physical source, FF receiver,
positive Perron representative, transfer norm, original two posterior laws,
boundary configurations, and original pair-Haar law. In particular, no
surrogate four-mode receiver or independent residual assumption is introduced.

For the original four-mode covariance moment S>0, original mean receiver
variance Vbar, original nonnegative orthogonal remainder Wbar, and the
genuine ACI posterior error envelope rho, ACK proves Vbar=16*S+Wbar.
ACO's genuine mean squared-GI margin is
    M = 4*kappa*S-rho*Wbar
      = (4*kappa+16*rho)*S-rho*Vbar,
with kappa=(2*b*exp(-32*b))^2.

The exact posterior coefficient identity at EVERY b is
    16*rho(b)=kappa(b)*(exp(64*b)-1)^2.
At positive b, kappa and the exponent gap are strictly positive. Thus
    M>0  iff  (exp(64*b)-1)^2*Wbar < 64*S
         iff  (exp(64*b)-1)^2*Vbar
                 < (64+16*(exp(64*b)-1)^2)*S.

These are algebraically exact tests on the original physical data, NOT
assertions that the original receiver satisfies the test. Failure of the
test is an explicit obstruction for the ACO *mean-budget* sufficient
condition; it does NOT establish vanishing of the actual original GI
response. Positive budget retains the ACO open positive-Haar-mass result.
No volume-uniform mass gap, support cylinder, or H1-H4 is inferred.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ACP_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACP_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACP_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACP_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACP_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACP_probability : IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "Vbar" => p4Q2PZ37ACK_originalReceiverVarianceMoment H
local notation "kappa" => p4Q2PZ37ACO_originalGISlopeSq
local notation "rho" => p4Q2PZ37ACI_originalPosteriorResidualEnvelope
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "L" => p4Q2PZ37ACM_originalGICertificate H
local notation "Γ" => p4Q2PZ37ACK_originalGaugePair H
local instance p4Q2PZ37ACP_links : Fintype Link := Fintype.ofFinite _

/-- The exact dimensionless exponential gap of the original two posteriors. -/
def p4Q2PZ37ACP_originalPosteriorExponentGapSq (b : ℝ) : ℝ :=
  (Real.exp (64 * b) - 1) ^ 2
local notation "tau" => p4Q2PZ37ACP_originalPosteriorExponentGapSq

/-- No approximation: the ACI error coefficient and ACO signal coefficient
have exactly this relation even at zero coupling. -/
theorem p4Q2PZ37ACP_originalPosteriorCoefficient_identity (b : ℝ) :
    16 * rho b = kappa b * tau b := by
  have hexp : Real.exp (32 * b) =
      Real.exp (-32 * b) * Real.exp (64 * b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold p4Q2PZ37ACI_originalPosteriorResidualEnvelope
    p4Q2PZ37ACO_originalGISlopeSq
    p4Q2PZ37ACP_originalPosteriorExponentGapSq
  rw [hexp]
  ring

/-- Genuine original GI signal coefficient is positive at every b>0. -/
theorem p4Q2PZ37ACP_originalGISlopeSq_pos (b : ℝ) (hb : 0 < b) :
    0 < kappa b := by
  unfold p4Q2PZ37ACO_originalGISlopeSq
  have h : 0 < 2 * b * Real.exp (-32 * b) := by positivity
  exact pow_pos h _

/-- The actual ACI posterior-error envelope is strictly positive for b>0. -/
theorem p4Q2PZ37ACP_originalPosteriorEnvelope_pos
    (b : ℝ) (hb : 0 < b) : 0 < rho b := by
  have hgap : 0 < Real.exp (32 * b) - Real.exp (-32 * b) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  unfold p4Q2PZ37ACI_originalPosteriorResidualEnvelope
  exact mul_pos (by positivity) (pow_pos hgap _)

/-- The explicit exponent-gap square is strictly positive for b>0. -/
theorem p4Q2PZ37ACP_originalPosteriorExponentGapSq_pos
    (b : ℝ) (hb : 0 < b) : 0 < tau b := by
  have he : 1 < Real.exp (64 * b) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  unfold p4Q2PZ37ACP_originalPosteriorExponentGapSq
  exact pow_pos (sub_pos.mpr he) _

/-- Exact physical mean-budget re-expression using ACK's genuine four-mode
Haar variance allocation, without introducing a numerical lower bound. -/
theorem p4Q2PZ37ACP_originalGIMeanBudget_variance_identity
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Budget b hb e =
      (4 * kappa b + 16 * rho b) * S b hb e -
        rho b * Vbar b hb e := by
  unfold p4Q2PZ37ACO_originalGIMeanBudget
  rw [p4Q2PZ37ACK_originalVarianceMoment_eq H b hb e]
  ring

/-- Sharp original-data variance criterion for the positive mean GI budget.
The inequality itself remains an open physical check. -/
theorem p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_variance
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    0 < Budget b hb e ↔
      rho b * Vbar b hb e <
        (4 * kappa b + 16 * rho b) * S b hb e := by
  rw [p4Q2PZ37ACP_originalGIMeanBudget_variance_identity H b hb e]
  exact sub_pos

/-- Exact obstruction to ACO's positive-*mean* criterion. It does not
assert that the original two-posterior GI response is zero. -/
theorem p4Q2PZ37ACP_originalGIMeanBudget_nonpos_iff_variance_obstruction
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Budget b hb e ≤ 0 ↔
      (4 * kappa b + 16 * rho b) * S b hb e ≤
        rho b * Vbar b hb e := by
  rw [p4Q2PZ37ACP_originalGIMeanBudget_variance_identity H b hb e]
  constructor <;> intro h <;> linarith

/-- All factors retained: a division-free exact exponential identity
linking the original original GI budget to its original four-mode remainder. -/
theorem p4Q2PZ37ACP_originalGIMeanBudget_scaled_exponential
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    16 * Budget b hb e =
      kappa b * (64 * S b hb e - tau b * Wbar b hb e) := by
  calc
    16 * Budget b hb e =
        (64 * S b hb e) * kappa b - (16 * rho b) * Wbar b hb e := by
      unfold p4Q2PZ37ACO_originalGIMeanBudget
      ring
    _ = (64 * S b hb e) * kappa b -
        (kappa b * tau b) * Wbar b hb e := by
      rw [p4Q2PZ37ACP_originalPosteriorCoefficient_identity]
    _ = kappa b * (64 * S b hb e - tau b * Wbar b hb e) := by ring

/-- EXACT conditional relative-residual threshold for the physical original
receiver, posterior pair, Perron representative, and boundary contexts. -/
theorem p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_residual
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < Budget b hb.le e ↔
      tau b * Wbar b hb.le e < 64 * S b hb.le e := by
  have hk : 0 < kappa b := p4Q2PZ37ACP_originalGISlopeSq_pos b hb
  have hEq := p4Q2PZ37ACP_originalGIMeanBudget_scaled_exponential H b hb.le e
  constructor
  · intro h
    have hp : 0 < kappa b *
        (64 * S b hb.le e - tau b * Wbar b hb.le e) := by
      rw [← hEq]
      exact mul_pos (by norm_num) h
    have hi : 0 < 64 * S b hb.le e - tau b * Wbar b hb.le e := by
      by_contra hn
      have hnon : 64 * S b hb.le e - tau b * Wbar b hb.le e ≤ 0 :=
        le_of_not_gt hn
      exact (not_le_of_gt hp) (mul_nonpos_of_nonneg_of_nonpos hk.le hnon)
    exact sub_pos.mp hi
  · intro h
    have hp : 0 < 16 * Budget b hb.le e := by
      rw [hEq]
      exact mul_pos hk (sub_pos.mpr h)
    nlinarith only [hp]

/-- The variance threshold has no division by S, and is valid for each
original finite-volume positive-coupling Wilson configuration family. -/
theorem p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_variance
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < Budget b hb.le e ↔
      tau b * Vbar b hb.le e <
        (64 + 16 * tau b) * S b hb.le e := by
  rw [p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_residual H b hb e]
  rw [p4Q2PZ37ACK_originalVarianceMoment_eq H b hb.le e]
  constructor <;> intro h <;> nlinarith only [h]

/-- Failure of the exact residual threshold is equivalent to the
nonpositive *mean certificate*, not to vanishing of the true GI. -/
theorem p4Q2PZ37ACP_originalGIMeanBudget_nonpos_iff_exponential_obstruction
    (b : ℝ) (hb : 0 < b) (e : Link) :
    Budget b hb.le e ≤ 0 ↔
      64 * S b hb.le e ≤ tau b * Wbar b hb.le e := by
  have hIff :=
    p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_residual H b hb e
  constructor
  · intro h
    by_contra hn
    have hp : 0 < Budget b hb.le e :=
      hIff.mpr (lt_of_not_ge hn)
    exact (not_le_of_gt hp) h
  · intro h
    by_contra hn
    have hp : 0 < Budget b hb.le e := lt_of_not_ge hn
    exact (not_lt_of_ge h) (hIff.mp hp)

/-- At b=0 neither the original first-order coefficient nor the genuine
posterior residual envelope can produce a positive budget. -/
theorem p4Q2PZ37ACP_originalGIMeanBudget_zero (e : Link) :
    Budget (0 : ℝ) (le_refl 0) e = 0 := by
  simp [p4Q2PZ37ACO_originalGIMeanBudget,
    p4Q2PZ37ACO_originalGISlopeSq,
    p4Q2PZ37ACI_originalPosteriorResidualEnvelope]

/-- A verified strict physical variance comparison would supply a real
SU(2) orbit with strictly positive original ACM/GI certificate. -/
theorem p4Q2PZ37ACP_originalVarianceThreshold_gives_orbitCertificate
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hThreshold : tau b * Vbar b hb.le e <
      (64 + 16 * tau b) * S b hb.le e) :
    ∃ z : Pair, ∃ a : G, 0 < L b hb.le e (Γ e a z) := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_orbitCertificate H b hb.le e
    ((p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_variance H b hb e).mpr
      hThreshold)

/-- Under that still-open exact physical comparison, the SAME original
two-posterior GI is nonzero on an open positive pair-Haar-mass region. -/
theorem p4Q2PZ37ACP_originalVarianceThreshold_gives_open_positiveGIRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hThreshold : tau b * Vbar b hb.le e <
      (64 + 16 * tau b) * S b hb.le e) :
    ∃ U : Set Pair, IsOpen U ∧
      0 < Measure.real outer U ∧
      ∀ w ∈ U,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le f₀ e w| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion H b hb.le e
    ((p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_variance H b hb e).mpr
      hThreshold)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalPosteriorCoefficient_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalGISlopeSq_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalPosteriorEnvelope_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalPosteriorExponentGapSq_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalGIMeanBudget_variance_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalGIMeanBudget_nonpos_iff_variance_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalGIMeanBudget_scaled_exponential
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_residual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalGIMeanBudget_nonpos_iff_exponential_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalGIMeanBudget_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalVarianceThreshold_gives_orbitCertificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACP_originalVarianceThreshold_gives_open_positiveGIRegion
