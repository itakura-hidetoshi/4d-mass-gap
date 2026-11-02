import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUnconditionalHaarRadiusV5_PZ37ADZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEA — unconditional explicit ORIGINAL boundary pair-Haar full-ball floor

ADZ established the strictly positive, unconditional, radius-only floor
κ(r) = Measure.toSphereBallBound 4 r / 4 for the genuine original
normalized SU(2) one-link chordal Haar mass m(r), at every positive r.

ADM independently established that for the ACTUAL finite-volume original
boundary pair-Haar ν_H and its original full all-link chordal distance D_H,
the mass of every true radius-R ball is at least
  m(R/(2*card(Link_H)+1))^(2*card(Link_H)).

This append-only file composes these TWO proved, unchanged interfaces.
It discharges the exact scaled-radius positivity and real-power
monotonicity, giving an unconditional positive, explicit, H-dependent
lower bound for EVERY original boundary-pair center and EVERY R>0.
The same bound is also installed in ADM's genuinely physical
nonzero-covariance moment witness for each original spatial link.

No new physical assumptions, changed SU(2), altered normalized Haar,
changed Gauss-law source, FF receiver, interacting posterior,
boundary pair law, H-uniform coercivity, spectral gap, or continuum
4D Yang-Mills mass gap are asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "Ball" => p4Q2PZ37ADL_originalFullBoundaryChordalBall H
local notation "m" => p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass
local notation "κ" => p4Q2PZ37ADQ_sphereRadiusFraction
local notation "b₀" => p4Q2PZ37ADC_fixedCoupling
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H

local instance p4Q2PZ37AEA_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AEA_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The exact original 2*card(Link_H)+1 denominator remains positive.
Every positive full-ball radius thus gives a positive one-link radius. -/
theorem p4Q2PZ37AEA_scaledRadius_pos
    (R : ℝ) (hR : 0 < R) :
    0 < R / (2 * (Fintype.card Link : ℝ) + 1) := by
  have hDen : (0 : ℝ) < 2 * (Fintype.card Link : ℝ) + 1 := by
    positivity
  exact div_pos hR hDen

/-- ADZ's unconditional, genuine SU(2) Haar lower bound applies at
ADM's exact full-box scale, with no new transport or covering premise. -/
theorem p4Q2PZ37AEA_scaledRadialMass_ge_explicit
    (R : ℝ) (hR : 0 < R) :
    κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ≤
      m (R / (2 * (Fintype.card Link : ℝ) + 1)) := by
  exact p4Q2PZ37ADZ_originalRadialMass_ge_explicit _
    (p4Q2PZ37AEA_scaledRadius_pos H R hR)

/-- The explicit finite-volume pair-Haar bound is strictly positive,
including at small radii. -/
theorem p4Q2PZ37AEA_explicitFloor_pos
    (R : ℝ) (hR : 0 < R) :
    0 <
      κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link) := by
  have hr := p4Q2PZ37AEA_scaledRadius_pos H R hR
  exact pow_pos (p4Q2PZ37ADQ_sphereRadiusFraction_pos _) _

/-- Power monotonicity is valid without any link-count nonemptiness
hypothesis: the exponent 2*card(Link_H) is a natural number. -/
theorem p4Q2PZ37AEA_explicitFloor_le_radialPower
    (R : ℝ) (hR : 0 < R) :
    κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link) ≤
      m (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link) := by
  exact pow_le_pow_left₀
    (le_of_lt (p4Q2PZ37ADQ_sphereRadiusFraction_pos _))
    (p4Q2PZ37AEA_scaledRadialMass_ge_explicit H R hR) _

/-- Main AEA result: an unconditional radius-only quantitative floor
for the TRUE, unchanged finite-H original boundary pair-Haar full
chordal ball, at EVERY center and R>0. The exponent depends on H. -/
theorem p4Q2PZ37AEA_originalFullBall_mass_ge_explicit
    (a : Pair) (R : ℝ) (hR : 0 < R) :
    κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link) ≤
      Measure.real outer (Ball a R) := by
  exact (p4Q2PZ37AEA_explicitFloor_le_radialPower H R hR).trans
    (p4Q2PZ37ADM_originalFullBall_mass_ge_radialPower H a R hR)

/-- A literal half-radius original full-boundary ball has the
same proved explicit nonzero pair-Haar lower bound. -/
theorem p4Q2PZ37AEA_originalHalfBall_mass_ge_explicit
    (a : Pair) :
    κ ((1 / 2 : ℝ) / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link) ≤
      Measure.real outer (Ball a (1 / 2)) :=
  p4Q2PZ37AEA_originalFullBall_mass_ge_explicit
    H a (1 / 2) (by norm_num)

/-- For EACH unchanged original physical spatial link, the nonzero
Wilson covariance witness from ACI/ADM has the SAME explicit ADZ
pair-Haar lower bound; the genuine ADE covariance-square moment
inequality is retained, not assumed or replaced. -/
theorem p4Q2PZ37AEA_originalEveryLink_explicitMomentWitness
    (e : Link) :
    ∃ (a : Pair) (R : ℝ),
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ≠ 0 ∧
      0 < R ∧
      0 <
        κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
          (2 * Fintype.card Link) ∧
      κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
          (2 * Fintype.card Link) ≤
        Measure.real outer (Ball a R) ∧
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2) ^ 2 *
        Measure.real outer (Ball a R) ≤
          S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨a, R, ha, hR, _hPositive, _hFloor, hMoment⟩ :=
    p4Q2PZ37ADM_originalEveryLink_radialMomentWitness H e
  exact ⟨a, R, ha, hR,
    p4Q2PZ37AEA_explicitFloor_pos H R hR,
    p4Q2PZ37AEA_originalFullBall_mass_ge_explicit H a R hR,
    hMoment⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEA_scaledRadius_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEA_scaledRadialMass_ge_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEA_explicitFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEA_explicitFloor_le_radialPower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEA_originalFullBall_mass_ge_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEA_originalHalfBall_mass_ge_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEA_originalEveryLink_explicitMomentWitness
