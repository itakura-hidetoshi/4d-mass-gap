import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCovarianceExplicitMomentFloorV5_PZ37AEB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEC — genuine SU(2) radius-polynomial Haar and covariance floor

The pinned mathlib HaarToSphere definition, not an assumed numerical
covering constant, gives for EVERY positive radius:
  toSphereBallBound 4 r / 4 = (min r 2 / 4)^4.

AEC unfolds this exact FIXED definition on the already proved
unchanged original normalized SU(2) Haar and original boundary pair-Haar.
Thus the actual finite-H full all-link ball has the elementary bound
  (min (R/(2*card(Link_H)+1)) 2 / 4)^(8*card(Link_H)).
For the concrete full-ball radius R=1/2 this is exactly
  (1/(8*(2*card(Link_H)+1)))^(8*card(Link_H)).
The AEB original physical Wilson covariance-square moment obtains
this same explicit polynomial factor, with the real radius/amplitude
stability certificate kept visible.

No substitute gauge law, phantom Haar, new physical Lipschitz assumption,
altered centered Gauss-law source/FF receiver/posteriors, modified physical
boundary pair-Haar, H-uniform coercivity, numerical amplitude/modulus,
or continuum four-dimensional Yang-Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "κ" => p4Q2PZ37ADQ_sphereRadiusFraction

/-- FIXED pinned-mathlib closed polynomial for every positive radius,
including the large-radius saturation branch. -/
theorem p4Q2PZ37AEC_originalKappa_eq_minQuartic
    (r : ℝ) (hr : 0 < r) :
    κ r = (min r 2 / 4) ^ 4 := by
  unfold p4Q2PZ37ADQ_sphereRadiusFraction Measure.toSphereBallBound
  have hif : (4 : ℕ) ≠ 0 ∧ 0 < r := ⟨by decide, hr⟩
  rw [if_pos hif]
  -- The pinned coercion simplifier pushes the cast THROUGH min.
  -- Rewrite the resulting Real.toNNReal coercion, not the old outer cast.
  push_cast
  rw [Real.coe_toNNReal r hr.le]
  ring

/-- Below the exact unit S³ chordal diameter 2,
the genuine original Haar floor is an ordinary fourth power. -/
theorem p4Q2PZ37AEC_originalKappa_eq_smallQuartic
    (r : ℝ) (hr : 0 < r) (hr2 : r ≤ 2) :
    κ r = (r / 4) ^ 4 := by
  rw [p4Q2PZ37AEC_originalKappa_eq_minQuartic r hr, min_eq_left hr2]

/-- The fixed mathlib lower certificate saturates at 1/16 for
positive radius at least 2. This is a lower bound, not the actual Haar mass. -/
theorem p4Q2PZ37AEC_originalKappa_largeRadius
    (r : ℝ) (hr2 : 2 ≤ r) :
    κ r = 1 / 16 := by
  have hr : 0 < r := by linarith
  rw [p4Q2PZ37AEC_originalKappa_eq_minQuartic r hr, min_eq_right hr2]
  norm_num

/-- A concrete rational one-link bound in the original normalized
SU(2) Haar, without a numerical spherical-cover cardinal assumption. -/
theorem p4Q2PZ37AEC_originalRadialMass_atOne_ge_oneOver256 :
    (1 / 256 : ℝ) ≤
      p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass 1 := by
  have h := p4Q2PZ37ADZ_originalRadialMass_ge_explicit 1 (by norm_num)
  rw [p4Q2PZ37AEC_originalKappa_eq_smallQuartic 1 (by norm_num) (by norm_num)] at h
  norm_num at h ⊢
  exact h

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "Ball" => p4Q2PZ37ADL_originalFullBoundaryChordalBall H
local notation "b₀" => p4Q2PZ37ADC_fixedCoupling
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H

local instance p4Q2PZ37AEC_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AEC_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Exactly the 8*card(Link_H) exponent after composing the
4-dimensional sphere quartic with the TWO original boundary fields. -/
theorem p4Q2PZ37AEC_originalFullFloor_eq_minPolynomial
    (R : ℝ) (hR : 0 < R) :
    κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link) =
      (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
        (8 * Fintype.card Link) := by
  rw [p4Q2PZ37AEC_originalKappa_eq_minQuartic _
    (p4Q2PZ37AEA_scaledRadius_pos H R hR)]
  rw [← pow_mul]
  congr 1
  omega

/-- The ACTUAL original finite-volume pair-Haar full D_H ball has a
radius-and-link-count-only elementary polynomial lower bound, any center. -/
theorem p4Q2PZ37AEC_originalFullBall_mass_ge_minPolynomial
    (a : Pair) (R : ℝ) (hR : 0 < R) :
    (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
        (8 * Fintype.card Link) ≤
      Measure.real outer (Ball a R) := by
  rw [← p4Q2PZ37AEC_originalFullFloor_eq_minPolynomial H R hR]
  exact p4Q2PZ37AEA_originalFullBall_mass_ge_explicit H a R hR

/-- In the literal R=1/2 original full D_H ball the lower bound is
a fully rational link-count formula, with no unknown covering count. -/
theorem p4Q2PZ37AEC_originalHalfBall_mass_ge_rationalPower
    (a : Pair) :
    (1 / (8 * (2 * (Fintype.card Link : ℝ) + 1))) ^
        (8 * Fintype.card Link) ≤
      Measure.real outer (Ball a (1 / 2)) := by
  have hDen : (0 : ℝ) < 2 * (Fintype.card Link : ℝ) + 1 := by positivity
  have hSmall : (1 / 2 : ℝ) /
      (2 * (Fintype.card Link : ℝ) + 1) ≤ 2 := by
    apply (div_le_iff₀ hDen).mpr
    have hCard : (0 : ℝ) ≤ (Fintype.card Link : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hBase :
      ((1 / 2 : ℝ) / (2 * (Fintype.card Link : ℝ) + 1)) / 4 =
        1 / (8 * (2 * (Fintype.card Link : ℝ) + 1)) := by
    field_simp; ring
  have h := p4Q2PZ37AEC_originalFullBall_mass_ge_minPolynomial
    H a (1 / 2) (by norm_num)
  rw [min_eq_left hSmall, hBase] at h
  exact h

/-- The genuine original covariance-square physical moment admits
the same elementary min-polynomial Haar factor when a verified
physical ball radius and a uniformly valid on-ball amplitude are known. -/
theorem p4Q2PZ37AEC_originalCertifiedBall_minPolynomialMoment
    (e : Link) (a : Pair) (R A : ℝ)
    (hR : 0 < R) (hA : 0 < A)
    (hStable : ∀ z ∈ Ball a R,
      A ≤ |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z|) :
    A ^ 2 *
      (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
        (8 * Fintype.card Link) ≤
      S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  have hMoment :=
    p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
      H e (Ball a R) A
      (p4Q2PZ37ADL_originalFullChordalBall_isOpen H a R)
      hA hStable
  have hHaar :=
    p4Q2PZ37AEC_originalFullBall_mass_ge_minPolynomial H a R hR
  exact (mul_le_mul_of_nonneg_left hHaar (sq_nonneg A)).trans hMoment

/-- Every ORIGINAL physical link, no excluded link or external
nonzero covariance premise, has a true positive witness (a,R).
The right-hand side is the original fixed-coupling physical covariance
second moment; radius R and physical covariance are not numerically evaluated. -/
theorem p4Q2PZ37AEC_originalEveryLink_minPolynomialMomentWitness
    (e : Link) :
    ∃ (a : Pair) (R : ℝ),
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ≠ 0 ∧
      0 < R ∧
      0 <
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2) ^ 2 *
          (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
            (8 * Fintype.card Link) ∧
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2) ^ 2 *
        (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
          (8 * Fintype.card Link) ≤
        S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨a, R, ha, hR, hPositive, hLower⟩ :=
    p4Q2PZ37AEB_originalEveryLink_explicitMomentWitness H e
  have hEq := p4Q2PZ37AEC_originalFullFloor_eq_minPolynomial H R hR
  rw [hEq] at hPositive hLower
  exact ⟨a, R, ha, hR, hPositive, hLower⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEC_originalKappa_eq_minQuartic
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEC_originalKappa_eq_smallQuartic
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEC_originalKappa_largeRadius
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEC_originalRadialMass_atOne_ge_oneOver256
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEC_originalFullFloor_eq_minPolynomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEC_originalFullBall_mass_ge_minPolynomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEC_originalHalfBall_mass_ge_rationalPower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEC_originalCertifiedBall_minPolynomialMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEC_originalEveryLink_minPolynomialMomentWitness
