import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSeventhVandermondeObstructionV5_PZ37C
import Mathlib.Tactic

/-!
# P4-Q2-PZ37D — genuine SU(2) sixth Haar Vandermonde source

All observables use the ORIGINAL SU(2) spatial Wilson half-action
w(X), the physical crossing action Cross(X,B), and the ORIGINAL
normalized spatial Haar measure. The scalar r labels two auxiliary
observable weights on the same model; no posterior is replaced.

The exact sixth-power difference between r=2 and r=1 has coefficients
6,45,140,225,186,63. Original first-crossing gauge-Haar invariance
annihilates the last two terms in a boundary DIFFERENCE, leaving exactly
the four genuine sixth mixed Haar sectors F(1,5), F(2,4), F(3,3),
and F(4,2) as the Vandermonde obstruction.

This module does NOT assume these high sectors vanish. Transport of
this one-Haar sixth obstruction to the actual two-slab sixth action
moment remains a separate physical theorem. No new axiom, sorry,
admit, native_decide proof substitute, volume-uniform claim, or gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint
section OriginalSixthHaarSource

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "I" => (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
  (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- Genuine mixed Wilson half-action / crossing Haar moment. -/
noncomputable def p4Q2PZ37D_originalMixedHaar
    (i j : ℕ) (B : Cfg) : ℝ :=
  ∫ X : Cfg, (w X)^i * (Cross X B)^j ∂haar

local notation "F" => p4Q2PZ37D_originalMixedHaar H

/-- True sixth spatial Haar moment for the scaled original observable
r*w(X)+Cross(X,B), not a substitute Wilson kernel. -/
noncomputable def p4Q2PZ37D_originalScaledStrippedSixth
    (r : ℝ) (B : Cfg) : ℝ :=
  ∫ X : Cfg, (r*w X+Cross X B)^6 ∂haar

local notation "U6" => p4Q2PZ37D_originalScaledStrippedSixth H

/-- Exact genuine sixth-moment binomial expansion via Mathlib and
the pre-existing physical PZ36A Haar binomial integration theorem. -/
theorem p4Q2PZ37D_originalScaledSixth_binomial
    (r : ℝ) (B : Cfg) :
    U6 r B =
      r^6*F 6 0 B + 6*r^5*F 5 1 B +
        15*r^4*F 4 2 B + 20*r^3*F 3 3 B +
          15*r^2*F 2 4 B + 6*r*F 1 5 B + F 0 6 B := by
  have hw : Continuous (fun X : Cfg => w X) :=
    p4Q2PZ36C_half_continuous H
  have hc : Continuous (fun X : Cfg => Cross X B) :=
    p4Q2PZ36C_cross_continuous H B
  have hr : Continuous (fun X : Cfg => r*w X) :=
    continuous_const.mul hw
  unfold p4Q2PZ37D_originalScaledStrippedSixth
  rw [p4Q2PZ36A_originalHaar_integral_binomial H
    (fun X : Cfg => r*w X) (fun X : Cfg => Cross X B)
      hr hc 6]
  have hTerms :
      (∑ k ∈ Finset.range 7, ((6 : ℕ).choose k : ℝ) *
        (∫ X : Cfg, (r*w X)^k*(Cross X B)^(6-k) ∂haar)) =
      ∑ k ∈ Finset.range 7, ((6 : ℕ).choose k : ℝ) *
        r^k * F k (6-k) B := by
    apply Finset.sum_congr rfl
    intro k _hk
    change ((6 : ℕ).choose k : ℝ) *
      (∫ X : Cfg, (r*w X)^k * (Cross X B)^(6-k) ∂haar) =
      ((6 : ℕ).choose k : ℝ) * r^k *
        (∫ X : Cfg, (w X)^k*(Cross X B)^(6-k) ∂haar)
    simp only [mul_pow, mul_assoc, integral_const_mul]
    ring
  rw [hTerms]
  simp [Finset.sum_range_succ, Nat.choose]
  ring

/-- No omitted sixth-Haar sectors: the 2-minus-1 original observable
difference is literally the weighted sum of six original Haar moments. -/
theorem p4Q2PZ37D_originalScaledSixth_gap_explicit
    (B : Cfg) :
    U6 2 B - U6 1 B =
      6*F 1 5 B + 45*F 2 4 B + 140*F 3 3 B +
        225*F 4 2 B + 186*F 5 1 B + 63*F 6 0 B := by
  rw [p4Q2PZ37D_originalScaledSixth_binomial H 2 B,
    p4Q2PZ37D_originalScaledSixth_binomial H 1 B]
  ring

/-- Two high sixth-Haar sectors are genuinely boundary-independent:
the fifth spatial weight times one crossing by physical PZ36A Haar,
and pure w^6 since it has no boundary crossing. -/
theorem p4Q2PZ37D_highSelected_invariant
    (A B : Cfg) :
    F 5 1 B = F 5 1 A ∧ F 6 0 B = F 6 0 A := by
  constructor
  · have hB :=
      p4Q2PZ36A_originalSpatialPower_oneCrossing_invariant H 5 B
    have hA :=
      p4Q2PZ36A_originalSpatialPower_oneCrossing_invariant H 5 A
    simp only [p4Q2PZ37D_originalMixedHaar, pow_one] at *
    exact hB.trans hA.symm
  · simp only [p4Q2PZ37D_originalMixedHaar, pow_zero, mul_one]

/-- Genuine B-A sixth difference: only four HIGH original SU(2)
Haar moments survive. This is an unconditional physical identity. -/
theorem p4Q2PZ37D_originalSixthGap_boundaryDifference
    (A B : Cfg) :
    (U6 2 B - U6 1 B) - (U6 2 A - U6 1 A) =
      6*(F 1 5 B-F 1 5 A) + 45*(F 2 4 B-F 2 4 A) +
        140*(F 3 3 B-F 3 3 A) + 225*(F 4 2 B-F 4 2 A) := by
  obtain ⟨h51,h60⟩ := p4Q2PZ37D_highSelected_invariant H A B
  rw [p4Q2PZ37D_originalScaledSixth_gap_explicit H B,
      p4Q2PZ37D_originalScaledSixth_gap_explicit H A]
  rw [h51, h60]
  ring

/-- The actual sixth SU(2) Haar source for the old Vandermonde route
is a four-sector original-Haar wedge. This is not yet the literal
Wilson minor's O(beta^8) asymptotic coefficient. -/
theorem p4Q2PZ37D_originalScaledSixthGap_wedge_fourSectors
    (A B C : Cfg) :
    p4Q2PZ37B_originalBoundaryWedge H w
      (fun D : Cfg => U6 2 D - U6 1 D) A B C =
    p4Q2PZ37B_originalBoundaryWedge H w
      (fun D : Cfg =>
        6*F 1 5 D + 45*F 2 4 D + 140*F 3 3 D + 225*F 4 2 D)
      A B C := by
  unfold p4Q2PZ37B_originalBoundaryWedge
  rw [p4Q2PZ37D_originalSixthGap_boundaryDifference H A B,
    p4Q2PZ37D_originalSixthGap_boundaryDifference H A C]
  ring

end OriginalSixthHaarSource
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37D_originalScaledSixth_binomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37D_originalScaledSixth_gap_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37D_highSelected_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37D_originalSixthGap_boundaryDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37D_originalScaledSixthGap_wedge_fourSectors
