import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarZeroModeHellingerCovarianceV5_HV
import Mathlib.Tactic

/-!
# P4-Q2-HW: relative half-density receiver and true normalized gap

GR already writes the ORIGINAL interacting-Wilson FF relative signed source
receiver as L*(T(h)-sqrt(p_b(h))/sqrt(p_b(g))*T(g)), where T is the
original source-dependent Wilson transfer, b is the physical left
boundary and p_b is its genuine normalized interacting Wilson
conditional density. GI computes the difference of the two ORIGINAL
conditional expectations as the Haar pairing against p_0-p_1.

This file isolates the exact integral algebra, for arbitrary compact
finite-measure spaces and normalized positive continuous densities.
The constant T(h) cancels because the two actual normalized posterior
densities have identical Haar integral. The remainder is precisely
  -L*sqrt(p_b(h)) * int T(g)*(p_0(g)-p_1(g))/sqrt(p_b(g)) dmu.
For strictly positive T and L, HV proves these remainders for the two
left boundaries CANNOT BOTH vanish if the densities differ.

The abstract bridge adds no source-frame, fake Haar conditional or
Dobrushin input. Specializing this to the literal original-Wilson
physical source, continuity of the actual zero-mode transfer and the
posterior normalization identities are separate obligations; they
must not be silently assumed verified by this generic theorem.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

namespace GroundStatePosteriorJoint

section AbstractRelativeReceiver

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Exact identity for a genuine two-posterior normalized expectation
gap of GR's relative half-density receiver. The T(h) constant term
vanishes because the two physical probability density rows have
the SAME normalization with respect to their common Haar reference. -/
theorem p4Q2HW_relative_receiver_expectation_gap_eq_weighted_projection
    (μ : Measure X) [IsFiniteMeasure μ]
    (T P0 P1 Q : X → ℝ)
    (hT : Continuous T) (hP0 : Continuous P0)
    (hP1 : Continuous P1) (hQ : Continuous Q)
    (hQpos : ∀ x, 0 < Q x)
    (hEqualMass : (∫ x, P0 x ∂μ) = (∫ x, P1 x ∂μ))
    (L : ℝ) (h : X) :
    (∫ g, (L * (T h - Real.sqrt (Q h) / Real.sqrt (Q g) * T g)) *
          (P0 g - P1 g) ∂μ) =
      (-L * Real.sqrt (Q h)) *
        (∫ g, (T g * (P0 g - P1 g) / Real.sqrt (Q g)) ∂μ) := by
  have hD : Integrable (fun g : X => P0 g - P1 g) μ :=
    (hP0.sub hP1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP0Int : Integrable P0 μ :=
    hP0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP1Int : Integrable P1 μ :=
    hP1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQsqrt : Continuous (fun g : X => Real.sqrt (Q g)) :=
    Real.continuous_sqrt.comp hQ
  have hDivCont : Continuous (fun g : X =>
      T g * (P0 g - P1 g) / Real.sqrt (Q g)) :=
    (hT.mul (hP0.sub hP1)).div hQsqrt
      (fun g => (Real.sqrt_pos.mpr (hQpos g)).ne')
  have hDivInt : Integrable (fun g : X =>
      T g * (P0 g - P1 g) / Real.sqrt (Q g)) μ :=
    hDivCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLeftInt : Integrable (fun g : X =>
      (L * T h) * (P0 g - P1 g)) μ := hD.const_mul _
  have hRightInt : Integrable (fun g : X =>
      (L * Real.sqrt (Q h)) *
        (T g * (P0 g - P1 g) / Real.sqrt (Q g))) μ :=
    hDivInt.const_mul _
  have hDzero : (∫ g, (P0 g - P1 g) ∂μ) = 0 := by
    rw [integral_sub hP0Int hP1Int]
    exact sub_eq_zero.mpr hEqualMass
  calc
    (∫ g, (L * (T h - Real.sqrt (Q h) / Real.sqrt (Q g) * T g)) *
          (P0 g - P1 g) ∂μ) =
      ∫ g, ((L * T h) * (P0 g - P1 g) -
        (L * Real.sqrt (Q h)) *
          (T g * (P0 g - P1 g) / Real.sqrt (Q g))) ∂μ := by
        apply integral_congr_ae
        filter_upwards with g
        ring
    _ = (L * T h) * (∫ g, P0 g - P1 g ∂μ) -
        (L * Real.sqrt (Q h)) *
          (∫ g, T g * (P0 g - P1 g) / Real.sqrt (Q g) ∂μ) := by
        rw [integral_sub hLeftInt hRightInt,
          integral_const_mul, integral_const_mul]
    _ = (-L * Real.sqrt (Q h)) *
        (∫ g, T g * (P0 g - P1 g) / Real.sqrt (Q g) ∂μ) := by
        rw [hDzero]
        ring

/-- Both genuine normalized relative receiver gaps cannot vanish:
the strictly positive HV Hellinger covariance forces at least one
two-posterior expected receiver contrast to be nonzero, for EVERY h.
This does not follow from positivity of a separate receiver square. -/
theorem p4Q2HW_two_normalized_relative_receiver_gaps_not_both_zero
    (μ : Measure X) [IsFiniteMeasure μ]
    (hFull : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < μ U)
    (T P0 P1 : X → ℝ) (L : ℝ)
    (hT : Continuous T) (hP0 : Continuous P0)
    (hP1 : Continuous P1)
    (hTpos : ∀ x, 0 < T x)
    (hP0pos : ∀ x, 0 < P0 x)
    (hP1pos : ∀ x, 0 < P1 x)
    (hDifferent : ∃ x, P0 x ≠ P1 x)
    (hEqualMass : (∫ x, P0 x ∂μ) = (∫ x, P1 x ∂μ))
    (hL : 0 < L) (h : X) :
    (∫ g, (L * (T h - Real.sqrt (P0 h) / Real.sqrt (P0 g) * T g)) *
      (P0 g - P1 g) ∂μ) ≠ 0 ∨
    (∫ g, (L * (T h - Real.sqrt (P1 h) / Real.sqrt (P1 g) * T g)) *
      (P0 g - P1 g) ∂μ) ≠ 0 := by
  have hGap0 :=
    p4Q2HW_relative_receiver_expectation_gap_eq_weighted_projection
      μ T P0 P1 P0 hT hP0 hP1 hP0 hP0pos hEqualMass L h
  have hGap1 :=
    p4Q2HW_relative_receiver_expectation_gap_eq_weighted_projection
      μ T P0 P1 P1 hT hP0 hP1 hP1 hP1pos hEqualMass L h
  have hHV :=
    p4Q2HV_two_sqrt_density_weighted_projections_cannot_both_vanish
      μ hFull T P0 P1 hT hP0 hP1 hTpos hP0pos hP1pos hDifferent
  have hFactor0 : (-L * Real.sqrt (P0 h)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hL))
      (ne_of_gt (Real.sqrt_pos.mpr (hP0pos h)))
  have hFactor1 : (-L * Real.sqrt (P1 h)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hL))
      (ne_of_gt (Real.sqrt_pos.mpr (hP1pos h)))
  rcases hHV with hJ0 | hJ1
  · left
    rw [hGap0]
    exact mul_ne_zero hFactor0 hJ0
  · right
    rw [hGap1]
    exact mul_ne_zero hFactor1 hJ1

end AbstractRelativeReceiver
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HW_relative_receiver_expectation_gap_eq_weighted_projection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HW_two_normalized_relative_receiver_gaps_not_both_zero
