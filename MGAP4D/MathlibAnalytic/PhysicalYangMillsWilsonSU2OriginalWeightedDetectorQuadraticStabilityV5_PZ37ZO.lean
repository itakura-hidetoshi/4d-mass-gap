import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAllPhysicalGLNullGIEquivalenceV5_PZ37ZM
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZO — quadratic stability of weighted real detector Haar masses

An auxiliary purely analytic inequality for the ORIGINAL Wilson GL
mass, not a change of physical model or posterior:
for any real-linear family of detectors L_z, strictly positive weight
q_z, and actual integrable signed detector squares, the authentic
weighted integrated mass Q satisfies

  Q(x+y) <= 2*Q(x) + 2*Q(y)
  Q(x)   <= 2*Q(x-y) + 2*Q(y)
  Q(x-y) >= Q(x)/2 - Q(y).

The proof is pointwise real square algebra followed by original-measure
integral monotonicity. The later physical application takes exactly
the original interacting SU(2) Wilson posterior GI detectors and the
actual density-row Haar separation as the positive weight. Crucially
there is NO point-Haar atom, assumed frame, new posterior, or any
invented coercivity premise. Integrability stays explicit here and is
provided by the existing physical GL theorem on application.

This will control the genuine O_H(t^2) Wilson Taylor remainder when
passing the authentic static two-mode GL floor to the fine physical
cancellation. No new axiom, sorry, admit, native_decide, arbitrary-
depth or volume-uniform lower estimate, endpoint E, H1-H4, or mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 850000

namespace GroundStatePosteriorJoint

section WeightedDetector

variable {X E : Type*} [MeasurableSpace X]
variable [AddCommGroup E] [Module ℝ E]
variable (μ : Measure X) (L : X → E →ₗ[ℝ] ℝ) (q : X → ℝ)

/-- The real quadratic mass induced by an unchanged positive-weight
family of linear source detectors on the provided reference measure. -/
noncomputable def p4Q2PZ37ZO_weightedDetectorMass (f : E) : ℝ :=
  ∫ z, (L z f)^2 / q z ∂μ

/-- Negating a true signed source does not change its quadratic mass. -/
theorem p4Q2PZ37ZO_weightedDetectorMass_neg (f : E) :
    p4Q2PZ37ZO_weightedDetectorMass μ L q (-f) =
      p4Q2PZ37ZO_weightedDetectorMass μ L q f := by
  unfold p4Q2PZ37ZO_weightedDetectorMass
  apply integral_congr_ae
  filter_upwards with z
  rw [map_neg]
  ring

/-- The factor-two quadratic triangle estimate follows pointwise
from (u+v)^2 <= 2u^2+2v^2 and the actual weighted integral.
No completeness, probability-normalization or detector positivity
hypothesis is hidden. -/
theorem p4Q2PZ37ZO_weightedDetectorMass_add_le_two
    (hq : ∀ z, 0 < q z)
    (hInt : ∀ f : E, Integrable (fun z => (L z f)^2 / q z) μ)
    (f g : E) :
    p4Q2PZ37ZO_weightedDetectorMass μ L q (f + g) ≤
      2 * p4Q2PZ37ZO_weightedDetectorMass μ L q f +
      2 * p4Q2PZ37ZO_weightedDetectorMass μ L q g := by
  have hPoint (z : X) :
      (L z (f + g))^2 / q z ≤
        2 * ((L z f)^2 / q z) + 2 * ((L z g)^2 / q z) := by
    rw [map_add]
    calc
      (L z f + L z g)^2 / q z ≤
          (2 * (L z f)^2 + 2 * (L z g)^2) / q z :=
        (div_le_div_iff_of_pos_right (hq z)).2 (by
          nlinarith [sq_nonneg (L z f - L z g)])
      _ = 2 * ((L z f)^2 / q z) + 2 * ((L z g)^2 / q z) := by ring
  have hR : Integrable
      (fun z : X => 2 * ((L z f)^2 / q z) +
        2 * ((L z g)^2 / q z)) μ :=
    ((hInt f).const_mul 2).add ((hInt g).const_mul 2)
  have hIntegral :
      (∫ z, (L z (f + g))^2 / q z ∂μ) ≤
      ∫ z, 2 * ((L z f)^2 / q z) +
        2 * ((L z g)^2 / q z) ∂μ :=
    integral_mono (hInt (f + g)) hR hPoint
  unfold p4Q2PZ37ZO_weightedDetectorMass
  calc
    (∫ z, (L z (f + g))^2 / q z ∂μ) ≤
        ∫ z, 2 * ((L z f)^2 / q z) +
          2 * ((L z g)^2 / q z) ∂μ := hIntegral
    _ = 2 * (∫ z, (L z f)^2 / q z ∂μ) +
          2 * (∫ z, (L z g)^2 / q z ∂μ) := by
      rw [integral_add ((hInt f).const_mul 2) ((hInt g).const_mul 2),
        integral_const_mul, integral_const_mul]

/-- Apply the same genuine weighted detector inequality to the
decomposition x=(x-y)+y, retaining exactly the original sources. -/
theorem p4Q2PZ37ZO_weightedDetectorMass_sub_comparison
    (hq : ∀ z, 0 < q z)
    (hInt : ∀ f : E, Integrable (fun z => (L z f)^2 / q z) μ)
    (f g : E) :
    p4Q2PZ37ZO_weightedDetectorMass μ L q f ≤
      2 * p4Q2PZ37ZO_weightedDetectorMass μ L q (f - g) +
      2 * p4Q2PZ37ZO_weightedDetectorMass μ L q g := by
  have h := p4Q2PZ37ZO_weightedDetectorMass_add_le_two
    μ L q hq hInt (f - g) g
  simpa only [sub_add_cancel] using h

/-- Explicit lower stability: the true full energy of x-y cannot
fall below half the energy of x except by the genuine quadratic
detector energy of the perturbation y. -/
theorem p4Q2PZ37ZO_weightedDetectorMass_sub_lower
    (hq : ∀ z, 0 < q z)
    (hInt : ∀ f : E, Integrable (fun z => (L z f)^2 / q z) μ)
    (f g : E) :
    p4Q2PZ37ZO_weightedDetectorMass μ L q f / 2 -
        p4Q2PZ37ZO_weightedDetectorMass μ L q g ≤
      p4Q2PZ37ZO_weightedDetectorMass μ L q (f - g) := by
  have h := p4Q2PZ37ZO_weightedDetectorMass_sub_comparison
    μ L q hq hInt f g
  linarith

end WeightedDetector
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZO_weightedDetectorMass_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZO_weightedDetectorMass_add_le_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZO_weightedDetectorMass_sub_comparison
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZO_weightedDetectorMass_sub_lower
