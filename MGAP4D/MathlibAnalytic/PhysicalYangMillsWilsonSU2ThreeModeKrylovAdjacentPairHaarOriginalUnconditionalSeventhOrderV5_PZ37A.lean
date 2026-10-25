import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSixthWardTransportV5_PZ36I
import Mathlib.Tactic

/-!
# P4-Q2-PZ37A — original literal Wilson minor has unconditional seventh-order bound

PZ36I proved the full ORIGINAL physical sixth Ward obstruction identically
zero for all finite spatial periods from true one/two-slab SU(2) Haar
and the actual PZ23/PX source definitions.

Previously PZ8 could only prove the physical literal interacting Wilson
minor's O(beta^7) remainder **conditionally** on this sixth Ward zero.
This module eliminates that hypothesis by the actual PZ36I theorem.
The source physical kernel, Haar and Wilson action are not replaced.

No numerical seventh coefficient, sign, positivity, rank-three physical
mode or continuum mass gap is claimed. In particular the previously
hypothesized -Vandermonde/512 is NOT treated as an unconditional theorem.
-/

namespace MGAP4D.MathlibAnalytic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

namespace GroundStatePosteriorJoint

/-- The GENUINE interacting original Wilson three-boundary minor
has an unconditional seventh-order bound, with the exact finite
physical-action small-coupling domain already established in PZ8.
The constant K may depend on H and the physical boundaries.
No seventh coefficient value is identified. -/
theorem p4Q2PZ37A_originalLiteralMinor_unconditional_seventhOrder
    (H : ℕ)
    (A B C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ beta : ℝ, ‖beta‖ ≤ 1 →
        ‖beta * (2 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)‖ ≤ 1 →
          ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C‖ ≤
            K * ‖beta‖ ^ 7 := by
  exact p4Q2PZ8_originalLiteralMinor_seventhOrder_of_sixthWardZero H A B C
    (p4Q2PZ36I_originalSixthWard_unconditional_zero H A B C)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37A_originalLiteralMinor_unconditional_seventhOrder
