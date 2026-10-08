import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarNormalizedFrozenSqrtRatioL2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumRetainedWitnessPythagoras
import Mathlib.Tactic

/-!
# P4-Q1: true original joint L² bridge for the already-proved sqrt-ratio candidate

PR #5307 supplied the concrete canonical original Wilson one-right-link
sqrt-density ratio r_e in the ORIGINAL ordered pair-Haar L² and proved
the exact Hilbert estimate
  ‖1 - r_e‖² ≤ (exp(16 beta) - 1)²,
uniform in the single link and spatial extent H.

This file REUSES that proof, rather than reconstructing it, and
transports r_e using the EXACT original half-density linear isometry
U_beta. Thus the approximation is a genuine vector in the ORIGINAL
physical ground-state Wilson JOINT law, with identical norm loss.

We also display the explicit finite-volume all-link cardinality
bound. It is NOT volume independent: obtaining a bound for the full
posterior L² residual SUM remains a separate quantitative task.
The transported candidate's retained-sigma-algebra measurability
is not assumed here; its a.e. physical representative requires a
separate proof. No Dobrushin, replacement posterior, new axiom,
sorry/admit, or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4Q1JointTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q1JointCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q1JointSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q1JointMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q1JointBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q1JointSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Unregularized true original-Wilson-joint L² approximant obtained
by the already-existing U_beta from the ORIGINAL pair-Haar ratio
r_e of #5307. This is not an alternate physical law or vacuum. -/
noncomputable def originalWilsonCanonicalRightLinkJointVacuumApproximant
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H 2 (Nat.zero_lt_succ 1) beta hbeta :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H 2 (Nat.zero_lt_succ 1) beta hbeta)
    (originalWilsonNormalizedFrozenRightLinkSqrtRatioL2
      H beta hbeta e)

/-- The genuine ORIGINAL posterior-joint L² approximation error
is bounded by (exp(16 beta)-1)² per link and independently of H.
This uses only the exact original half-density isometry and #5307. -/
theorem originalWilsonCanonicalRightLinkJointVacuumApproximant_error_sq_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ‖originalGroundStateJointTransportedPairHaarOne H 2
        (Nat.zero_lt_succ 1) beta hbeta -
      originalWilsonCanonicalRightLinkJointVacuumApproximant
        H beta hbeta e‖ ^ 2 ≤
      (Real.exp (16 * beta) - 1) ^ 2 := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H 2 (Nat.zero_lt_succ 1) beta hbeta
  let one : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2 :=
    Lp.const 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
      (1 : ℝ)
  let q := originalWilsonNormalizedFrozenRightLinkSqrtRatioL2 H beta hbeta e
  change ‖U one - U q‖ ^ 2 ≤ _
  rw [← map_sub, U.norm_map]
  exact originalWilsonNormalizedFrozenRightLinkSqrtRatioL2_error_sq_le
    H beta hbeta e

/-- Honest finite-volume full-link error sum bound for explicit
isometric Wilson candidates. The spatial-link cardinality appears;
this is NOT a volume-uniform posterior-vacuum residual estimate. -/
theorem originalWilsonCanonicalRightLinkJointVacuumApproximant_fullError_le_card
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖originalGroundStateJointTransportedPairHaarOne H 2
          (Nat.zero_lt_succ 1) beta hbeta -
        originalWilsonCanonicalRightLinkJointVacuumApproximant
          H beta hbeta e‖ ^ 2) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (Real.exp (16 * beta) - 1) ^ 2 := by
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖originalGroundStateJointTransportedPairHaarOne H 2
          (Nat.zero_lt_succ 1) beta hbeta -
        originalWilsonCanonicalRightLinkJointVacuumApproximant
          H beta hbeta e‖ ^ 2) ≤
      ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H,
        (Real.exp (16 * beta) - 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro e _he
      exact originalWilsonCanonicalRightLinkJointVacuumApproximant_error_sq_le
        H beta hbeta e
    _ = (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          (Real.exp (16 * beta) - 1) ^ 2 := by simp

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
