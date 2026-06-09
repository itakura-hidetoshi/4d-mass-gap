import MGAP4D.R6.Theorem.IntervalExclusionDirectProofReviewSurface
import MGAP4D.R6.Theorem.ExactAtom3320NonDefinitionalDerivation
import MGAP4D.R6.Theorem.ExactAtom3320SpectralOriginFirewall
import MGAP4D.R6.Theorem.ExactAtom3320ValueOriginQuarantine

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R6 bridge from the direct R5 observable review surface to the exact-atom
33/20 audit lane.

This bridge does **not** prove a non-definitional spectral origin for the value
`33 / 20`.  The value-origin route is explicitly quarantined: the carrier-level
numeric equality is visible, but it cannot be pushed into the observable-atom or
PVM-mass lane and counted as a spectral derivation. -/
def ExactAtom3320DirectReviewBridgeReady : Prop :=
  IntervalExclusionDirectProofReviewSurfaceReady ∧
  ExactAtom3320R5HandoffInputReady ∧
  ExactAtom3320NonDefinitionalDerivationTarget ∧
  ExactAtom3320ValueOriginBlocked ∧
  (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable) ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal ∈
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R6 direct-review bridge reaches the exact-atom audit lane while keeping
value-origin quarantine active. -/
theorem exact_atom_3320_direct_review_bridge_ready :
    ExactAtom3320DirectReviewBridgeReady := by
  exact ⟨
    interval_exclusion_direct_proof_review_surface_ready,
    exact_atom_3320_r5_handoff_input_ready,
    exact_atom_3320_nondefinitional_derivation_target_ready,
    exact_atom_3320_value_origin_blocked_ready,
    interval_exclusion_direct_proof_review_surface_atom_chosen_laws,
    exact_atom_3320_value_eq,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_exact_value_in_atom,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Projection: the direct R5 review surface is available in the exact atom lane. -/
theorem exact_atom_3320_direct_review_bridge_has_direct_surface :
    IntervalExclusionDirectProofReviewSurfaceReady := by
  exact exact_atom_3320_direct_review_bridge_ready.1

/-- Projection: the exact carrier value remains equal to 33/20. -/
theorem exact_atom_3320_direct_review_bridge_value_eq :
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  rcases exact_atom_3320_direct_review_bridge_ready with
    ⟨_hdirect, _hhandoff, _htarget, _hblocked, _hlaws, hvalue, _hinAtom, _hnoWeight, _hr4⟩
  exact hvalue

/-- Projection: R6 direct review reaches atom membership for the exact value. -/
theorem exact_atom_3320_direct_review_bridge_value_mem_atom :
    MGAP4D.MathlibAnalytic.exactGapValueReal ∈
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom := by
  rcases exact_atom_3320_direct_review_bridge_ready with
    ⟨_hdirect, _hhandoff, _htarget, _hblocked, _hlaws, _hvalue, hinAtom, _hnoWeight, _hr4⟩
  exact hinAtom

/-- Projection: the direct-review bridge keeps the value-origin quarantine active. -/
theorem exact_atom_3320_direct_review_bridge_value_origin_blocked :
    ExactAtom3320ValueOriginBlocked := by
  rcases exact_atom_3320_direct_review_bridge_ready with
    ⟨_hdirect, _hhandoff, _htarget, hblocked, _hlaws, _hvalue, _hinAtom, _hnoWeight, _hr4⟩
  exact hblocked

/-- Boundary: the direct exact-atom bridge still does not consume positive
spectral weight. -/
theorem exact_atom_3320_direct_review_bridge_does_not_consume_positive_weight :
    ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary := by
  rcases exact_atom_3320_direct_review_bridge_ready with
    ⟨_hdirect, _hhandoff, _htarget, _hblocked, _hlaws, _hvalue, _hinAtom, hnoWeight, _hr4⟩
  exact hnoWeight

end

end Theorem
end R6
end MGAP4D
