import MGAP4D.R6.Theorem.IntervalExclusionDirectProofReviewSurface
import MGAP4D.R6.Theorem.ExactAtom3320NonDefinitionalDerivation
import MGAP4D.R6.Theorem.ExactAtom3320SpectralOriginFirewall

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R6 bridge from the direct R5 observable review surface to the exact-atom
33/20 carrier-transport lane.

This still does not unlock positive spectral weight, a final mass-gap release,
or a completed non-definitional spectral-origin proof of the value `33 / 20`.
It records that the R5 direct proof has reached the R6 exact-atom lane while
preserving the R4 no-collapse boundary and the R6 spectral-origin firewall. -/
def ExactAtom3320DirectReviewBridgeReady : Prop :=
  IntervalExclusionDirectProofReviewSurfaceReady ∧
  ExactAtom3320R5HandoffInputReady ∧
  ExactAtom3320NonDefinitionalDerivationTarget ∧
  ExactAtom3320SpectralOriginPublicBoundaryHeld ∧
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

/-- The R6 direct-review bridge reaches the exact-atom carrier-transport lane. -/
theorem exact_atom_3320_direct_review_bridge_ready :
    ExactAtom3320DirectReviewBridgeReady := by
  exact ⟨
    interval_exclusion_direct_proof_review_surface_ready,
    exact_atom_3320_r5_handoff_input_ready,
    exact_atom_3320_nondefinitional_derivation_target_ready,
    exact_atom_3320_spectral_origin_public_boundary_held,
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
    ⟨_hdirect, _hhandoff, _htarget, _hfirewall, _hlaws, hvalue, _hinAtom, _hnoWeight, _hr4⟩
  exact hvalue

/-- Projection: R6 direct review reaches atom membership for the exact value. -/
theorem exact_atom_3320_direct_review_bridge_value_mem_atom :
    MGAP4D.MathlibAnalytic.exactGapValueReal ∈
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom := by
  rcases exact_atom_3320_direct_review_bridge_ready with
    ⟨_hdirect, _hhandoff, _htarget, _hfirewall, _hlaws, _hvalue, hinAtom, _hnoWeight, _hr4⟩
  exact hinAtom

/-- Projection: the direct-review bridge keeps the value-origin firewall visible. -/
theorem exact_atom_3320_direct_review_bridge_spectral_origin_firewall :
    ExactAtom3320SpectralOriginPublicBoundaryHeld := by
  rcases exact_atom_3320_direct_review_bridge_ready with
    ⟨_hdirect, _hhandoff, _htarget, hfirewall, _hlaws, _hvalue, _hinAtom, _hnoWeight, _hr4⟩
  exact hfirewall

/-- Boundary: the direct exact-atom bridge still does not consume positive
spectral weight. -/
theorem exact_atom_3320_direct_review_bridge_does_not_consume_positive_weight :
    ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary := by
  rcases exact_atom_3320_direct_review_bridge_ready with
    ⟨_hdirect, _hhandoff, _htarget, _hfirewall, _hlaws, _hvalue, _hinAtom, hnoWeight, _hr4⟩
  exact hnoWeight

end

end Theorem
end R6
end MGAP4D
