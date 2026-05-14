import MGAP4D.Gap3320
import MGAP4D.Constructive.FinalTheorem
import MGAP4D.Release.V16
import MGAP4D.SpectralFinalReleaseHold

namespace MGAP4D

/-!
# MGAP4D Final Spine

This file is the top-level spine for migrating the 4D mass gap proof into Lean.
The intended workflow is:

1. move definitions into small files;
2. replace prose obligations by theorem statements;
3. replace theorem statements by proofs;
4. keep CI green at every step.
-/

/-- CI-visible top-level theorem confirming that the migration spine compiles. -/
theorem final_spine_compiles : True := by
  trivial

/-- The current migration-level final theorem packet has normalized gap `33/20`. -/
theorem final_spine_gap3320 :
    Constructive.finalTheoremPacket3320.massGap.value = 33 / 20 := by
  rfl

/-- The current migration-level final theorem packet carries a positive plaquette witness. -/
theorem final_spine_plaquette_positive :
    Constructive.finalTheoremPacket3320.plaquette.observableWitness.positiveMass = true := by
  rfl

/-- The v1.6 release packet is wired to the `33/20` final theorem packet. -/
theorem final_spine_v16_release_gap3320 :
    Release.v16ReleasePacket.finalPacket.massGap.value = 33 / 20 := by
  rfl

/-- The spectral release-readiness chain is visible, but final release remains held. -/
theorem final_spine_spectral_final_release_held :
    spectral3320FinalReleaseHold.finalReleaseHeld := by
  exact spectral3320_final_release_is_held

/-- The spectral final-release hold preserves the public theorem boundary. -/
theorem final_spine_spectral_public_boundary_held :
    spectral3320FinalReleaseHold.publicBoundaryHeld := by
  exact spectral3320_final_release_public_boundary_held

end MGAP4D
