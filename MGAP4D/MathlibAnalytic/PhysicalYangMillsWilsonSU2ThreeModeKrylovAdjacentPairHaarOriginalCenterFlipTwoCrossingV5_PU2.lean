import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCenterFlipHaarV5_PU
import Mathlib.Tactic

/-!
# P4-Q2-PU2 — original SU(2) Haar free-link cancellation for two crossings

Let target be a true spatial lattice link, distinct from the two
temporal-crossing links e and f. Multiplying the target SU(2) variable
by central -I leaves BOTH genuine crossing plaquette energies
  E(A(e)^{-1}B(e)) * E(A(f)^{-1}B(f))
unchanged. Thus any continuous SU(2) spatial plaquette-profile
observable shown to be odd under that target flip has zero Haar
pairing with this genuine two-crossing term.

This proves the analytic selection rule without silently assuming
that every given plaquette has an available free edge; the latter
four-link geometric fact is a separate finite-lattice theorem.
The original product spatial Haar, Wilson temporal action, and
physical two-posterior transfer remain untouched. No sorry or axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PU2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PU2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PU2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PU2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PU2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalTwoCrossingCenterSelection
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H

/-- An actual temporal Wilson plaquette at spatial link e is pointwise
unchanged by a central flip at a *different* spatial link target. -/
theorem p4Q2PU2_originalCrossingEnergy_unchanged_at_other
    (target e : Link) (he : e ≠ target)
    (A B : Cfg) :
    E (((Flip target A) e)⁻¹ * B e) =
      E ((A e)⁻¹ * B e) := by
  rw [p4Q2PU_originalSingleLinkCenterFlip_other H target e he A]

/-- The literal pair of original SU(2) temporal-crossing energies
is unchanged by a center flip at any third (different) link. -/
theorem p4Q2PU2_originalTwoCrossingEnergy_unchanged
    (target e f : Link) (he : e ≠ target) (hf : f ≠ target)
    (A B : Cfg) :
    E (((Flip target A) e)⁻¹ * B e) *
      E (((Flip target A) f)⁻¹ * B f) =
    E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f) := by
  rw [p4Q2PU2_originalCrossingEnergy_unchanged_at_other H target e he A B,
    p4Q2PU2_originalCrossingEnergy_unchanged_at_other H target f hf A B]

/-- Fully original two-crossing Haar selection rule: an actual
SU(2) plaquette observable known to be odd at a third, free link
has zero pairing with the unmodified product of two crossing energies.
Only the pointwise oddness and disjointness are supplied explicitly;
neither is inserted as an unproved global Wilson axiom. -/
theorem p4Q2PU2_originalOddPlaquette_twoCrossingHaar_zero
    (target e f : Link) (he : e ≠ target) (hf : f ≠ target)
    (obs : Cfg → ℝ) (hobs : Continuous obs)
    (hodd : ∀ A : Cfg, obs (Flip target A) = -obs A)
    (B : Cfg) :
    (∫ A : Cfg,
      obs A * (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) = 0 := by
  let weight : Cfg → ℝ := fun A =>
    E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)
  have hEc (d : Link) :
      Continuous (fun A : Cfg => E ((A d)⁻¹ * B d)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have hweight : Continuous weight := (hEc e).mul (hEc f)
  let g : Cfg → ℝ := fun A => obs A * weight A
  have hg : Continuous g := hobs.mul hweight
  have hoddg (A : Cfg) : g (Flip target A) = -g A := by
    have hwe :
        weight (Flip target A) = weight A :=
      p4Q2PU2_originalTwoCrossingEnergy_unchanged
        H target e f he hf A B
    dsimp [g]
    rw [hodd A, hwe]
    ring
  change (∫ A : Cfg, g A ∂haar) = 0
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H target g hg hoddg

end OriginalTwoCrossingCenterSelection
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PU2_originalCrossingEnergy_unchanged_at_other
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PU2_originalTwoCrossingEnergy_unchanged
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PU2_originalOddPlaquette_twoCrossingHaar_zero
