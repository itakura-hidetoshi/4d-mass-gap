import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPlaquetteCenterTraceV5_PV
import Mathlib.Tactic

/-!
# P4-Q2-PV2 — actual Wilson plaquette character / TWO crossing orthogonality

For every genuine spatial Wilson plaquette p and arbitrary two
temporal-crossing links e,f, PU3 constructs an ACTUAL third link on
p that neither crossing touches. PV proves the full SU(2) Wilson
normalized trace is odd under the center flip at that link. PU/PU2
prove the full original spatial product Haar is measure preserving
and the two crossing factors are unchanged. Hence their exact Haar
integral vanishes, with NO conditional plaquette oddness assumption
left in this theorem.

This is the termwise original spatial-plaquette Haar selection rule.
A separate finite-sum integration step is still needed to conclude
the entire physical P(B) and fourth Wilson coefficient vanish.
No independent posterior, rank, Dobrushin, new axiom, admit or sorry.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PV2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PV2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PV2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PV2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PV2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalPlaquetteTwoCrossingHaarOrthogonality

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H

/-- GENUINE non-conditional SU(2) selection rule at every finite H:
each spatial Wilson plaquette character is orthogonal in original Haar
to an arbitrary ordered pair of temporal Wilson crossing energies,
including the e=f diagonal. The unused link comes from true geometry. -/
theorem p4Q2PV2_originalPlaquette_twoCrossingHaar_zero
    (p : Plaq) (e f : Link) (B : Cfg) :
    (∫ A : Cfg,
      χ p A *
        (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) = 0 := by
  obtain ⟨target, hMember, htE, htF⟩ :=
    p4Q2PU3_originalPlaquette_freeLink_for_twoCrossings H p e f
  exact p4Q2PU2_originalOddPlaquette_twoCrossingHaar_zero
    H target e f htE.symm htF.symm (χ p)
    (p4Q2PV_originalPlaquetteRealCharacter_continuous H p)
    (p4Q2PV_originalPlaquetteRealCharacter_centerOdd H p target hMember) B

end OriginalPlaquetteTwoCrossingHaarOrthogonality
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PV2_originalPlaquette_twoCrossingHaar_zero
