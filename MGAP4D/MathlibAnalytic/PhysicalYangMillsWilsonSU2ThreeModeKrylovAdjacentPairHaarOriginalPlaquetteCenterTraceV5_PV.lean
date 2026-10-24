import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPlaquetteFreeLinkGeometryV5_PU3
import Mathlib.Tactic

/-!
# P4-Q2-PV — true spatial SU(2) Wilson plaquette character is center-odd

The original spatial plaquette holonomy is the ordered FOUR-link
SU(2) group word u0*u1*u2^{-1}*u3^{-1}. The true rank-two central
negative identity z=-I commutes with every SU(2) element and z^{-1}=z.

At every one of the first THREE genuine spatial plaquette links,
the original one-link center flip changes the full plaquette holonomy
to holonomy*z, including correct inverse orientation of the third link.
The true Wilson normalized real trace chi=1-E(Hol) thus changes sign.

All four spatial links are proved distinct by PU3, even at period two.
No artificial link independence, physical posterior change, rank
hypothesis, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PV_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PV_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PV_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PV_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PV_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "z" => specialUnitaryTwoNegativeIdentity

/-- The original physical SU(2) center element is central as a
matrix fact, not an assumed group-theoretic symmetry. -/
theorem p4Q2PV_originalSU2Center_commutes (u : G) :
    z * u = u * z := by
  apply Subtype.ext
  change (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      (u : Matrix (Fin 2) (Fin 2) ℂ) =
    (u : Matrix (Fin 2) (Fin 2) ℂ) *
      (-(1 : Matrix (Fin 2) (Fin 2) ℂ))
  simp

/-- The same physical rank-two central element has order two. -/
theorem p4Q2PV_originalSU2Center_inverse :
    z⁻¹ = z := by
  apply Subtype.ext
  change star (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) =
    -(1 : Matrix (Fin 2) (Fin 2) ℂ)
  simp

/-- Move the central -I through any subsequent SU(2) factor. -/
theorem p4Q2PV_originalSU2Center_move_right (u v : G) :
    (u * z) * v = (u * v) * z := by
  calc
    (u * z) * v = u * (z * v) := mul_assoc _ _ _
    _ = u * (v * z) := by rw [p4Q2PV_originalSU2Center_commutes v]
    _ = (u * v) * z := (mul_assoc _ _ _).symm

/-- Inverse-oriented links also insert exactly one central -I. -/
theorem p4Q2PV_originalSU2Center_inverse_mul (u : G) :
    (u * z)⁻¹ = u⁻¹ * z := by
  rw [mul_inv_rev, p4Q2PV_originalSU2Center_inverse,
    p4Q2PV_originalSU2Center_commutes (u⁻¹)]

section ActualSpatialPlaquetteCharacter
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Hol" =>
  periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H

/-- The actual spatial Wilson plaquette's normalized real trace.
This is exactly 1 minus its original Wilson plaquette energy. -/
noncomputable def p4Q2PV_originalPlaquetteRealCharacter
    (p : Plaq) (A : Cfg) : ℝ :=
  1 - E (Hol A p)

local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H

theorem p4Q2PV_originalPlaquetteRealCharacter_continuous
    (p : Plaq) :
    Continuous (fun A : Cfg => χ p A) := by
  have hHol : Continuous (fun A : Cfg => Hol A p) := by
    unfold periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
    fun_prop
  exact continuous_const.sub
    ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp hHol)

/-- Center flipping any of the first THREE actual plaquette edges
multiplies the complete oriented four-edge holonomy on the RIGHT by -I.
In particular the inverse-oriented third edge is treated correctly. -/
theorem p4Q2PV_originalPlaquetteHolonomy_flip_firstThree
    (p : Plaq) (A : Cfg) (target : Link)
    (hMember : target = e0 p ∨ target = e1 p ∨ target = e2 p) :
    Hol (Flip target A) p = Hol A p * z := by
  obtain ⟨h01, h02, h12⟩ :=
    p4Q2PU3_originalPlaquette_firstThree_distinct H p
  obtain ⟨h30, h31, h32⟩ :=
    p4Q2PU3_originalPlaquette_last_distinct H p
  rcases hMember with h0 | h1 | h2
  · subst target
    change
      (Flip (e0 p) A (e0 p)) *
        (Flip (e0 p) A (e1 p)) *
        (Flip (e0 p) A (e2 p))⁻¹ *
        (Flip (e0 p) A (e3 p))⁻¹ =
      (A (e0 p) * A (e1 p) * (A (e2 p))⁻¹ * (A (e3 p))⁻¹) * z
    rw [p4Q2PU_originalSingleLinkCenterFlip_at H (e0 p) A,
      p4Q2PU_originalSingleLinkCenterFlip_other H (e0 p) (e1 p) h01.symm A,
      p4Q2PU_originalSingleLinkCenterFlip_other H (e0 p) (e2 p) h02.symm A,
      p4Q2PU_originalSingleLinkCenterFlip_other H (e0 p) (e3 p) h30 A]
    rw [p4Q2PV_originalSU2Center_move_right
      (A (e0 p)) (A (e1 p))]
    rw [p4Q2PV_originalSU2Center_move_right
      (A (e0 p) * A (e1 p)) ((A (e2 p))⁻¹)]
    rw [p4Q2PV_originalSU2Center_move_right
      (A (e0 p) * A (e1 p) * (A (e2 p))⁻¹) ((A (e3 p))⁻¹)]
  · subst target
    change
      (Flip (e1 p) A (e0 p)) *
        (Flip (e1 p) A (e1 p)) *
        (Flip (e1 p) A (e2 p))⁻¹ *
        (Flip (e1 p) A (e3 p))⁻¹ =
      (A (e0 p) * A (e1 p) * (A (e2 p))⁻¹ * (A (e3 p))⁻¹) * z
    rw [p4Q2PU_originalSingleLinkCenterFlip_other H (e1 p) (e0 p) h01 A,
      p4Q2PU_originalSingleLinkCenterFlip_at H (e1 p) A,
      p4Q2PU_originalSingleLinkCenterFlip_other H (e1 p) (e2 p) h12.symm A,
      p4Q2PU_originalSingleLinkCenterFlip_other H (e1 p) (e3 p) h31 A]
    rw [← mul_assoc (A (e0 p)) (A (e1 p)) z]
    rw [p4Q2PV_originalSU2Center_move_right
      (A (e0 p) * A (e1 p)) ((A (e2 p))⁻¹)]
    rw [p4Q2PV_originalSU2Center_move_right
      (A (e0 p) * A (e1 p) * (A (e2 p))⁻¹) ((A (e3 p))⁻¹)]
  · subst target
    change
      (Flip (e2 p) A (e0 p)) *
        (Flip (e2 p) A (e1 p)) *
        (Flip (e2 p) A (e2 p))⁻¹ *
        (Flip (e2 p) A (e3 p))⁻¹ =
      (A (e0 p) * A (e1 p) * (A (e2 p))⁻¹ * (A (e3 p))⁻¹) * z
    rw [p4Q2PU_originalSingleLinkCenterFlip_other H (e2 p) (e0 p) h02 A,
      p4Q2PU_originalSingleLinkCenterFlip_other H (e2 p) (e1 p) h12 A,
      p4Q2PU_originalSingleLinkCenterFlip_at H (e2 p) A,
      p4Q2PU_originalSingleLinkCenterFlip_other H (e2 p) (e3 p) h32 A]
    rw [p4Q2PV_originalSU2Center_inverse_mul (A (e2 p))]
    rw [← mul_assoc (A (e0 p) * A (e1 p)) ((A (e2 p))⁻¹) z]
    rw [p4Q2PV_originalSU2Center_move_right
      (A (e0 p) * A (e1 p) * (A (e2 p))⁻¹) ((A (e3 p))⁻¹)]

/-- True original plaquette real character is center-odd at ANY
free spatial edge among the three physically distinct candidates. -/
theorem p4Q2PV_originalPlaquetteRealCharacter_centerOdd
    (p : Plaq) (target : Link)
    (hMember : target = e0 p ∨ target = e1 p ∨ target = e2 p)
    (A : Cfg) :
    χ p (Flip target A) = -χ p A := by
  unfold p4Q2PV_originalPlaquetteRealCharacter
  rw [p4Q2PV_originalPlaquetteHolonomy_flip_firstThree H p A target hMember,
    specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity]
  ring

end ActualSpatialPlaquetteCharacter
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PV_originalSU2Center_commutes
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PV_originalSU2Center_inverse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PV_originalSU2Center_move_right
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PV_originalSU2Center_inverse_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteHolonomy_flip_firstThree
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_centerOdd
