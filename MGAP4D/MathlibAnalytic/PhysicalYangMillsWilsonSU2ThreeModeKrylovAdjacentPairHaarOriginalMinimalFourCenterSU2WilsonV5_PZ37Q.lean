import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalMinimalFourCenterIncidenceV5_PZ37Q
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonCenterWitnessV5_IY
import Mathlib.Tactic

/-!
# PZ37Q — sixteen actual SU(2) center plaquettes at the minimal period

Transport the kernel-checked *physical* period-two 4-link incidence
certificate into the original SU(2) spatial Wilson action. Map Bool
selected-link parity into the genuine SU(2) center {I,-I}; the center
product and inversion identities show that the unchanged original
oriented plaquette holonomy has exactly that parity.

All 16 affected plaquettes have original Wilson energy 2; the other
8 have energy 0. Thus the true spatial Wilson action is EXACTLY 32,
and the true half-action is 16. No surrogate lattice, Haar integral,
Wilson kernel, fake group representation or native_decide is involved.
-/

namespace MGAP4D.MathlibAnalytic
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

local notation "SU" => SpecialUnitaryMatrixGroup 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink 0
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette 0
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 0 2
local notation "Odd" => p4Q2PZ37Q_originalMinimalPlaquetteOdd

private theorem p4Q2PZ37Q_negativeIdentity_inv :
    specialUnitaryTwoNegativeIdentity⁻¹ = specialUnitaryTwoNegativeIdentity := by
  apply Subtype.ext
  change star (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) =
    -(1 : Matrix (Fin 2) (Fin 2) ℂ)
  simp

private theorem p4Q2PZ37Q_negativeIdentity_sq :
    specialUnitaryTwoNegativeIdentity * specialUnitaryTwoNegativeIdentity =
      (1 : SU) := by
  calc
    specialUnitaryTwoNegativeIdentity * specialUnitaryTwoNegativeIdentity =
        specialUnitaryTwoNegativeIdentity⁻¹ *
          specialUnitaryTwoNegativeIdentity := by
            rw [p4Q2PZ37Q_negativeIdentity_inv]
    _ = 1 := inv_mul_cancel _

/-- Genuine SU(2) center sign, not an auxiliary finite gauge group. -/
def p4Q2PZ37Q_originalSU2CenterSign (b : Bool) : SU :=
  if b then specialUnitaryTwoNegativeIdentity else 1

private theorem p4Q2PZ37Q_centerSign_mul (b c : Bool) :
    p4Q2PZ37Q_originalSU2CenterSign b *
        p4Q2PZ37Q_originalSU2CenterSign c =
      p4Q2PZ37Q_originalSU2CenterSign (Bool.xor b c) := by
  cases b <;> cases c <;>
    simp [p4Q2PZ37Q_originalSU2CenterSign,
      p4Q2PZ37Q_negativeIdentity_sq]

private theorem p4Q2PZ37Q_centerSign_inv (b : Bool) :
    (p4Q2PZ37Q_originalSU2CenterSign b)⁻¹ =
      p4Q2PZ37Q_originalSU2CenterSign b := by
  cases b <;> simp [p4Q2PZ37Q_originalSU2CenterSign,
    p4Q2PZ37Q_negativeIdentity_inv]

/-- Actual SU(2) boundary configuration: four selected genuine physical
spatial positive links are -I, all other original links are I. -/
def p4Q2PZ37Q_originalMinimalFourCenterBoundary : Cfg :=
  fun e => p4Q2PZ37Q_originalSU2CenterSign
    (p4Q2PZ37Q_originalMinimalSelected e)

local notation "B₁₆" => p4Q2PZ37Q_originalMinimalFourCenterBoundary

/-- Exact center parity of the original oriented four-edge plaquette
holonomy, using the original spatial gauge carrier and inversions. -/
theorem p4Q2PZ37Q_originalMinimalPlaquetteHolonomy_center
    (p : Plaq) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B₁₆ p =
      p4Q2PZ37Q_originalSU2CenterSign (Odd p) := by
  change
    p4Q2PZ37Q_originalSU2CenterSign
        (p4Q2PZ37Q_originalMinimalSelected (p4Q2PU3_originalPlaquetteEdge0 0 p)) *
      p4Q2PZ37Q_originalSU2CenterSign
        (p4Q2PZ37Q_originalMinimalSelected (p4Q2PU3_originalPlaquetteEdge1 0 p)) *
      (p4Q2PZ37Q_originalSU2CenterSign
        (p4Q2PZ37Q_originalMinimalSelected (p4Q2PU3_originalPlaquetteEdge2 0 p)))⁻¹ *
      (p4Q2PZ37Q_originalSU2CenterSign
        (p4Q2PZ37Q_originalMinimalSelected (p4Q2PU3_originalPlaquetteEdge3 0 p)))⁻¹ =
          p4Q2PZ37Q_originalSU2CenterSign (Odd p)
  simp only [p4Q2PZ37Q_centerSign_inv, p4Q2PZ37Q_centerSign_mul,
    p4Q2PZ37Q_originalMinimalPlaquetteOdd, Bool.xor_assoc]

/-- Each literal SU(2) spatial plaquette has exactly its
physical Wilson energy 2 for odd center sign and 0 otherwise. -/
theorem p4Q2PZ37Q_originalMinimalPlaquetteWilsonEnergy
    (p : Plaq) :
    specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B₁₆ p) =
      if Odd p = true then (2 : ℝ) else 0 := by
  rw [p4Q2PZ37Q_originalMinimalPlaquetteHolonomy_center]
  cases h : Odd p with
  | false =>
    simpa [h, p4Q2PZ37Q_originalSU2CenterSign] using
      (specialUnitaryWilsonPlaquetteEnergy_one 2 (by decide))
  | true =>
    simpa [h, p4Q2PZ37Q_originalSU2CenterSign] using
      specialUnitaryWilsonPlaquetteEnergy_two_negativeIdentity

/-- The actual ORIGINAL full spatial Wilson energy equals 32: 16
physical SU(2) center plaquettes, each contributing exactly 2. -/
theorem p4Q2PZ37Q_originalMinimalFourCenterBoundary_spatialWilsonAction :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction 0 2 B₁₆ = 32 := by
  classical
  let F : Finset Plaq :=
    Finset.univ.filter (fun p => Odd p = true)
  have hSet :
      F = p4Q2PZ37Q_originalMinimalAffectedPlaquettes := by
    ext p
    simp [F, p4Q2PZ37Q_originalMinimalAffectedPlaquettes]
  have hCount : F.card = 16 := by
    rw [hSet]
    exact p4Q2PZ37Q_originalMinimalAffectedPlaquettes_card
  have hAction :
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction 0 2 B₁₆ =
        ∑ p : Plaq,
          specialUnitaryWilsonPlaquetteEnergy 2
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B₁₆ p) := by
    simp [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction,
      periodicHypercubicEvenSpatialSlicePlaquetteList]
    apply Finset.sum_congr
    · ext p
      simp
    · intro p hp
      rfl
  rw [hAction]
  calc
    (∑ p : Plaq,
       specialUnitaryWilsonPlaquetteEnergy 2
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B₁₆ p)) =
        ∑ p : Plaq, (if Odd p = true then (2 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro p _
          exact p4Q2PZ37Q_originalMinimalPlaquetteWilsonEnergy p
    _ = ∑ p ∈ F, (2 : ℝ) := by
          simp only [F, Finset.sum_filter]
    _ = 32 := by
          norm_num [hCount]

/-- In the exact original one-slab physical boundary weight, the
minimal-period genuine SU(2) center state reaches HALF-action 16. -/
theorem p4Q2PZ37Q_originalMinimalFourCenterBoundary_halfAction :
    p4Q2PS_originalHalfSpatialAction 0 B₁₆ = 16 := by
  change (1 / 2 : ℝ) *
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction 0 2 B₁₆ = 16
  rw [p4Q2PZ37Q_originalMinimalFourCenterBoundary_spatialWilsonAction]
  norm_num

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Q_originalMinimalPlaquetteHolonomy_center
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Q_originalMinimalFourCenterBoundary_spatialWilsonAction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Q_originalMinimalFourCenterBoundary_halfAction
