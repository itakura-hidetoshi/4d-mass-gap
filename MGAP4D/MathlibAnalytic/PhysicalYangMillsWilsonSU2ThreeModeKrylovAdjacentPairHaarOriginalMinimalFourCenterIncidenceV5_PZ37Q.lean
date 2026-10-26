import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalMinimalBoundaryLoopBudgetV5_PZ37P
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPlaquetteFreeLinkGeometryV5_PU3
import Mathlib.Tactic

/-!
# PZ37Q — actual period-two spatial four-link incidence certificate

On the original H=0 spatial slice, select four genuine physical positive
links, two in direction 1 and two in direction 2. Their four-plaquette
incidence supports are mutually disjoint and hence exactly 16 of the original
24 spatial plaquettes have odd selected-link incidence.

This is a kernel-checked FINITE GEOMETRIC computation on the original
periodic physical vertices and oriented spatial plaquettes. No native_decide
or invented plaquette set, auxiliary Wilson/Haar law, or new axiom.
The next file transports this geometry to genuine SU(2) center holonomies.
-/

namespace MGAP4D.MathlibAnalytic
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 29000000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37Q_fullVertexDecidableEq :
    DecidableEq (PeriodicHypercubicEvenVertex 0) := Fintype.decidablePiFintype
local instance p4Q2PZ37Q_spatialVertexDecidableEq :
    DecidableEq (PeriodicHypercubicEvenSpatialSliceVertex 0) := Subtype.instDecidableEq
local instance p4Q2PZ37Q_directionDecidableEq :
    DecidableEq PeriodicHypercubicEvenSpatialDirection := Subtype.instDecidableEq
local instance p4Q2PZ37Q_planeDecidableEq :
    DecidableEq PeriodicHypercubicEvenSpatialDirectionPair := Subtype.instDecidableEq
local instance p4Q2PZ37Q_linkDecidableEq :
    DecidableEq (PeriodicHypercubicEvenSpatialSliceLink 0) := instDecidableEqProd
local instance p4Q2PZ37Q_plaqDecidableEq :
    DecidableEq (PeriodicHypercubicEvenSpatialSlicePlaquette 0) := instDecidableEqProd
local instance p4Q2PZ37Q_primaryPlaneDecidable :
    DecidablePred (periodicHypercubicEvenOnPrimaryReflectionPlane 0) :=
  fun v => inferInstanceAs (Decidable (v 0 = 0))
local instance p4Q2PZ37Q_vertexFintype :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex 0) :=
  Fintype.subtype
    (Finset.univ.filter (periodicHypercubicEvenOnPrimaryReflectionPlane 0))
    (by intro v; simp)
local instance p4Q2PZ37Q_directionFintype :
    Fintype PeriodicHypercubicEvenSpatialDirection :=
  Fintype.subtype
    ((Finset.univ : Finset PeriodicHypercubicAxis).filter (fun mu => mu ≠ 0))
    (by intro mu; simp)
local instance p4Q2PZ37Q_planeFintype :
    Fintype PeriodicHypercubicEvenSpatialDirectionPair :=
  Fintype.subtype
    ((Finset.univ : Finset (PeriodicHypercubicEvenSpatialDirection ×
      PeriodicHypercubicEvenSpatialDirection)).filter (fun d => d.1.1 < d.2.1))
    (by intro d; simp)
local instance p4Q2PZ37Q_linkFintype :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink 0) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex 0)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ37Q_plaqFintype :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette 0) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex 0)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint

local notation "Vtx" => PeriodicHypercubicEvenSpatialSliceVertex 0
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink 0
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette 0

/-- Actual spatial time-zero vertex: physical axes 1,2,3 receive x,y,z. -/
def p4Q2PZ37Q_minimalSpatialVertex (x y z : ZMod 2) : Vtx :=
  ⟨fun i : Fin 4 =>
      if i = 0 then 0 else if i = 1 then x else if i = 2 then y else z,
    by simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩

/-- Four actual positive spatial links. Their supports share no plaquette. -/
def p4Q2PZ37Q_originalMinimalFourCenterLinks : Finset Link :=
  { (p4Q2PZ37Q_minimalSpatialVertex 0 0 0, ⟨1, by decide⟩),
    (p4Q2PZ37Q_minimalSpatialVertex 0 0 1, ⟨2, by decide⟩),
    (p4Q2PZ37Q_minimalSpatialVertex 0 1 1, ⟨2, by decide⟩),
    (p4Q2PZ37Q_minimalSpatialVertex 1 0 0, ⟨1, by decide⟩) }

/-- Exactly four DISTINCT physical positive spatial links are selected. -/
theorem p4Q2PZ37Q_originalMinimalFourCenterLinks_card :
    p4Q2PZ37Q_originalMinimalFourCenterLinks.card = 4 := by
  decide

/-- Boolean center-sign selector, using ONLY actual original links. -/
def p4Q2PZ37Q_originalMinimalSelected (e : Link) : Bool :=
  decide (e ∈ p4Q2PZ37Q_originalMinimalFourCenterLinks)

/-- The parity of selected incidence along the four oriented links
of an original physical spatial plaquette. Inverse orientation leaves
center parity unchanged, as will be proved in the SU(2) transport. -/
def p4Q2PZ37Q_originalMinimalPlaquetteOdd (p : Plaq) : Bool :=
  Bool.xor
    (Bool.xor
      (p4Q2PZ37Q_originalMinimalSelected (p4Q2PU3_originalPlaquetteEdge0 0 p))
      (p4Q2PZ37Q_originalMinimalSelected (p4Q2PU3_originalPlaquetteEdge1 0 p)))
    (Bool.xor
      (p4Q2PZ37Q_originalMinimalSelected (p4Q2PU3_originalPlaquetteEdge2 0 p))
      (p4Q2PZ37Q_originalMinimalSelected (p4Q2PU3_originalPlaquetteEdge3 0 p)))

/-- Original plaquettes with a single selected edge, obtained by the
kernel-checked original four-positive-link support of PZ28. -/
def p4Q2PZ37Q_originalMinimalAffectedPlaquettes : Finset Plaq :=
  Finset.univ.filter (fun p => p4Q2PZ37Q_originalMinimalPlaquetteOdd p = true)

/-- The four selected physical links have pairwise disjoint
plaquette-incidence supports: no physical plaquette contains two of them. -/
theorem p4Q2PZ37Q_originalMinimalSelectedPlaquette_count_le_one :
    ∀ p : Plaq,
      ((p4Q2PZ28_originalFourEdges 0 p) ∩
        p4Q2PZ37Q_originalMinimalFourCenterLinks).card ≤ 1 := by
  decide

/-- Exactly SIXTEEN true physical spatial plaquettes carry odd
center holonomy on the original H=0 period-two slice. -/
theorem p4Q2PZ37Q_originalMinimalAffectedPlaquettes_card :
    p4Q2PZ37Q_originalMinimalAffectedPlaquettes.card = 16 := by
  decide

end GroundStatePosteriorJoint
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Q_originalMinimalFourCenterLinks_card
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Q_originalMinimalSelectedPlaquette_count_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Q_originalMinimalAffectedPlaquettes_card
