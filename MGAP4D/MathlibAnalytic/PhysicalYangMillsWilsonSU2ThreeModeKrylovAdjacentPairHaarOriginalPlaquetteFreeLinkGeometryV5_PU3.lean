import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCenterFlipTwoCrossingV5_PU2
import Mathlib.Tactic

/-!
# P4-Q2-PU3 — every original spatial Wilson plaquette has a free link

At every finite even-periodic spatial SU(2) volume, the four actual
oriented spatial links of a spatial Wilson plaquette are distinct.
In particular, THREE of these links are pairwise distinct and so
cannot all belong to an arbitrary pair of temporal-crossing links.
This gives a genuine plaquette link untouched by any two-crossing
insertion, without postulating it, even at minimal even period two.

This is purely original finite-lattice geometry, not a nonzero
coefficient, extra rank axiom or synthetic spectral measure.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint
section OriginalSpatialPlaquetteFreeLink

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H

/-- First forward oriented spatial link. -/
def p4Q2PU3_originalPlaquetteEdge0 (p : Plaq) : Link :=
  (p.1, p.2.1.1)

/-- Second forward oriented spatial link. -/
def p4Q2PU3_originalPlaquetteEdge1 (p : Plaq) : Link :=
  (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1, p.2.1.2)

/-- Third (inverse-oriented) spatial link. -/
def p4Q2PU3_originalPlaquetteEdge2 (p : Plaq) : Link :=
  (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2, p.2.1.1)

/-- Fourth (inverse-oriented) spatial link. -/
def p4Q2PU3_originalPlaquetteEdge3 (p : Plaq) : Link :=
  (p.1, p.2.1.2)

local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H

/-- The original first THREE spatial plaquette links are pairwise
distinct on every even period, including the period-two torus. -/
theorem p4Q2PU3_originalPlaquette_firstThree_distinct (p : Plaq) :
    e0 p ≠ e1 p ∧ e0 p ≠ e2 p ∧ e1 p ≠ e2 p := by
  have hmu : p.2.1.1 ≠ p.2.1.2 := by
    intro heq
    exact (ne_of_lt p.2.2) (congrArg Subtype.val heq)
  have hnu :
      periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2 ≠ p.1 :=
    p4Q2PL_originalSpatialLink_target_ne_source H (p.1, p.2.1.2)
  constructor
  · intro heq
    exact hmu (congrArg Prod.snd heq)
  constructor
  · intro heq
    exact hnu (congrArg Prod.fst heq).symm
  · intro heq
    exact hmu.symm (congrArg Prod.snd heq)

/-- The fourth physical spatial plaquette link is distinct from
all first three links, using the original even-period shift geometry. -/
theorem p4Q2PU3_originalPlaquette_last_distinct (p : Plaq) :
    e3 p ≠ e0 p ∧ e3 p ≠ e1 p ∧ e3 p ≠ e2 p := by
  have hmu : p.2.1.1 ≠ p.2.1.2 := by
    intro heq
    exact (ne_of_lt p.2.2) (congrArg Subtype.val heq)
  have hshift :
      periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1 ≠ p.1 :=
    p4Q2PL_originalSpatialLink_target_ne_source H (p.1, p.2.1.1)
  constructor
  · intro heq
    exact hmu.symm (congrArg Prod.snd heq)
  constructor
  · intro heq
    exact hshift (congrArg Prod.fst heq).symm
  · intro heq
    exact hmu.symm (congrArg Prod.snd heq)

/-- Pigeonhole for the ACTUAL Wilson plaquette: among the first
three pairwise-distinct spatial links, at least one is different
from ANY chosen two crossing links e and f. -/
theorem p4Q2PU3_originalPlaquette_freeLink_for_twoCrossings
    (p : Plaq) (e f : Link) :
    ∃ target : Link,
      (target = e0 p ∨ target = e1 p ∨ target = e2 p) ∧
      target ≠ e ∧ target ≠ f := by
  obtain ⟨h01, h02, h12⟩ :=
    p4Q2PU3_originalPlaquette_firstThree_distinct H p
  by_contra hNo
  have hAll (target : Link)
      (hmember : target = e0 p ∨ target = e1 p ∨ target = e2 p) :
      target = e ∨ target = f := by
    by_contra hbad
    have he : target ≠ e := by
      intro ht
      exact hbad (Or.inl ht)
    have hf : target ≠ f := by
      intro ht
      exact hbad (Or.inr ht)
    exact hNo ⟨target, hmember, he, hf⟩
  have h0 : e0 p = e ∨ e0 p = f :=
    hAll (e0 p) (Or.inl rfl)
  have h1 : e1 p = e ∨ e1 p = f :=
    hAll (e1 p) (Or.inr (Or.inl rfl))
  have h2 : e2 p = e ∨ e2 p = f :=
    hAll (e2 p) (Or.inr (Or.inr rfl))
  rcases h0 with h0 | h0 <;>
    rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;>
    simp_all

end OriginalSpatialPlaquetteFreeLink
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PU3_originalPlaquette_firstThree_distinct
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PU3_originalPlaquette_last_distinct
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PU3_originalPlaquette_freeLink_for_twoCrossings
