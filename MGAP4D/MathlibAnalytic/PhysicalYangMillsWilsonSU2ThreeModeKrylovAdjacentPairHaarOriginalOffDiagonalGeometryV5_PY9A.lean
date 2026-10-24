import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalOffDiagonalFreeEdgeWardV5_PY8D
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSharedPlaquetteUniqueness
import Mathlib.Tactic

/-!
# P4-Q2-PY9A — actual spatial plaquette support and nondegenerate pair geometry

The original SU(2) spatial four-edge boundary defines a finite link support.
For even side length at least four, two DISTINCT physical coordinate plaquettes
cannot share two distinct spatial links: the existing actual finite periodic
shared-plaquette uniqueness theorem proves this, without surrogate geometry.

Consequently each of the four genuine p edges has at least THREE p-only
representatives. One of these avoids ANY two temporal crossing links.
The period-two geometry is deliberately NOT assumed to obey the same
one-shared-edge bound. No change to the Wilson action, Haar reference,
Gauss-law Hilbert space or interacting posterior; no new axioms/sorry/admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint
section OriginalOffDiagonalPairGeometry

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H

/-- The exact four unoriented PHYSICAL positive links in the original
oriented spatial plaquette holonomy. -/
noncomputable def p4Q2PY9_originalPlaquettePhysicalEdges (p : Plaq) :
    Finset Link := by
  classical
  exact {e0 p, e1 p, e2 p, e3 p}

@[simp] theorem p4Q2PY9_originalPlaquettePhysicalEdges_mem
    (p : Plaq) (target : Link) :
    target ∈ p4Q2PY9_originalPlaquettePhysicalEdges H p ↔
      target = e0 p ∨ target = e1 p ∨
      target = e2 p ∨ target = e3 p := by
  classical
  simp [p4Q2PY9_originalPlaquettePhysicalEdges]

/-- All FOUR original spatial Wilson plaquette physical links are distinct,
including at the shortest even period. -/
theorem p4Q2PY9_originalPlaquettePhysicalEdges_card (p : Plaq) :
    (p4Q2PY9_originalPlaquettePhysicalEdges H p).card = 4 := by
  classical
  obtain ⟨h01, h02, h12⟩ :=
    p4Q2PU3_originalPlaquette_firstThree_distinct H p
  obtain ⟨h30, h31, h32⟩ :=
    p4Q2PU3_originalPlaquette_last_distinct H p
  simp [p4Q2PY9_originalPlaquettePhysicalEdges,
    h01, h02, h12, h30, h31, h32,
    Ne.symm h01, Ne.symm h02, Ne.symm h12,
    Ne.symm h30, Ne.symm h31, Ne.symm h32]

/-- Every member of the original four-link support is a genuinely
incident physical link in the FOUR-DIMENSIONAL coordinate plaquette. -/
theorem p4Q2PY9_originalPlaquettePhysicalEdges_touches
    (p : Plaq) (target : Link)
    (hmem : target ∈ p4Q2PY9_originalPlaquettePhysicalEdges H p) :
    periodicHypercubicPlaquetteTouchesEdge
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) := by
  rcases (p4Q2PY9_originalPlaquettePhysicalEdges_mem H p target).mp hmem with
    h0 | h1 | h2 | h3
  · subst target
    exact ⟨0, rfl⟩
  · subst target
    exact ⟨1, rfl⟩
  · subst target
    exact ⟨2, rfl⟩
  · subst target
    exact ⟨3, rfl⟩

/-- In side length >=4, two distinct ACTUAL spatial plaquettes share
at most one genuine physical link (not one abstract graph edge). -/
theorem p4Q2PY9_originalDistinctPlaquettes_sharedEdges_card_le_one
    (hH : 0 < H) (p q : Plaq) (hpq : p ≠ q) :
    ((p4Q2PY9_originalPlaquettePhysicalEdges H p) ∩
      (p4Q2PY9_originalPlaquettePhysicalEdges H q)).card ≤ 1 := by
  classical
  have hn : 3 ≤ PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    omega⟩
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hne
  have hPhysNe :
      periodicHypercubicEvenSpatialSliceLinkEmbedding H f ≠
        periodicHypercubicEvenSpatialSliceLinkEmbedding H e := by
    intro hEq
    exact hne
      ((periodicHypercubicEvenSpatialSliceLinkEmbedding_injective H hEq).symm)
  have hpE := p4Q2PY9_originalPlaquettePhysicalEdges_touches
    H p e (Finset.mem_inter.mp he).1
  have hpF := p4Q2PY9_originalPlaquettePhysicalEdges_touches
    H p f (Finset.mem_inter.mp hf).1
  have hqE := p4Q2PY9_originalPlaquettePhysicalEdges_touches
    H q e (Finset.mem_inter.mp he).2
  have hqF := p4Q2PY9_originalPlaquettePhysicalEdges_touches
    H q f (Finset.mem_inter.mp hf).2
  have hEqualEmbeddings :=
    periodicHypercubicPlaquette_eq_of_touches_two_edges
      (PeriodicHypercubicEvenSideLength H) hn
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H e)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H f)
      hPhysNe
      (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p)
      (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H q)
      hpE hpF hqE hqF
  exact hpq (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_injective
    H hEqualEmbeddings)

/-- Given two physical crossing links, a p-only link always remains
for distinct p,q at even side >=4. -/
theorem p4Q2PY9_originalDistinctPlaquettes_freeLink_for_twoCrossings
    (hH : 0 < H) (p q : Plaq) (hpq : p ≠ q) (e f : Link) :
    ∃ target : Link,
      target ∈ p4Q2PY9_originalPlaquettePhysicalEdges H p ∧
      target ∉ p4Q2PY9_originalPlaquettePhysicalEdges H q ∧
      target ≠ e ∧ target ≠ f := by
  classical
  let s := p4Q2PY9_originalPlaquettePhysicalEdges H p
  let t := p4Q2PY9_originalPlaquettePhysicalEdges H q
  have hs : s.card = 4 :=
    p4Q2PY9_originalPlaquettePhysicalEdges_card H p
  have hinter : (s ∩ t).card ≤ 1 :=
    p4Q2PY9_originalDistinctPlaquettes_sharedEdges_card_le_one
      H hH p q hpq
  have hCard : 3 ≤ (s \ t).card := by
    have hsum := Finset.card_sdiff_add_card_inter s t
    omega
  have hef : ({e, f} : Finset Link).card ≤ 2 := by
    by_cases heq : e = f <;> simp [heq]
  have hNonempty : ((s \ t) \ ({e, f} : Finset Link)).Nonempty :=
    Finset.sdiff_nonempty_of_card_lt_card (by omega)
  obtain ⟨target, htarget⟩ := hNonempty
  have ht := (Finset.mem_sdiff.mp htarget)
  have hst := (Finset.mem_sdiff.mp ht.1)
  refine ⟨target, hst.1, hst.2, ?_, ?_⟩
  · intro h
    exact ht.2 (by simp [h])
  · intro h
    exact ht.2 (by simp [h])

end OriginalOffDiagonalPairGeometry
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalPlaquettePhysicalEdges_card
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalPlaquettePhysicalEdges_touches
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalDistinctPlaquettes_sharedEdges_card_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalDistinctPlaquettes_freeLink_for_twoCrossings
