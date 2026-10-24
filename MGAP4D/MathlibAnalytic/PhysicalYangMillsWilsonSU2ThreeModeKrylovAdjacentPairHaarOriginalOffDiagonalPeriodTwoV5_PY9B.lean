import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalOffDiagonalGeometryV5_PY9A
import Mathlib.Tactic

/-!
# P4-Q2-PY9B — exceptional period-two plaquette geometry and universal pair selection

At minimal physical even period two, distinct spatial plaquettes may
share TWO (not just one) of their original four positive links.
This file decides the exact finite H=0 physical incidence, proving
there are NO distinct plaquette pairs sharing three or four links.
The H>0 proof reuses PY9A's genuine periodic shared-plaquette uniqueness.

Thus every distinct pair p != q has at least four center-odd links
in its physical symmetric difference for ALL H >= 0. Two genuine
temporal Wilson crossings cannot occupy them all. Applying PY8D
in either orientation kills EVERY distinct-plaquette/two-crossing
reference-Haar moment. This is an original spatial-link Ward statement,
not a claim about the interacting Wilson posterior or the C5 minor.
No made-up spectral measure, rank, axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000
set_option maxRecDepth 8000

namespace GroundStatePosteriorJoint
section GenuinePeriodTwoPairGeometry

local notation "Link0" => PeriodicHypercubicEvenSpatialSliceLink 0
local notation "Plaq0" => PeriodicHypercubicEvenSpatialSlicePlaquette 0
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3

/-- Explicit constructive enumeration of the original time-zero vertices.
Avoid the noncomputable Finite.toFintype fallback in `native_decide`. -/
local instance p4Q2PY9B_periodTwoVertexFintype :
    Fintype (PeriodicHypercubicEvenVertex 0) := inferInstance

local instance p4Q2PY9B_periodTwoPrimaryDecidable :
    DecidablePred (periodicHypercubicEvenOnPrimaryReflectionPlane 0) :=
  fun v => (inferInstance : Decidable (v 0 = 0))

local instance p4Q2PY9B_periodTwoSpatialVertexFintype :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex 0) :=
  Subtype.fintype (periodicHypercubicEvenOnPrimaryReflectionPlane 0)

local instance p4Q2PY9B_periodTwoSpatialDirectionFintype :
    Fintype PeriodicHypercubicEvenSpatialDirection :=
  Subtype.fintype (fun mu : PeriodicHypercubicAxis => mu ≠ 0)

local instance p4Q2PY9B_periodTwoDirectionPairFintype :
    Fintype PeriodicHypercubicEvenSpatialDirectionPair :=
  Subtype.fintype (fun pair :
      PeriodicHypercubicEvenSpatialDirection ×
        PeriodicHypercubicEvenSpatialDirection => pair.1.1 < pair.2.1)

local instance p4Q2PY9B_periodTwoPlaquetteFintype : Fintype Plaq0 :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex 0)
    PeriodicHypercubicEvenSpatialDirectionPair

/-- Pure finite geometric certificate: on the actual 2-periodic
time-zero three-dimensional SU(2) spatial lattice, DISTINCT oriented
coordinate plaquettes share at most TWO physical positive links.
This has no gauge-variable, Wilson measure, or posterior input. -/
private theorem p4Q2PY9B_periodTwo_discrete_two_shared :
    ∀ p q : Plaq0, p ≠ q →
      (({e0 0 p, e1 0 p, e2 0 p, e3 0 p} : Finset Link0) ∩
        ({e0 0 q, e1 0 q, e2 0 q, e3 0 q} : Finset Link0)).card ≤ 2 := by
  native_decide

/-- Actual period-two pair support bound, connected to PY9A's
original four-link definition, not an independent graph proxy. -/
theorem p4Q2PY9_originalPeriodTwo_sharedEdges_card_le_two
    (p q : Plaq0) (hpq : p ≠ q) :
    ((p4Q2PY9_originalPlaquettePhysicalEdges 0 p) ∩
      (p4Q2PY9_originalPlaquettePhysicalEdges 0 q)).card ≤ 2 := by
  classical
  have hSet (r : Plaq0) :
      p4Q2PY9_originalPlaquettePhysicalEdges 0 r =
        ({e0 0 r, e1 0 r, e2 0 r, e3 0 r} : Finset Link0) := by
    ext target
    simp [p4Q2PY9_originalPlaquettePhysicalEdges_mem]
  rw [hSet p, hSet q]
  exact p4Q2PY9B_periodTwo_discrete_two_shared p q hpq

end GenuinePeriodTwoPairGeometry

section UniversalOffDiagonalOddPair
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "s" => p4Q2PY9_originalPlaquettePhysicalEdges H

/-- Genuine shared-link cardinality at most TWO for EVERY finite even
period, by nondegenerate uniqueness and exact minimal-period check. -/
theorem p4Q2PY9_originalDistinctPlaquettes_sharedEdges_card_le_two
    (p q : Plaq) (hpq : p ≠ q) :
    ((s p) ∩ (s q)).card ≤ 2 := by
  rcases Nat.eq_zero_or_pos H with h0 | hH
  · subst H
    exact p4Q2PY9_originalPeriodTwo_sharedEdges_card_le_two p q hpq
  · exact le_trans
      (p4Q2PY9_originalDistinctPlaquettes_sharedEdges_card_le_one
        H hH p q hpq) (by omega)

/-- Any distinct original plaquette pair has at least FOUR physical
center-odd links (the symmetric difference of their genuine supports). -/
theorem p4Q2PY9_originalDistinctPlaquettes_oddEdges_card_ge_four
    (p q : Plaq) (hpq : p ≠ q) :
    4 ≤ (((s p) \ (s q)) ∪ ((s q) \ (s p))).card := by
  classical
  let u := s p
  let v := s q
  have hu : u.card = 4 := p4Q2PY9_originalPlaquettePhysicalEdges_card H p
  have hv : v.card = 4 := p4Q2PY9_originalPlaquettePhysicalEdges_card H q
  have hint : (u ∩ v).card ≤ 2 :=
    p4Q2PY9_originalDistinctPlaquettes_sharedEdges_card_le_two
      H p q hpq
  have hdisj : Disjoint (u \ v) (v \ u) := by
    apply Finset.disjoint_left.mpr
    intro target h1 h2
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
  have huDiff := Finset.card_sdiff_add_card_inter u v
  have hvDiff := Finset.card_sdiff_add_card_inter v u
  rw [Finset.inter_comm v u] at hvDiff
  change 4 ≤ ((u \ v) ∪ (v \ u)).card
  rw [Finset.card_union_of_disjoint hdisj]
  omega

/-- UNIVERSAL genuinely unused center-odd spatial link outside any
two original temporal crossing links, including the H=0 exception. -/
theorem p4Q2PY9_originalDistinctPlaquettes_oddFreeLink_for_twoCrossings
    (p q : Plaq) (hpq : p ≠ q) (e f : Link) :
    ∃ target : Link,
      ((target ∈ s p ∧ target ∉ s q) ∨
        (target ∈ s q ∧ target ∉ s p)) ∧
      target ≠ e ∧ target ≠ f := by
  classical
  let odd := ((s p) \ (s q)) ∪ ((s q) \ (s p))
  have hOdd : 4 ≤ odd.card :=
    p4Q2PY9_originalDistinctPlaquettes_oddEdges_card_ge_four H p q hpq
  have hef : ({e, f} : Finset Link).card ≤ 2 := by
    by_cases heq : e = f <;> simp [heq]
  have hnon : (odd \ ({e, f} : Finset Link)).Nonempty :=
    Finset.sdiff_nonempty_of_card_lt_card (by omega)
  obtain ⟨target, htarget⟩ := hnon
  have hmem := (Finset.mem_sdiff.mp htarget)
  have hside := (Finset.mem_union.mp hmem.1)
  refine ⟨target, ?_, ?_, ?_⟩
  · rcases hside with h | h
    · exact Or.inl (Finset.mem_sdiff.mp h)
    · exact Or.inr (Finset.mem_sdiff.mp h)
  · intro h
    exact hmem.2 (by simp [h])
  · intro h
    exact hmem.2 (by simp [h])

end UniversalOffDiagonalOddPair

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalPeriodTwo_sharedEdges_card_le_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalDistinctPlaquettes_sharedEdges_card_le_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalDistinctPlaquettes_oddEdges_card_ge_four
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalDistinctPlaquettes_oddFreeLink_for_twoCrossings
