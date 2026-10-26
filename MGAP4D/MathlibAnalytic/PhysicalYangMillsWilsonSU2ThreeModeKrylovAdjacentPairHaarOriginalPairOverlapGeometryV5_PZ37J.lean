import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPairFourthParityV5_PZ37I
import Mathlib.Tactic

/-!
# PZ37J — original pair/four-crossing Haar: geometric off-diagonal elimination

The actual four-edge supports obey |Odd(p,q)| + 2|E(p) intersect E(q)| = 8.
Four temporal insertions cover at most four distinct links, even with repeats.
Consequently an original pair Haar term vanishes if the spatial pair shares
at most one edge. PZ30 already proves this geometric premise for every
DISTINCT pair at H >= 1, so every nonminimal off-diagonal Pair4 is zero.

Keep the diagonal response and all genuine two-or-more-edge overlaps at H=0.
The exact original K4 and physical seventh jet are decomposed into these
remaining sectors. A diagonal Haar value is NOT declared constant or zero.
No surviving H=0 amplitude, O(beta^8) remainder, rank or mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37J_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37J_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalPairOverlap
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Four" => p4Q2PZ28_originalFourEdges H
local notation "On" => p4Q2PZ27_originalEdgeOnPlaquette H
local notation "Odd" => p4Q2PZ37I_originalPairOddEdge H
local notation "Covers" => p4Q2PZ37I_originalQuadCoversOddPair H
local notation "Term4" => p4Q2PZ37I_originalPairFourthTerm H
local notation "Pair4" => p4Q2PZ37I_originalPairTraceFourth H
local notation "K4" => p4Q2PZ37I_originalQuadraticTraceFourth H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "W" => p4Q2PZ37B_originalBoundaryWedge H

/-- Finite symmetric difference of the two ORIGINAL four-edge supports. -/
noncomputable def p4Q2PZ37J_originalPairOddEdges (p q : Plaq) : Finset Link := by
  classical
  exact (Four p \ Four q) ∪ (Four q \ Four p)
local notation "OddSet" => p4Q2PZ37J_originalPairOddEdges H

/-- Membership is exactly the physical centre parity used in PZ37I. -/
theorem p4Q2PZ37J_originalPairOddEdges_mem
    (p q : Plaq) (e : Link) : e ∈ OddSet p q ↔ Odd p q e := by
  classical
  have hOn (r : Plaq) : e ∈ Four r ↔ On r e := by
    simp [p4Q2PZ28_originalFourEdges, p4Q2PZ27_originalEdgeOnPlaquette]
  simp only [p4Q2PZ37J_originalPairOddEdges, Finset.mem_union,
    Finset.mem_sdiff, hOn, p4Q2PZ37I_originalPairOddEdge]
  tauto

/-- Exact finite support identity, valid also for coincident plaquettes
and all period-two geometric overlaps. -/
theorem p4Q2PZ37J_originalPairOddEdges_card_balance
    (p q : Plaq) :
    (OddSet p q).card + 2*(Four p ∩ Four q).card = 8 := by
  classical
  have hDisj : Disjoint (Four p \ Four q) (Four q \ Four p) := by
    apply Finset.disjoint_left.mpr
    intro e hp hq
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mp hq).1
  have hOdd : (OddSet p q).card =
      (Four p \ Four q).card + (Four q \ Four p).card :=
    Finset.card_union_of_disjoint hDisj
  have hp := Finset.card_sdiff_add_card_inter (Four p) (Four q)
  have hq := Finset.card_sdiff_add_card_inter (Four q) (Four p)
  rw [Finset.inter_comm (Four q) (Four p)] at hq
  rw [p4Q2PZ28_originalFourEdges_card H p] at hp
  rw [p4Q2PZ28_originalFourEdges_card H q] at hq
  omega

/-- Four ORIGINAL temporal insertions can cover at most four different
odd-incidence links; repeated crossing indices do not create extra support. -/
theorem p4Q2PZ37J_originalCoveredOddEdges_card_le_four
    (p q : Plaq) (e f g k : Link) (h : Covers p q e f g k) :
    (OddSet p q).card ≤ 4 := by
  classical
  have hSub : OddSet p q ⊆ ({e,f,g,k} : Finset Link) := by
    intro a ha
    have hh := h a ((p4Q2PZ37J_originalPairOddEdges_mem H p q a).1 ha)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  have h1 := Finset.card_insert_le e ({f,g,k} : Finset Link)
  have h2 := Finset.card_insert_le f ({g,k} : Finset Link)
  have h3 := Finset.card_insert_le g ({k} : Finset Link)
  simp only [Finset.card_singleton] at h3
  have hc := Finset.card_le_card hSub
  omega

/-- A surviving four-link support necessarily has at least two shared
true spatial edges. This is a necessary condition, not an amplitude claim. -/
theorem p4Q2PZ37J_originalCoveredPair_overlap_ge_two
    (p q : Plaq) (e f g k : Link) (h : Covers p q e f g k) :
    2 ≤ (Four p ∩ Four q).card := by
  have hBalance := p4Q2PZ37J_originalPairOddEdges_card_balance H p q
  have hBound := p4Q2PZ37J_originalCoveredOddEdges_card_le_four H p q e f g k h
  omega

/-- At most one shared spatial edge forces a missing odd edge,
and therefore a zero ORIGINAL SU(2) Haar integral. -/
theorem p4Q2PZ37J_originalPairFourthTerm_zero_of_overlap_le_one
    (p q : Plaq) (e f g k : Link) (B : Cfg)
    (hOverlap : (Four p ∩ Four q).card ≤ 1) :
    Term4 p q e f g k B = 0 := by
  apply p4Q2PZ37I_originalPairFourthTerm_zero_of_notCovered H p q e f g k B
  intro h
  have hh := p4Q2PZ37J_originalCoveredPair_overlap_ge_two H p q e f g k h
  omega

/-- The full pair-weighted fourth power vanishes under the genuine
at-most-one-overlap condition; all ordered crossing tuples are integrated. -/
theorem p4Q2PZ37J_originalPairFourth_zero_of_overlap_le_one
    (p q : Plaq) (B : Cfg)
    (hOverlap : (Four p ∩ Four q).card ≤ 1) :
    Pair4 p q B = 0 := by
  classical
  rw [p4Q2PZ37I_originalPairFourth_quadrupleExpansion H p q B]
  apply Finset.sum_eq_zero
  intro e _he
  apply Finset.sum_eq_zero
  intro f _hf
  apply Finset.sum_eq_zero
  intro g _hg
  apply Finset.sum_eq_zero
  intro k _hk
  exact p4Q2PZ37J_originalPairFourthTerm_zero_of_overlap_le_one H p q e f g k B hOverlap

/-- Every distinct spatial plaquette pair has zero genuine fourth-crossing
Haar response at all nonminimal even periods. H=0 is deliberately not inferred. -/
theorem p4Q2PZ37J_originalNonminimalPairFourth_offDiagonal_zero
    (hH : 1 ≤ H) (p q : Plaq) (hpq : p ≠ q) (B : Cfg) :
    Pair4 p q B = 0 :=
  p4Q2PZ37J_originalPairFourth_zero_of_overlap_le_one H p q B
    (p4Q2PZ30_originalPairOverlap_card_le_one H hH p q hpq)

/-- Original diagonal spatial-plaquette response, retained as actual Haar
values. Its boundary constancy is NOT assumed by this definition. -/
noncomputable def p4Q2PZ37J_originalDiagonalFourth (B : Cfg) : ℝ :=
  ∑ p : Plaq, Pair4 p p B
local notation "Diag4" => p4Q2PZ37J_originalDiagonalFourth H

/-- Actual off-diagonal pair terms with at least TWO shared physical links.
No geometrically surviving Haar amplitude is discarded or presumed nonzero. -/
noncomputable def p4Q2PZ37J_originalOverlapFourth (B : Cfg) : ℝ := by
  classical
  exact ∑ p : Plaq, ∑ q : Plaq,
    if p ≠ q ∧ 2 ≤ (Four p ∩ Four q).card then Pair4 p q B else 0
local notation "Overlap4" => p4Q2PZ37J_originalOverlapFourth H

/-- Exact separation of the ORIGINAL quadratic Haar source into diagonal
and genuinely exceptional overlapping spatial pairs, at EVERY finite H. -/
theorem p4Q2PZ37J_originalQuadraticFourth_diagonal_add_overlap
    (B : Cfg) : K4 B = Diag4 B + Overlap4 B := by
  classical
  have hRow (p : Plaq) :
      (∑ q : Plaq, Pair4 p q B) = Pair4 p p B +
        ∑ q : Plaq, if p ≠ q ∧ 2 ≤ (Four p ∩ Four q).card then Pair4 p q B else 0 := by
    calc
      (∑ q : Plaq, Pair4 p q B) =
          ∑ q : Plaq, ((if q = p then Pair4 p p B else 0) +
            (if p ≠ q ∧ 2 ≤ (Four p ∩ Four q).card then Pair4 p q B else 0)) := by
        apply Finset.sum_congr rfl
        intro q _hq
        by_cases hpq : p = q
        · subst q
          simp
        · by_cases hOverlap : 2 ≤ (Four p ∩ Four q).card
          · simp [hpq, Ne.symm hpq, hOverlap]
          · have hZero := p4Q2PZ37J_originalPairFourth_zero_of_overlap_le_one
              H p q B (by omega)
            simp [hpq, Ne.symm hpq, hOverlap, hZero]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [p4Q2PZ37I_originalQuadraticTraceFourth_pairSum H B]
  calc
    (∑ p : Plaq, ∑ q : Plaq, Pair4 p q B) =
        ∑ p : Plaq, (Pair4 p p B +
          ∑ q : Plaq, if p ≠ q ∧ 2 ≤ (Four p ∩ Four q).card then Pair4 p q B else 0) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact hRow p
    _ = _ := by
      rw [Finset.sum_add_distrib]
      rfl

/-- Exceptional off-diagonal geometry is absent for every H >= 1. -/
theorem p4Q2PZ37J_originalOverlapFourth_nonminimal_zero
    (hH : 1 ≤ H) (B : Cfg) : Overlap4 B = 0 := by
  classical
  unfold p4Q2PZ37J_originalOverlapFourth
  apply Finset.sum_eq_zero
  intro p _hp
  apply Finset.sum_eq_zero
  intro q _hq
  by_cases h : p ≠ q ∧ 2 ≤ (Four p ∩ Four q).card
  · rw [if_pos h]
    exact p4Q2PZ37J_originalNonminimalPairFourth_offDiagonal_zero H hH p q h.1 B
  · rw [if_neg h]

/-- Nonminimal quadratic trace Haar response consists exactly of its
original diagonal terms, not of a postulated boundary constant. -/
theorem p4Q2PZ37J_originalQuadraticFourth_nonminimal_diagonal
    (hH : 1 ≤ H) (B : Cfg) : K4 B = Diag4 B := by
  rw [p4Q2PZ37J_originalQuadraticFourth_diagonal_add_overlap H B,
    p4Q2PZ37J_originalOverlapFourth_nonminimal_zero H hH B, add_zero]

/-- The minimal-period exception is explicit in the all-period formula. -/
theorem p4Q2PZ37J_originalQuadraticFourth_minimal_exception
    (B : Cfg) : K4 B = Diag4 B + if H = 0 then Overlap4 B else 0 := by
  by_cases hH : H = 0
  · rw [if_pos hH]
    exact p4Q2PZ37J_originalQuadraticFourth_diagonal_add_overlap H B
  · rw [if_neg hH, add_zero]
    exact p4Q2PZ37J_originalQuadraticFourth_nonminimal_diagonal H (by omega) B

/-- The physical seventh six-moment jet retains both genuine diagonal
and exceptional overlap responses with coefficient exactly 1/64. -/
theorem p4Q2PZ37J_originalPhysicalSeventhJet_diagonal_overlap
    (A B C : Cfg) :
    p4Q2PZ37B_originalPhysicalSeventhCoefficient H A B C =
      -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512 -
        W w Diag4 A B C/64 - W w Overlap4 A B C/64 := by
  rw [p4Q2PZ37I_originalPhysicalSeventhJet_pairTraceFourth H A B C]
  unfold p4Q2PZ37B_originalBoundaryWedge
  rw [p4Q2PZ37J_originalQuadraticFourth_diagonal_add_overlap H A,
    p4Q2PZ37J_originalQuadraticFourth_diagonal_add_overlap H B,
    p4Q2PZ37J_originalQuadraticFourth_diagonal_add_overlap H C]
  ring

/-- For H >= 1 only the original diagonal Haar wedge remains.
No pure Vandermonde formula is asserted without evaluating that wedge. -/
theorem p4Q2PZ37J_originalPhysicalSeventhJet_nonminimal_diagonal
    (hH : 1 ≤ H) (A B C : Cfg) :
    p4Q2PZ37B_originalPhysicalSeventhCoefficient H A B C =
      -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512 -
        W w Diag4 A B C/64 := by
  rw [p4Q2PZ37I_originalPhysicalSeventhJet_pairTraceFourth H A B C]
  unfold p4Q2PZ37B_originalBoundaryWedge
  rw [p4Q2PZ37J_originalQuadraticFourth_nonminimal_diagonal H hH A,
    p4Q2PZ37J_originalQuadraticFourth_nonminimal_diagonal H hH B,
    p4Q2PZ37J_originalQuadraticFourth_nonminimal_diagonal H hH C]

end OriginalPairOverlap
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalPairOddEdges_mem
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalPairOddEdges_card_balance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalCoveredOddEdges_card_le_four
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalCoveredPair_overlap_ge_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalPairFourthTerm_zero_of_overlap_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalPairFourth_zero_of_overlap_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalNonminimalPairFourth_offDiagonal_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalQuadraticFourth_diagonal_add_overlap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalOverlapFourth_nonminimal_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalQuadraticFourth_nonminimal_diagonal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalQuadraticFourth_minimal_exception
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalPhysicalSeventhJet_diagonal_overlap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37J_originalPhysicalSeventhJet_nonminimal_diagonal
