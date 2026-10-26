import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalOddFourFactorialV5_PZ37L
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalMinimalPairOverlapV5_PZ37J
import Mathlib.Tactic

/-!
# PZ37L — exact genuine period-two overlap response

Kernel decide classifies the actual 48 ordered pairs into the two possible
opposite-edge sharing orientations. Genuine Haar contraction gives 3/128
times a product of two normalized boundary winding characters per pair.
Thus R_0 is an explicit finite boundary polynomial, and R_0(I)=9/8.
The seventh jet is transported to this polynomial; no actual-minor
remainder or vanishing of its alternating wedge is presumed.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 29000000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 1050000
local instance p4Q2PZ37L_min_fullVertexDecidableEq :
    DecidableEq (PeriodicHypercubicEvenVertex 0) := Fintype.decidablePiFintype
local instance p4Q2PZ37L_min_spatialVertexDecidableEq :
    DecidableEq (PeriodicHypercubicEvenSpatialSliceVertex 0) := Subtype.instDecidableEq
local instance p4Q2PZ37L_min_directionDecidableEq :
    DecidableEq PeriodicHypercubicEvenSpatialDirection := Subtype.instDecidableEq
local instance p4Q2PZ37L_min_planeDecidableEq :
    DecidableEq PeriodicHypercubicEvenSpatialDirectionPair := Subtype.instDecidableEq
local instance p4Q2PZ37L_min_linkDecidableEq :
    DecidableEq (PeriodicHypercubicEvenSpatialSliceLink 0) := instDecidableEqProd
local instance p4Q2PZ37L_min_plaqDecidableEq :
    DecidableEq (PeriodicHypercubicEvenSpatialSlicePlaquette 0) := instDecidableEqProd
local instance p4Q2PZ37L_min_primaryPlaneDecidable :
    DecidablePred (periodicHypercubicEvenOnPrimaryReflectionPlane 0) :=
  fun v => inferInstanceAs (Decidable (v 0 = 0))
local instance p4Q2PZ37L_min_vertexFintype :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex 0) :=
  Fintype.subtype
    (Finset.univ.filter (periodicHypercubicEvenOnPrimaryReflectionPlane 0))
    (by intro v; simp)
local instance p4Q2PZ37L_min_directionFintype :
    Fintype PeriodicHypercubicEvenSpatialDirection :=
  Fintype.subtype
    ((Finset.univ : Finset PeriodicHypercubicAxis).filter (fun mu => mu ≠ 0))
    (by intro mu; simp)
local instance p4Q2PZ37L_min_planeFintype :
    Fintype PeriodicHypercubicEvenSpatialDirectionPair :=
  Fintype.subtype
    ((Finset.univ : Finset (PeriodicHypercubicEvenSpatialDirection ×
      PeriodicHypercubicEvenSpatialDirection)).filter (fun d => d.1.1 < d.2.1))
    (by intro d; simp)
local instance p4Q2PZ37L_min_linkFintype :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink 0) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex 0)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ37L_min_plaqFintype :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette 0) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex 0)
    PeriodicHypercubicEvenSpatialDirectionPair


namespace GroundStatePosteriorJoint
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink 0
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette 0
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 0 2
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 0
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 0
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 0
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 0
local notation "Four" => p4Q2PZ28_originalFourEdges 0
local notation "CFour" => p4Q2PZ37J_computableMinimalFourEdges
local notation "Pair4" => p4Q2PZ37I_originalPairTraceFourth 0
local notation "Term4" => p4Q2PZ37I_originalPairFourthTerm 0
local notation "Odd" => p4Q2PZ37I_originalPairOddEdge 0
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter 0
local notation "ch" => p4Q2PZ35C_originalOneLinkCharacter
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Pairs" => p4Q2PZ37J_originalMinimalOverlapPairs
local notation "Overlap4" => p4Q2PZ37J_originalOverlapFourth 0
local notation "w" => p4Q2PS_originalHalfSpatialAction 0
local notation "W" => p4Q2PZ37B_originalBoundaryWedge 0
local notation "I" => (fun _ : Link => (1 : G))

/-- The two orientations use genuine edges of the original plaquettes. -/
def p4Q2PZ37L_originalMinimalPairShape (p q : Plaq) : Prop :=
  (e1 q = e3 p ∧ e3 q = e1 p ∧
    ([e0 p,e2 p,e0 q,e2 q,e1 p,e3 p] : List Link).Nodup) ∨
  (e0 q = e2 p ∧ e2 q = e0 p ∧
    ([e3 p,e1 p,e3 q,e1 q,e2 p,e0 p] : List Link).Nodup)

private theorem shape_certificate : ∀ p q : Plaq, p ≠ q →
    (CFour p ∩ CFour q).card = 2 → p4Q2PZ37L_originalMinimalPairShape p q := by
  unfold p4Q2PZ37L_originalMinimalPairShape
  decide

/-- Unconditional geometry classification on the original physical carriers. -/
theorem p4Q2PZ37L_originalMinimalPairShape_of_overlap
    (p q : Plaq) (hpq : p ≠ q) (h : (Four p ∩ Four q).card = 2) :
    p4Q2PZ37L_originalMinimalPairShape p q := by
  apply shape_certificate p q hpq
  simpa only [p4Q2PZ37J_computableMinimalFourEdges_eq_original] using h

noncomputable section

/-- Product of two actual length-two boundary winding characters. -/
def p4Q2PZ37L_originalMinimalBoundaryLoops (p q : Plaq) (B : Cfg) : ℝ :=
  if e1 q = e3 p ∧ e3 q = e1 p then
    ch (B (e0 p)*B (e0 q))*ch (B (e2 p)*B (e2 q))
  else ch (B (e3 p)*B (e3 q))*ch (B (e1 p)*B (e1 q))
local notation "Loops" => p4Q2PZ37L_originalMinimalBoundaryLoops

private theorem odd_six (a b c d s t x : Link)
    (hn : ([a,b,c,d,s,t] : List Link).Nodup) :
    (((x=a ∨ x=s ∨ x=b ∨ x=t) ∧ ¬(x=c ∨ x=t ∨ x=d ∨ x=s)) ∨
      (¬(x=a ∨ x=s ∨ x=b ∨ x=t) ∧ (x=c ∨ x=t ∨ x=d ∨ x=s))) ↔
      x ∈ [a,b,c,d] := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil,
    List.not_mem_nil, not_false_eq_true, and_true] at hn
  by_cases ha : x=a
  · subst x; simp_all
  by_cases hb : x=b
  · subst x; simp_all
  by_cases hc : x=c
  · subst x; simp_all
  by_cases hd : x=d
  · subst x; simp_all
  by_cases hs : x=s
  · subst x; simp_all
  by_cases ht : x=t
  · subst x; simp_all
  simp_all

private theorem nodup_first_four (a b c d s t : Link)
    (hn : ([a,b,c,d,s,t] : List Link).Nodup) : ([a,b,c,d] : List Link).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil,
    List.not_mem_nil, not_false_eq_true, and_true] at hn ⊢
  tauto

private theorem char_inverse_word (p : Plaq) (X : Cfg) :
    χ p X = ch (X (e3 p)*X (e2 p)*(X (e1 p))⁻¹*(X (e0 p))⁻¹) := by
  change ch (X (e0 p)*X (e1 p)*(X (e2 p))⁻¹*(X (e3 p))⁻¹) = _
  rw [← p4Q2PZ35D5_originalCharacter_inv
    (X (e0 p)*X (e1 p)*(X (e2 p))⁻¹*(X (e3 p))⁻¹)]
  congr 1
  group

/-- Every surviving physical pair has its exact non-assumed boundary amplitude. -/
theorem p4Q2PZ37L_originalMinimalPairFourth_exact
    (p q : Plaq) (hpq : p ≠ q) (h : (Four p ∩ Four q).card = 2) (B : Cfg) :
    Pair4 p q B = (3/128 : ℝ)*Loops p q B := by
  rcases p4Q2PZ37L_originalMinimalPairShape_of_overlap p q hpq h with
    ⟨h1,h3,hn⟩ | ⟨h0,h2,hn⟩
  · have hOdd (x : Link) : Odd p q x ↔ x ∈ [e0 p,e2 p,e0 q,e2 q] := by
      unfold p4Q2PZ37I_originalPairOddEdge p4Q2PZ27_originalEdgeOnPlaquette
      rw [h1,h3]
      exact odd_six _ _ _ _ _ _ x hn
    rw [p4Q2PZ37L_originalPairFourth_eq_twentyFour 0 p q
      (e0 p) (e2 p) (e0 q) (e2 q) (nodup_first_four _ _ _ _ _ _ hn) hOdd]
    have hi := p4Q2PZ37L_originalSixLinkOverlap_exact 0
      (e0 p) (e2 p) (e0 q) (e2 q) (e1 p) (e3 p) hn B
    have hTerm : Term4 p q (e0 p) (e2 p) (e0 q) (e2 q) B =
        (1/1024 : ℝ)*ch (B (e0 p)*B (e0 q))*ch (B (e2 p)*B (e2 q)) := by
      unfold p4Q2PZ37I_originalPairFourthTerm p4Q2PV_originalPlaquetteRealCharacter
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
      change (∫ X : Cfg, ch (X (e0 p)*X (e1 p)*(X (e2 p))⁻¹*(X (e3 p))⁻¹)*
        ch (X (e0 q)*X (e1 q)*(X (e2 q))⁻¹*(X (e3 q))⁻¹)*_ ∂_) = _
      rw [h1,h3]
      exact hi
    rw [hTerm]
    simp only [p4Q2PZ37L_originalMinimalBoundaryLoops, h1,h3, and_self, if_true]
    ring
  · have hOdd (x : Link) : Odd p q x ↔ x ∈ [e3 p,e1 p,e3 q,e1 q] := by
      have hh := odd_six (e3 p) (e1 p) (e3 q) (e1 q) (e2 p) (e0 p) x hn
      unfold p4Q2PZ37I_originalPairOddEdge p4Q2PZ27_originalEdgeOnPlaquette
      rw [h0,h2]
      tauto
    rw [p4Q2PZ37L_originalPairFourth_eq_twentyFour 0 p q
      (e3 p) (e1 p) (e3 q) (e1 q) (nodup_first_four _ _ _ _ _ _ hn) hOdd]
    have hi := p4Q2PZ37L_originalSixLinkOverlap_exact 0
      (e3 p) (e1 p) (e3 q) (e1 q) (e2 p) (e0 p) hn B
    have hTerm : Term4 p q (e3 p) (e1 p) (e3 q) (e1 q) B =
        (1/1024 : ℝ)*ch (B (e3 p)*B (e3 q))*ch (B (e1 p)*B (e1 q)) := by
      unfold p4Q2PZ37I_originalPairFourthTerm
      simp_rw [char_inverse_word, h0,h2]
      exact hi
    rw [hTerm]
    have hNot : ¬(e1 q = e3 p ∧ e3 q = e1 p) := by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil,
        List.not_mem_nil, not_false_eq_true, and_true] at hn
      intro hh
      tauto
    rw [p4Q2PZ37L_originalMinimalBoundaryLoops, if_neg hNot]
    ring

/-- Sum over exactly the previously kernel-counted 48 ordered physical pairs. -/
def p4Q2PZ37L_originalMinimalBoundaryLoopSum (B : Cfg) : ℝ :=
  ∑ pq ∈ Pairs, Loops pq.1 pq.2 B
local notation "LoopSum" => p4Q2PZ37L_originalMinimalBoundaryLoopSum

/-- The genuine minimal-period Haar response is now a finite boundary polynomial. -/
theorem p4Q2PZ37L_originalMinimalOverlapFourth_exact (B : Cfg) :
    Overlap4 B = (3/128 : ℝ)*LoopSum B := by
  have hProd (f : Plaq × Plaq → ℝ) :
      (∑ pq : Plaq × Plaq, f pq) = ∑ p : Plaq, ∑ q : Plaq, f (p,q) :=
    Fintype.sum_prod_type f
  unfold p4Q2PZ37J_originalOverlapFourth p4Q2PZ37L_originalMinimalBoundaryLoopSum
    p4Q2PZ37J_originalMinimalOverlapPairs
  rw [Finset.mul_sum]
  simp only [Finset.sum_filter]
  rw [hProd]
  apply Finset.sum_congr (by ext p; simp)
  intro p _
  apply Finset.sum_congr (by ext q; simp)
  intro q _
  by_cases hpq : p=q
  · simp [hpq]
  · have hle := p4Q2PZ37J_originalMinimalOverlap_le_two p q hpq
    have hiff : 2 ≤ (Four p ∩ Four q).card ↔ (Four p ∩ Four q).card = 2 := by omega
    by_cases h : (Four p ∩ Four q).card = 2
    · simp only [hpq, not_false_eq_true, true_and, hiff, h, if_true]
      exact p4Q2PZ37L_originalMinimalPairFourth_exact p q hpq h B
    · have hno : ¬ 2 ≤ (Four p ∩ Four q).card := by omega
      simp [h,hno]

/-- At identity boundary every normalized winding character is one. -/
theorem p4Q2PZ37L_originalMinimalBoundaryLoops_identity (p q : Plaq) : Loops p q I = 1 := by
  have hOne : ch (1 : G) = 1 := by
    unfold p4Q2PZ35C_originalOneLinkCharacter
    rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by decide)]
    norm_num
  simp [p4Q2PZ37L_originalMinimalBoundaryLoops,hOne]

/-- Each of the 48 geometric pairs has the exact positive amplitude at I. -/
theorem p4Q2PZ37L_originalMinimalPairFourth_identity
    (p q : Plaq) (hpq : p ≠ q) (h : (Four p ∩ Four q).card = 2) :
    Pair4 p q I = (3/128 : ℝ) := by
  rw [p4Q2PZ37L_originalMinimalPairFourth_exact p q hpq h,
    p4Q2PZ37L_originalMinimalBoundaryLoops_identity, mul_one]

/-- Nonvanishing is proved at the specified identity boundary, not assumed. -/
theorem p4Q2PZ37L_originalMinimalPairFourth_identity_pos
    (p q : Plaq) (hpq : p ≠ q) (h : (Four p ∩ Four q).card = 2) :
    0 < Pair4 p q I := by
  rw [p4Q2PZ37L_originalMinimalPairFourth_identity p q hpq h]
  norm_num

/-- The 48 actual supported Haar amplitudes give an exact nonzero total at I. -/
theorem p4Q2PZ37L_originalMinimalOverlapFourth_identity : Overlap4 I = (9/8 : ℝ) := by
  rw [p4Q2PZ37L_originalMinimalOverlapFourth_exact]
  unfold p4Q2PZ37L_originalMinimalBoundaryLoopSum
  simp_rw [p4Q2PZ37L_originalMinimalBoundaryLoops_identity]
  simp [p4Q2PZ37J_originalMinimalOverlapPairs_card]
  norm_num

/-- Minimal-period seventh Taylor JET with no unevaluated Haar response.
Its remaining boundary-loop wedge is not presumed zero. -/
theorem p4Q2PZ37L_originalMinimalPhysicalSeventhJet_exact (A B C : Cfg) :
    p4Q2PZ37B_originalPhysicalSeventhCoefficient 0 A B C =
      -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512 -
        (3/8192 : ℝ)*W w LoopSum A B C := by
  rw [p4Q2PZ37K_originalPhysicalSeventhJet_overlapOnly]
  unfold p4Q2PZ37B_originalBoundaryWedge
  rw [p4Q2PZ37L_originalMinimalOverlapFourth_exact A,
    p4Q2PZ37L_originalMinimalOverlapFourth_exact B,
    p4Q2PZ37L_originalMinimalOverlapFourth_exact C]
  ring

end
end GroundStatePosteriorJoint
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalMinimalPairShape_of_overlap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalMinimalPairFourth_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalMinimalOverlapFourth_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalMinimalBoundaryLoops_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalMinimalPairFourth_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalMinimalPairFourth_identity_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalMinimalOverlapFourth_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalMinimalPhysicalSeventhJet_exact
