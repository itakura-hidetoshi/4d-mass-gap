import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTriplePlaquetteSingleJunctionSelectionV5_PZ29
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSharedPlaquetteUniqueness
import Mathlib.Tactic

/-!
# P4-Q2-PZ30 — physical odd-edge lower bound on nonminimal even periods

For the ORIGINAL periodic SU(2) spatial Wilson plaquettes, prove the
nondegenerate geometric classification:

* Spatial side = 2*(H+1); H ≥ 1 hence physical side ≥ 4.
* Two distinct genuine spatial plaquettes cannot share TWO different
  physical links, by the existing original periodic hypercubic theorem
  asserting that two distinct links determine at most one plaquette
  when side ≥ 3.
* For three pairwise-distinct plaquettes, each of the three true
  four-edge supports therefore has at least two exclusive edges.
  These three exclusive subsets are pairwise disjoint, so the
  original odd-incidence set contains at least SIX true links.
* Original PZ27 SU(2) center-flip Haar cancellation then excludes
  every two-crossing weighted triple Haar moment. The true centered
  cubic two-crossing sector Z32 and its boundary defect D32 vanish
  on H ≥ 1, with original Wilson weights and Haar intact.

The MINIMAL spatial side = 2 (H = 0) is EXPLICITLY EXCLUDED from the
final vanishing statement; the existing two-edge uniqueness theorem
does not apply there. No unsupported extension to period two, no
independent posterior, surrogate, Dobrushin, rank3, gap, new axiom,
sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ30_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ30_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalNondegenerateTripleGeometry
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "On" => p4Q2PZ27_originalEdgeOnPlaquette H
local notation "Four" => p4Q2PZ28_originalFourEdges H
local notation "Odd" => p4Q2PZ27_originalTripleOddEdge H
local notation "OddSet" => p4Q2PZ28_originalOddEdges H
local notation "Adm" => p4Q2PZ27_originalTwoLinkCoversOddEdges H
local notation "J2" => p4Q2PZ26_originalTriplePlaquetteTwoLinkHaar H
local notation "Selected2" =>
  p4Q2PZ27_originalParityAdmissibleTripleTwoLinkHaar H
local notation "Residual3" => p4Q2PZ29_originalNonThinGeometricHaar H
local notation "Z32" => p4Q2PZ24_originalCenteredCubeCrossSquareHaar H
local notation "D32" => p4Q2PZ24_originalCenteredCubeSquareDefect H
local notation "I" => (fun _ : Link =>
  (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- True four-dimensional physical incidence of an embedded spatial
Wilson plaquette: the four links are the original signed boundary. -/
theorem p4Q2PZ30_originalTouches_of_on
    (p : Plaq) (target : Link) (hOn : On p target) :
    periodicHypercubicPlaquetteTouchesEdge
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) := by
  rcases hOn with h0 | h1 | h2 | h3
  · refine ⟨0, ?_⟩
    subst target
    rfl
  · refine ⟨1, ?_⟩
    subst target
    rfl
  · refine ⟨2, ?_⟩
    subst target
    rfl
  · refine ⟨3, ?_⟩
    subst target
    rfl

/-- For H ≥ 1, TWO distinct true spatial plaquettes cannot share TWO
different spatial physical links. This directly uses the ORIGINAL
four-dimensional periodic geometry theorem, not a graph proxy. -/
theorem p4Q2PZ30_originalDistinctPlaquettes_noTwoSharedLinks
    (hH : 1 ≤ H) (p q : Plaq) (hpq : p ≠ q)
    (a b : Link) (hab : a ≠ b)
    (hpa : On p a) (hpb : On p b)
    (hqa : On q a) (hqb : On q b) : False := by
  have hSide : 3 ≤ PeriodicHypercubicEvenSideLength H := by
    dsimp [PeriodicHypercubicEvenSideLength]
    omega
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by omega⟩
  have hFullNe :
      periodicHypercubicEvenSpatialSliceLinkEmbedding H a ≠
      periodicHypercubicEvenSpatialSliceLinkEmbedding H b := by
    intro h
    exact hab (periodicHypercubicEvenSpatialSliceLinkEmbedding_injective H h)
  have hFullEq :
      periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p =
      periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H q :=
    periodicHypercubicPlaquette_eq_of_touches_two_edges
      (PeriodicHypercubicEvenSideLength H) hSide
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H a)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H b)
      hFullNe.symm
      (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p)
      (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H q)
      (p4Q2PZ30_originalTouches_of_on H p a hpa)
      (p4Q2PZ30_originalTouches_of_on H p b hpb)
      (p4Q2PZ30_originalTouches_of_on H q a hqa)
      (p4Q2PZ30_originalTouches_of_on H q b hqb)
  exact hpq
    (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_injective H hFullEq)

/-- Nondegenerate physically distinct plaquettes have at most ONE
common genuine original spatial Wilson link. -/
theorem p4Q2PZ30_originalPairOverlap_card_le_one
    (hH : 1 ≤ H) (p q : Plaq) (hpq : p ≠ q) :
    (Four p ∩ Four q).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra hab
  have ha' := Finset.mem_inter.mp ha
  have hb' := Finset.mem_inter.mp hb
  have hOn (s : Plaq) (x : Link) (hx : x ∈ Four s) : On s x := by
    simpa [p4Q2PZ28_originalFourEdges,
      p4Q2PZ27_originalEdgeOnPlaquette] using hx
  exact p4Q2PZ30_originalDistinctPlaquettes_noTwoSharedLinks H hH
    p q hpq a b hab
    (hOn p a ha'.1) (hOn p b hb'.1)
    (hOn q a ha'.2) (hOn q b hb'.2)

/-- General mathlib finite-set counting lemma:
a four-element set overlapping each of two other finite sets in at
most one element has at least TWO exclusive elements. -/
private theorem p4Q2PZ30_two_exclusive_of_pairwise_overlap
    {α : Type*} [DecidableEq α] (A B C : Finset α)
    (hA : A.card = 4)
    (hAB : (A ∩ B).card ≤ 1)
    (hAC : (A ∩ C).card ≤ 1) :
    2 ≤ (A \ (B ∪ C)).card := by
  have hCover :
      (A ∩ (B ∪ C)).card ≤ (A ∩ B).card + (A ∩ C).card := by
    calc
      (A ∩ (B ∪ C)).card ≤ ((A ∩ B) ∪ (A ∩ C)).card :=
        Finset.card_le_card (by
          intro x hx
          obtain ⟨hAx, hBC⟩ := Finset.mem_inter.mp hx
          rcases Finset.mem_union.mp hBC with hBx | hCx
          · exact Finset.mem_union.mpr
              (Or.inl (Finset.mem_inter.mpr ⟨hAx, hBx⟩))
          · exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_inter.mpr ⟨hAx, hCx⟩)))
      _ ≤ (A ∩ B).card + (A ∩ C).card :=
        Finset.card_union_le _ _
  have hSplit := Finset.card_sdiff_add_card_inter A (B ∪ C)
  omega

/-- The three free-edge subsets of genuine plaquettes each have
cardinality ≥2 if the three true supports pairwise overlap in ≤1. -/
theorem p4Q2PZ30_originalTripleFreeEdges_card_ge_two
    (hH : 1 ≤ H) (p q r : Plaq)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    2 ≤ (Four p \ (Four q ∪ Four r)).card ∧
    2 ≤ (Four q \ (Four p ∪ Four r)).card ∧
    2 ≤ (Four r \ (Four p ∪ Four q)).card := by
  have hpq' := p4Q2PZ30_originalPairOverlap_card_le_one H hH p q hpq
  have hpr' := p4Q2PZ30_originalPairOverlap_card_le_one H hH p r hpr
  have hqr' := p4Q2PZ30_originalPairOverlap_card_le_one H hH q r hqr
  have hqp' : (Four q ∩ Four p).card ≤ 1 := by
    simpa [Finset.inter_comm] using hpq'
  have hrp' : (Four r ∩ Four p).card ≤ 1 := by
    simpa [Finset.inter_comm] using hpr'
  have hrq' : (Four r ∩ Four q).card ≤ 1 := by
    simpa [Finset.inter_comm] using hqr'
  exact ⟨
    p4Q2PZ30_two_exclusive_of_pairwise_overlap
      (Four p) (Four q) (Four r)
      (p4Q2PZ28_originalFourEdges_card H p) hpq' hpr',
    p4Q2PZ30_two_exclusive_of_pairwise_overlap
      (Four q) (Four p) (Four r)
      (p4Q2PZ28_originalFourEdges_card H q) hqp' hqr',
    p4Q2PZ30_two_exclusive_of_pairwise_overlap
      (Four r) (Four p) (Four q)
      (p4Q2PZ28_originalFourEdges_card H r) hrp' hrq'⟩

/-- GENERAL mathlib finite combinatorics: three disjoint families
of at least two exclusive members yield six distinct members of
ANY genuine finite odd-support set containing all three families.
Passing the actual target finite set explicitly avoids accidental
changes of Fintype/DecidablePred instances. -/
private theorem p4Q2PZ30_threeFourSets_odd_card_ge_six
    {α : Type*} [DecidableEq α]
    (A B C O : Finset α)
    (hFreeA : 2 ≤ (A \ (B ∪ C)).card)
    (hFreeB : 2 ≤ (B \ (A ∪ C)).card)
    (hFreeC : 2 ≤ (C \ (A ∪ B)).card)
    (hA : ∀ x, x ∈ A → x ∉ B → x ∉ C → x ∈ O)
    (hB : ∀ x, x ∈ B → x ∉ A → x ∉ C → x ∈ O)
    (hC : ∀ x, x ∈ C → x ∉ A → x ∉ B → x ∈ O) :
    6 ≤ O.card := by
  classical
  let AP : Finset α := A \ (B ∪ C)
  let BP : Finset α := B \ (A ∪ C)
  let CP : Finset α := C \ (A ∪ B)
  have hPsub : AP ⊆ O := by
    intro x hx
    obtain ⟨ha, hnotBC⟩ := Finset.mem_sdiff.mp hx
    have hb : x ∉ B := by
      intro h
      exact hnotBC (Finset.mem_union.mpr (Or.inl h))
    have hc : x ∉ C := by
      intro h
      exact hnotBC (Finset.mem_union.mpr (Or.inr h))
    exact hA x ha hb hc
  have hQsub : BP ⊆ O := by
    intro x hx
    obtain ⟨hb, hnotAC⟩ := Finset.mem_sdiff.mp hx
    have ha : x ∉ A := by
      intro h
      exact hnotAC (Finset.mem_union.mpr (Or.inl h))
    have hc : x ∉ C := by
      intro h
      exact hnotAC (Finset.mem_union.mpr (Or.inr h))
    exact hB x hb ha hc
  have hRsub : CP ⊆ O := by
    intro x hx
    obtain ⟨hc, hnotAB⟩ := Finset.mem_sdiff.mp hx
    have ha : x ∉ A := by
      intro h
      exact hnotAB (Finset.mem_union.mpr (Or.inl h))
    have hb : x ∉ B := by
      intro h
      exact hnotAB (Finset.mem_union.mpr (Or.inr h))
    exact hC x hc ha hb
  have hDisjAB : Disjoint AP BP := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hnot := (Finset.mem_sdiff.mp hx).2
    exact hnot (Finset.mem_union.mpr
      (Or.inl (Finset.mem_sdiff.mp hy).1))
  have hDisjAC : Disjoint AP CP := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hnot := (Finset.mem_sdiff.mp hx).2
    exact hnot (Finset.mem_union.mpr
      (Or.inr (Finset.mem_sdiff.mp hy).1))
  have hDisjBC : Disjoint BP CP := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hnot := (Finset.mem_sdiff.mp hx).2
    exact hnot (Finset.mem_union.mpr
      (Or.inr (Finset.mem_sdiff.mp hy).1))
  have hDisjAll : Disjoint (AP ∪ BP) CP := by
    apply Finset.disjoint_left.mpr
    intro x hxy hz
    rcases Finset.mem_union.mp hxy with ha | hb
    · exact (Finset.disjoint_left.mp hDisjAC) ha hz
    · exact (Finset.disjoint_left.mp hDisjBC) hb hz
  have hSubset : (AP ∪ BP) ∪ CP ⊆ O := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxy | hc
    · rcases Finset.mem_union.mp hxy with ha | hb
      · exact hPsub ha
      · exact hQsub hb
    · exact hRsub hc
  have hCardUnion :
      ((AP ∪ BP) ∪ CP).card = AP.card + BP.card + CP.card := by
    rw [Finset.card_union_of_disjoint hDisjAll,
      Finset.card_union_of_disjoint hDisjAB]
  have hBound := Finset.card_le_card hSubset
  dsimp [AP, BP, CP] at hCardUnion
  dsimp [AP, BP, CP] at hBound
  omega

/-- For H ≥ 1, a triple of pairwise-distinct ORIGINAL spatial Wilson
plaquettes has at least SIX genuinely odd-incidence spatial links.
No finite Fintype enumerations or synthetic observable are used. -/
theorem p4Q2PZ30_originalTripleOddEdges_card_ge_six
    (hH : 1 ≤ H) (p q r : Plaq)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    6 ≤ (OddSet p q r).card := by
  classical
  obtain ⟨hp, hq, hr⟩ :=
    p4Q2PZ30_originalTripleFreeEdges_card_ge_two
      H hH p q r hpq hpr hqr
  have hMem (s : Plaq) (x : Link) :
      x ∈ Four s ↔ On s x := by
    simp [p4Q2PZ28_originalFourEdges,
      p4Q2PZ27_originalEdgeOnPlaquette]
  apply p4Q2PZ30_threeFourSets_odd_card_ge_six
    (Four p) (Four q) (Four r) (OddSet p q r)
    hp hq hr
  · intro x hx hNotQ hNotR
    have hP : On p x := (hMem p x).mp hx
    have hQ : ¬ On q x := by
      intro h
      exact hNotQ ((hMem q x).mpr h)
    have hR : ¬ On r x := by
      intro h
      exact hNotR ((hMem r x).mpr h)
    simp only [p4Q2PZ28_originalOddEdges,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨hP, hQ, hR⟩
  · intro x hx hNotP hNotR
    have hQ : On q x := (hMem q x).mp hx
    have hP : ¬ On p x := by
      intro h
      exact hNotP ((hMem p x).mpr h)
    have hR : ¬ On r x := by
      intro h
      exact hNotR ((hMem r x).mpr h)
    simp only [p4Q2PZ28_originalOddEdges,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr (Or.inl ⟨hP, hQ, hR⟩)
  · intro x hx hNotP hNotQ
    have hR : On r x := (hMem r x).mp hx
    have hP : ¬ On p x := by
      intro h
      exact hNotP ((hMem p x).mpr h)
    have hQ : ¬ On q x := by
      intro h
      exact hNotQ ((hMem q x).mpr h)
    simp only [p4Q2PZ28_originalOddEdges,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr (Or.inl ⟨hP, hQ, hR⟩))

/-- No two real temporal crossing Wilson links can support a pairwise
distinct triple on a spatial torus of side 2*(H+1) ≥4. -/
theorem p4Q2PZ30_originalTripleTwoLinks_notCover
    (hH : 1 ≤ H) (p q r : Plaq)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (e f : Link) :
    ¬ Adm p q r e f := by
  intro hAdm
  have hLarge :=
    p4Q2PZ30_originalTripleOddEdges_card_ge_six
      H hH p q r hpq hpr hqr
  have hSmall :=
    p4Q2PZ29_originalOddEdges_card_le_two_of_covered
      H p q r e f hAdm
  omega

/-- Genuine SU(2) center parity gives TRUE Haar zero; no spatial
posterior factorization or modified Wilson action. -/
theorem p4Q2PZ30_originalTripleTwoLinkHaar_zero
    (hH : 1 ≤ H) (p q r : Plaq)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (e f : Link) (B : Cfg) :
    J2 p q r e f B = 0 :=
  p4Q2PZ27_originalTripleTwoLinkHaar_zero_of_notAdmissible
    H p q r e f B
    (p4Q2PZ30_originalTripleTwoLinks_notCover H hH
      p q r hpq hpr hqr e f)

/-- Every ordered true two-link crossing term for a distinct original
spatial triple vanishes on nonminimal even periods. -/
theorem p4Q2PZ30_originalSelectedTwoLinkHaar_zero
    (hH : 1 ≤ H) (p q r : Plaq)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (B : Cfg) :
    Selected2 p q r B = 0 := by
  classical
  unfold p4Q2PZ27_originalParityAdmissibleTripleTwoLinkHaar
  apply Finset.sum_eq_zero
  intro e _he
  apply Finset.sum_eq_zero
  intro f _hf
  have hNot :=
    p4Q2PZ30_originalTripleTwoLinks_notCover H hH
      p q r hpq hpr hqr e f
  simp [hNot]

/-- All terms of the TRUE PZ29 geometric Haar finite sum vanish for
H ≥1; this statement deliberately excludes H=0, period two. -/
theorem p4Q2PZ30_originalNonminimalResidualTripleHaar_zero
    (hH : 1 ≤ H) (B : Cfg) :
    Residual3 B = 0 := by
  classical
  unfold p4Q2PZ29_originalNonThinGeometricHaar
  apply Finset.sum_eq_zero
  intro p _hp
  apply Finset.sum_eq_zero
  intro q _hq
  apply Finset.sum_eq_zero
  intro r _hr
  by_cases hDistinct : p ≠ q ∧ p ≠ r ∧ q ≠ r
  · obtain ⟨hpq, hpr, hqr⟩ := hDistinct
    have hZero :=
      p4Q2PZ30_originalSelectedTwoLinkHaar_zero H hH
        p q r hpq hpr hqr B
    simp [hpq, hpr, hqr, hZero]
  · have hNot :
        ¬ (p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
          p4Q2PZ28_originalAtLeastTwoSharedPairs H p q r ∧
          ¬ p4Q2PZ29_originalHasSingleJunction H p q r) := by
      rintro ⟨hpq, hpr, hqr, _, _⟩
      exact hDistinct ⟨hpq, hpr, hqr⟩
    simp [hNot]

/-- New exact Haar cancellation on nonminimal even periodicity,
still referring to the ORIGINAL centered cubic Wilson sector. -/
theorem p4Q2PZ30_originalNonminimalCenteredCube_zero
    (hH : 1 ≤ H) (B : Cfg) :
    Z32 B = 0 := by
  rw [p4Q2PZ29_originalCenteredCube_onlyNonThinGeometricTriples H B,
    p4Q2PZ30_originalNonminimalResidualTripleHaar_zero H hH B]
  ring

/-- Exact boundary-normalized cubic defect vanishes for H ≥ 1.
The H=0 period-two obstruction is not silently removed. -/
theorem p4Q2PZ30_originalNonminimalCenteredCubicDefect_zero
    (hH : 1 ≤ H) (B : Cfg) :
    D32 B = 0 := by
  rw [p4Q2PZ29_originalCenteredCubicDefect_onlyNonThinGeometricTriples H B,
    p4Q2PZ30_originalNonminimalResidualTripleHaar_zero H hH B,
    p4Q2PZ30_originalNonminimalResidualTripleHaar_zero H hH I]
  ring

end OriginalNondegenerateTripleGeometry
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ30_originalTouches_of_on
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ30_originalDistinctPlaquettes_noTwoSharedLinks
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ30_originalPairOverlap_card_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ30_originalTripleFreeEdges_card_ge_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ30_originalTripleOddEdges_card_ge_six
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ30_originalTripleTwoLinks_notCover
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ30_originalTripleTwoLinkHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ30_originalSelectedTwoLinkHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ30_originalNonminimalResidualTripleHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ30_originalNonminimalCenteredCube_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ30_originalNonminimalCenteredCubicDefect_zero
