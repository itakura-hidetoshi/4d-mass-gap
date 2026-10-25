import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTriplePlaquetteParitySelectionV5_PZ27
import Mathlib.Tactic

/-!
# P4-Q2-PZ28 — genuine periodic plaquette triple: isolated-face obstruction

The geometry here is the ORIGINAL finite even-periodic spatial hypercubic
lattice. In particular, the four distinct physical links of each original
SU(2) Wilson spatial plaquette are used, including minimal period two.

A triple of genuine plaquettes with an isolated member (no physical edge
shared with either of the other two) has at least FOUR odd-incidence links.
Consequently, no TWO genuine temporal crossing links can cover all of its
odd links. By PZ27's proved center-flip Haar selection, every such term in
the original two-crossing triple Haar integral is zero.

The remaining finite sum is restricted to triples whose shared-edge graph
has at least two of its three possible edges. This is a necessary support
condition, NOT a claim that such connected triples occur, are nonzero, or
are boundary dependent. The general problem whether |Odd(p,q,r)| <= 2
for non-isolated triples, especially the period-two degeneracies, remains
OPEN; there is no wholesale elimination of D32.

All original Wilson plaquettes, spatial Haar, temporal crossing actions,
the physical source, and both true posterior sectors are unchanged.
No new axioms, surrogate model, sorry, admit, or mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ28_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ28_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalTriplePlaquetteOddEdgeGeometry

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H
local notation "On" => p4Q2PZ27_originalEdgeOnPlaquette H
local notation "Odd" => p4Q2PZ27_originalTripleOddEdge H
local notation "Adm" => p4Q2PZ27_originalTwoLinkCoversOddEdges H
local notation "J2" => p4Q2PZ26_originalTriplePlaquetteTwoLinkHaar H
local notation "Selected2" =>
  p4Q2PZ27_originalParityAdmissibleTripleTwoLinkHaar H
local notation "Surviving3" =>
  p4Q2PZ27_originalDistinctParityAdmissibleHaar H
local notation "Z32" => p4Q2PZ24_originalCenteredCubeCrossSquareHaar H
local notation "D32" => p4Q2PZ24_originalCenteredCubeSquareDefect H
local notation "I" => (fun _ : Link =>
  (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- Finite genuine four-link support of one oriented spatial plaquette. -/
def p4Q2PZ28_originalFourEdges (p : Plaq) : Finset Link :=
  {e0 p, e1 p, e2 p, e3 p}

/-- Each original plaquette has four DIFFERENT physical links, even at
period two; it is not an abstract square with assumed vertices. -/
theorem p4Q2PZ28_originalFourEdges_card (p : Plaq) :
    (p4Q2PZ28_originalFourEdges H p).card = 4 := by
  obtain ⟨h01, h02, h12⟩ :=
    p4Q2PU3_originalPlaquette_firstThree_distinct H p
  obtain ⟨h30, h31, h32⟩ :=
    p4Q2PU3_originalPlaquette_last_distinct H p
  simp [p4Q2PZ28_originalFourEdges,
    h01, h02, h12, Ne.symm h30, Ne.symm h31, Ne.symm h32]

/-- The actual finite set of links at odd incidence among three
original spatial plaquettes (one or three of their supports). -/
noncomputable def p4Q2PZ28_originalOddEdges
    (p q r : Plaq) : Finset Link := by
  classical
  exact Finset.univ.filter (fun target => Odd p q r target)

/-- A shared physical spatial link, independent of plaquette traversal
orientation. -/
def p4Q2PZ28_originalShareEdge (p q : Plaq) : Prop :=
  ∃ target : Link, On p target ∧ On q target

local notation "Share" => p4Q2PZ28_originalShareEdge H

theorem p4Q2PZ28_originalShareEdge_symm (p q : Plaq) :
    Share p q ↔ Share q p := by
  constructor
  · rintro ⟨target, hp, hq⟩
    exact ⟨target, hq, hp⟩
  · rintro ⟨target, hq, hp⟩
    exact ⟨target, hp, hq⟩

/-- The graph of shared ACTUAL periodic spatial links has an isolated
vertex among the three plaquette labels. This is a physical incidence
condition, not a graph substitution for the Wilson action. -/
def p4Q2PZ28_originalHasIsolatedPlaquette
    (p q r : Plaq) : Prop :=
  (¬ Share p q ∧ ¬ Share p r) ∨
  (¬ Share p q ∧ ¬ Share q r) ∨
  (¬ Share p r ∧ ¬ Share q r)

local notation "Isolated" => p4Q2PZ28_originalHasIsolatedPlaquette H

/-- Exactly two or three of the three possible genuine shared-edge
relations hold. No assertion about their total number of common edges. -/
def p4Q2PZ28_originalAtLeastTwoSharedPairs
    (p q r : Plaq) : Prop :=
  (Share p q ∧ Share p r) ∨
  (Share p q ∧ Share q r) ∨
  (Share p r ∧ Share q r)

local notation "Geo" => p4Q2PZ28_originalAtLeastTwoSharedPairs H

theorem p4Q2PZ28_originalAtLeastTwoSharedPairs_iff_noIsolated
    (p q r : Plaq) :
    Geo p q r ↔ ¬ Isolated p q r := by
  unfold p4Q2PZ28_originalAtLeastTwoSharedPairs
    p4Q2PZ28_originalHasIsolatedPlaquette
  tauto

/-- A geometrically isolated original plaquette supplies FOUR distinct
odd-incidence edges, even on the degenerate smallest even-periodic box.
This excludes |Odd| <= 2 for this class, but not yet for all triples. -/
theorem p4Q2PZ28_originalOddEdges_card_ge_four_of_isolated
    (p q r : Plaq)
    (hIso : Isolated p q r) :
    4 ≤ (p4Q2PZ28_originalOddEdges H p q r).card := by
  classical
  have hFour (s : Plaq)
      (hOdd : ∀ target, On s target → Odd p q r target) :
      4 ≤ (p4Q2PZ28_originalOddEdges H p q r).card := by
    have hSubset :
        p4Q2PZ28_originalFourEdges H s ⊆
          p4Q2PZ28_originalOddEdges H p q r := by
      intro target hMem
      have hOn : On s target := by
        simpa [p4Q2PZ28_originalFourEdges,
          p4Q2PZ27_originalEdgeOnPlaquette] using hMem
      simp only [p4Q2PZ28_originalOddEdges, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hOdd target hOn
    calc
      4 = (p4Q2PZ28_originalFourEdges H s).card :=
        (p4Q2PZ28_originalFourEdges_card H s).symm
      _ ≤ (p4Q2PZ28_originalOddEdges H p q r).card :=
        Finset.card_le_card hSubset
  rcases hIso with hP | hQ | hR
  · apply hFour p
    intro target hp
    left
    refine ⟨hp, ?_, ?_⟩
    · intro hq
      exact hP.1 ⟨target, hp, hq⟩
    · intro hr
      exact hP.2 ⟨target, hp, hr⟩
  · apply hFour q
    intro target hq
    right
    left
    refine ⟨?_, hq, ?_⟩
    · intro hp
      exact hQ.1 ⟨target, hp, hq⟩
    · intro hr
      exact hQ.2 ⟨target, hq, hr⟩
  · apply hFour r
    intro target hr
    right
    right
    left
    refine ⟨?_, ?_, hr⟩
    · intro hp
      exact hR.1 ⟨target, hp, hr⟩
    · intro hq
      exact hR.2 ⟨target, hq, hr⟩

/-- Two genuine crossing links cannot cover the odd-edge support of
a triple containing an isolated original plaquette. The contradiction
uses the already proved true four-edge free-link lemma. -/
theorem p4Q2PZ28_originalTwoLinks_notCover_of_isolated
    (p q r : Plaq) (e f : Link)
    (hIso : Isolated p q r) :
    ¬ Adm p q r e f := by
  intro hAdm
  rcases hIso with hP | hQ | hR
  · obtain ⟨target, hMember, he, hf⟩ :=
      p4Q2PU3_originalPlaquette_freeLink_for_twoCrossings H p e f
    have hp : On p target := by
      rcases hMember with h0 | h1 | h2
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h2))
    have hq : ¬ On q target := by
      intro h
      exact hP.1 ⟨target, hp, h⟩
    have hr : ¬ On r target := by
      intro h
      exact hP.2 ⟨target, hp, h⟩
    exact (hAdm target he hf) (Or.inl ⟨hp, hq, hr⟩)
  · obtain ⟨target, hMember, he, hf⟩ :=
      p4Q2PU3_originalPlaquette_freeLink_for_twoCrossings H q e f
    have hq : On q target := by
      rcases hMember with h0 | h1 | h2
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h2))
    have hp : ¬ On p target := by
      intro h
      exact hQ.1 ⟨target, h, hq⟩
    have hr : ¬ On r target := by
      intro h
      exact hQ.2 ⟨target, hq, h⟩
    exact (hAdm target he hf) (Or.inr (Or.inl ⟨hp, hq, hr⟩))
  · obtain ⟨target, hMember, he, hf⟩ :=
      p4Q2PU3_originalPlaquette_freeLink_for_twoCrossings H r e f
    have hr : On r target := by
      rcases hMember with h0 | h1 | h2
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h2))
    have hp : ¬ On p target := by
      intro h
      exact hR.1 ⟨target, h, hr⟩
    have hq : ¬ On q target := by
      intro h
      exact hR.2 ⟨target, h, hr⟩
    exact (hAdm target he hf) (Or.inr (Or.inr (Or.inl ⟨hp, hq, hr⟩)))

/-- Genuine original SU(2) spatial Haar integral vanishes, without
factorization of the posterior or alteration of any Wilson weight. -/
theorem p4Q2PZ28_originalTripleTwoLinkHaar_zero_of_isolated
    (p q r : Plaq) (e f : Link) (B : Cfg)
    (hIso : Isolated p q r) :
    J2 p q r e f B = 0 :=
  p4Q2PZ27_originalTripleTwoLinkHaar_zero_of_notAdmissible
    H p q r e f B
    (p4Q2PZ28_originalTwoLinks_notCover_of_isolated H p q r e f hIso)

/-- The COMPLETE PZ27 two-crossing sum of a geometrically isolated
triple vanishes; both crossing indices are still the original ones. -/
theorem p4Q2PZ28_originalSelectedTwoLinkHaar_zero_of_isolated
    (p q r : Plaq) (B : Cfg)
    (hIso : Isolated p q r) :
    Selected2 p q r B = 0 := by
  classical
  unfold p4Q2PZ27_originalParityAdmissibleTripleTwoLinkHaar
  apply Finset.sum_eq_zero
  intro e _he
  apply Finset.sum_eq_zero
  intro f _hf
  have hNot :=
    p4Q2PZ28_originalTwoLinks_notCover_of_isolated H p q r e f hIso
  simp [hNot]

/-- Every nonzero PZ27 triple MUST share physical edges along
at least two of the three pairs. -/
theorem p4Q2PZ28_originalSelectedTwoLinkHaar_zero_of_notGeometric
    (p q r : Plaq) (B : Cfg) (hNotGeo : ¬ Geo p q r) :
    Selected2 p q r B = 0 := by
  have hIso : Isolated p q r := by
    by_contra hNotIso
    exact hNotGeo
      ((p4Q2PZ28_originalAtLeastTwoSharedPairs_iff_noIsolated
        H p q r).2 hNotIso)
  exact p4Q2PZ28_originalSelectedTwoLinkHaar_zero_of_isolated
    H p q r B hIso

/-- Original finite sum after both PZ26 repeated-plaquette cancellation,
PZ27 odd-edge selection and PZ28 genuine shared-edge geometry selection. -/
noncomputable def p4Q2PZ28_originalGeometricParitySelectedHaar
    (B : Cfg) : ℝ := by
  classical
  exact ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq,
    if p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ Geo p q r then
      Selected2 p q r B else 0

local notation "Geometric3" =>
  p4Q2PZ28_originalGeometricParitySelectedHaar H

/-- Exact equality with the ORIGINAL Wilson Haar sum: every
geometrically discarded term has an explicit center-flip zero proof. -/
theorem p4Q2PZ28_originalDistinctParityHaar_onlyGeometricTriples
    (B : Cfg) :
    Surviving3 B = Geometric3 B := by
  classical
  unfold p4Q2PZ27_originalDistinctParityAdmissibleHaar
    p4Q2PZ28_originalGeometricParitySelectedHaar
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hDistinct : p ≠ q ∧ p ≠ r ∧ q ≠ r
  · by_cases hGeo : Geo p q r
    · simp [hDistinct, hGeo]
    · have hZero :=
        p4Q2PZ28_originalSelectedTwoLinkHaar_zero_of_notGeometric
          H p q r B hGeo
      simp [hDistinct, hGeo, hZero]
  · have hNot : ¬ (p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ Geo p q r) := by
      rintro ⟨hpq, hpr, hqr, _hGeo⟩
      exact hDistinct ⟨hpq, hpr, hqr⟩
    simp [hDistinct, hNot]

/-- PZ24's original centered cubic/two-crossing Haar term with
only the genuinely not-yet-eliminated shared-edge triples. -/
theorem p4Q2PZ28_originalCenteredCube_onlyGeometricTriples
    (B : Cfg) :
    Z32 B = (1 / 8 : ℝ) * Geometric3 B := by
  rw [p4Q2PZ27_originalCenteredCube_onlyOddEdgeCovered H B,
    p4Q2PZ28_originalDistinctParityHaar_onlyGeometricTriples H B]

/-- Exact boundary-normalized D32. This is NOT a nonzero witness
and does NOT claim geometric completeness for period-two triples. -/
theorem p4Q2PZ28_originalCenteredCubicDefect_onlyGeometricTriples
    (B : Cfg) :
    D32 B = (1 / 8 : ℝ) * (Geometric3 B - Geometric3 I) := by
  rw [p4Q2PZ27_originalCenteredCubicDefect_onlyOddEdgeCovered H B,
    p4Q2PZ28_originalDistinctParityHaar_onlyGeometricTriples H B,
    p4Q2PZ28_originalDistinctParityHaar_onlyGeometricTriples H I]

end OriginalTriplePlaquetteOddEdgeGeometry
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ28_originalFourEdges_card
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ28_originalShareEdge_symm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ28_originalAtLeastTwoSharedPairs_iff_noIsolated
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ28_originalOddEdges_card_ge_four_of_isolated
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ28_originalTwoLinks_notCover_of_isolated
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ28_originalTripleTwoLinkHaar_zero_of_isolated
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ28_originalSelectedTwoLinkHaar_zero_of_isolated
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ28_originalSelectedTwoLinkHaar_zero_of_notGeometric
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ28_originalDistinctParityHaar_onlyGeometricTriples
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ28_originalCenteredCube_onlyGeometricTriples
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ28_originalCenteredCubicDefect_onlyGeometricTriples
