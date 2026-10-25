import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTriplePlaquetteOddEdgeGeometryV5_PZ28
import Mathlib.Tactic

/-!
# P4-Q2-PZ29 — genuine triple-plaquette single-junction Haar exclusion

PZ28 showed that a triple with an isolated genuine spatial plaquette
contributes zero to the original SU(2) Wilson cubic/two-crossing Haar.

The present step also handles NON-ISOLATED triples: if all physical
edges shared by one plaquette with either of the other two belong to
ONE chosen genuine spatial link (a single-junction overlap), then at
least THREE of its four actual edges occur with odd parity.

Two genuine temporal crossing links cannot cover these three odd
edges. By PZ27's exact SU(2) center-flip theorem, the original
triple-plaq/two-crossing Haar moment is zero. Every surviving
triple must therefore have TWO DISTINCT physical overlap edges
at EACH of its three plaquettes, not just a connected overlap graph.

All statements hold for every even spatial period, including period
two. There is NO claim that the further remaining triples exist, are
nonzero, or have |odd edges| <= 2. The general geometry obstruction
remains open. Original Wilson action, genuine spatial Haar, all
intermediate spatial plaquettes, physical Gauss-law source, and BOTH
genuine posterior sectors are unchanged.

No proxy, independence assumption, Dobrushin, new axiom, sorry, admit,
rank3, third Hankel positivity or mass-gap assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ29_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ29_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalTriplePlaquetteSingleJunctionSelection

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "On" => p4Q2PZ27_originalEdgeOnPlaquette H
local notation "Odd" => p4Q2PZ27_originalTripleOddEdge H
local notation "OddSet" => p4Q2PZ28_originalOddEdges H
local notation "Four" => p4Q2PZ28_originalFourEdges H
local notation "Adm" => p4Q2PZ27_originalTwoLinkCoversOddEdges H
local notation "J2" => p4Q2PZ26_originalTriplePlaquetteTwoLinkHaar H
local notation "Selected2" =>
  p4Q2PZ27_originalParityAdmissibleTripleTwoLinkHaar H
local notation "Geometric3" =>
  p4Q2PZ28_originalGeometricParitySelectedHaar H
local notation "Geo" => p4Q2PZ28_originalAtLeastTwoSharedPairs H
local notation "Z32" => p4Q2PZ24_originalCenteredCubeCrossSquareHaar H
local notation "D32" => p4Q2PZ24_originalCenteredCubeSquareDefect H
local notation "I" => (fun _ : Link =>
  (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- Every ORIGINAL physical spatial edge shared by p with either q or r
is confined to one chosen genuine link g. This is a geometric
predicate, not a substitute Wilson interaction or posterior. -/
def p4Q2PZ29_originalSingleJunctionAt
    (p q r : Plaq) (g : Link) : Prop :=
  ∀ target : Link, On p target →
    (On q target ∨ On r target) → target = g

local notation "Junction" => p4Q2PZ29_originalSingleJunctionAt H

/-- A single-junction obstruction at any one of the three original
plaquettes (including the three cyclic choices). -/
def p4Q2PZ29_originalHasSingleJunction
    (p q r : Plaq) : Prop :=
  (∃ g : Link, Junction p q r g) ∨
  (∃ g : Link, Junction q r p g) ∨
  (∃ g : Link, Junction r p q g)

local notation "Thin" => p4Q2PZ29_originalHasSingleJunction H

/-- The true odd-incidence edge count does not depend on the cyclic
ordering of its three original plaquettes. -/
theorem p4Q2PZ29_originalOddEdges_card_cyclic (p q r : Plaq) :
    (OddSet p q r).card = (OddSet q r p).card := by
  classical
  have hEq : OddSet p q r = OddSet q r p := by
    ext target
    simp only [p4Q2PZ28_originalOddEdges, Finset.mem_filter,
      Finset.mem_univ, true_and]
    unfold p4Q2PZ27_originalTripleOddEdge
    tauto
  exact congrArg Finset.card hEq

/-- At least THREE of the four ACTUAL oriented Wilson plaquette links
are odd if all overlaps of p with q or r use only the physical link g.
This uses Finset.card_sdiff_add_card_inter, not a surrogate plaquette. -/
theorem p4Q2PZ29_originalOddEdges_card_ge_three_of_junction
    (p q r : Plaq) (g : Link)
    (hJ : Junction p q r g) :
    3 ≤ (OddSet p q r).card := by
  classical
  let S : Finset Link := Four p
  have hFour : S.card = 4 :=
    p4Q2PZ28_originalFourEdges_card H p
  have hSplit :
      (S \ {g}).card + (S ∩ {g}).card = S.card :=
    Finset.card_sdiff_add_card_inter S {g}
  have hSmall : (S ∩ {g}).card ≤ 1 := by
    calc
      (S ∩ {g}).card ≤ ({g} : Finset Link).card := Finset.card_le_card (by
        intro target ht
        exact (Finset.mem_inter.mp ht).2)
      _ = 1 := Finset.card_singleton g
  have hThree : 3 ≤ (S \ {g}).card := by
    omega
  have hSubset : S \ {g} ⊆ OddSet p q r := by
    intro target ht
    obtain ⟨hS, hNot⟩ := Finset.mem_sdiff.mp ht
    have hNe : target ≠ g := by
      intro hEq
      exact hNot (by simp [hEq])
    have hp : On p target := by
      simpa [S, p4Q2PZ28_originalFourEdges,
        p4Q2PZ27_originalEdgeOnPlaquette] using hS
    have hq : ¬ On q target := by
      intro h
      exact hNe (hJ target hp (Or.inl h))
    have hr : ¬ On r target := by
      intro h
      exact hNe (hJ target hp (Or.inr h))
    simp only [p4Q2PZ28_originalOddEdges, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Or.inl ⟨hp, hq, hr⟩
  exact le_trans hThree (Finset.card_le_card hSubset)

/-- A single-junction condition at ANY face implies three or more
odd physical spatial links, including on the shortest even torus. -/
theorem p4Q2PZ29_originalOddEdges_card_ge_three_of_thin
    (p q r : Plaq) (hThin : Thin p q r) :
    3 ≤ (OddSet p q r).card := by
  rcases hThin with ⟨g, hp⟩ | ⟨g, hq⟩ | ⟨g, hr⟩
  · exact p4Q2PZ29_originalOddEdges_card_ge_three_of_junction
      H p q r g hp
  · calc
      3 ≤ (OddSet q r p).card :=
        p4Q2PZ29_originalOddEdges_card_ge_three_of_junction H q r p g hq
      _ = (OddSet p q r).card :=
        (p4Q2PZ29_originalOddEdges_card_cyclic H p q r).symm
  · calc
      3 ≤ (OddSet r p q).card :=
        p4Q2PZ29_originalOddEdges_card_ge_three_of_junction H r p q g hr
      _ = (OddSet p q r).card :=
        p4Q2PZ29_originalOddEdges_card_cyclic H r p q

/-- Every admissible genuine pair of temporal crossing links gives a
PROVED upper bound 2 on the true odd-edge finite set. -/
theorem p4Q2PZ29_originalOddEdges_card_le_two_of_covered
    (p q r : Plaq) (e f : Link)
    (hAdm : Adm p q r e f) :
    (OddSet p q r).card ≤ 2 := by
  classical
  have hSubset : OddSet p q r ⊆ ({e, f} : Finset Link) := by
    intro target ht
    have hOdd : Odd p q r target := by
      simpa [p4Q2PZ28_originalOddEdges] using ht
    by_cases he : target = e
    · simp [he]
    · by_cases hf : target = f
      · simp [hf]
      · exact False.elim ((hAdm target he hf) hOdd)
  calc
    (OddSet p q r).card ≤ ({e,f} : Finset Link).card :=
      Finset.card_le_card hSubset
    _ ≤ 2 := Finset.card_le_two

/-- No pair of ORIGINAL temporal Wilson crossings can cover the true
odd-edge support when any face has a single overlap junction. -/
theorem p4Q2PZ29_originalTwoLinks_notCover_of_singleJunction
    (p q r : Plaq) (e f : Link)
    (hThin : Thin p q r) :
    ¬ Adm p q r e f := by
  intro hAdm
  have hLarge :=
    p4Q2PZ29_originalOddEdges_card_ge_three_of_thin H p q r hThin
  have hSmall :=
    p4Q2PZ29_originalOddEdges_card_le_two_of_covered H p q r e f hAdm
  omega

/-- Original SU(2) center-flip Haar cancellation for the NEW
non-isolated single-junction obstruction, not posterior factorization. -/
theorem p4Q2PZ29_originalTripleTwoLinkHaar_zero_of_singleJunction
    (p q r : Plaq) (e f : Link) (B : Cfg)
    (hThin : Thin p q r) :
    J2 p q r e f B = 0 :=
  p4Q2PZ27_originalTripleTwoLinkHaar_zero_of_notAdmissible
    H p q r e f B
    (p4Q2PZ29_originalTwoLinks_notCover_of_singleJunction
      H p q r e f hThin)

/-- All pair-crossing contributions of a genuine thin triple vanish,
including if its three plaquettes do NOT have an isolated vertex. -/
theorem p4Q2PZ29_originalSelectedTwoLinkHaar_zero_of_singleJunction
    (p q r : Plaq) (B : Cfg) (hThin : Thin p q r) :
    Selected2 p q r B = 0 := by
  classical
  unfold p4Q2PZ27_originalParityAdmissibleTripleTwoLinkHaar
  apply Finset.sum_eq_zero
  intro e _he
  apply Finset.sum_eq_zero
  intro f _hf
  have hNot :=
    p4Q2PZ29_originalTwoLinks_notCover_of_singleJunction
      H p q r e f hThin
  simp [hNot]

/-- If overlap edges of a plaquette are NOT confined to one link,
there are at least TWO distinct physical links shared with the
other two plaquettes. The links are produced from the real incidence
predicate, not a graph-only assumption. -/
theorem p4Q2PZ29_originalTwoDistinctOverlapEdges_of_notJunction
    (p q r : Plaq)
    (hNot : ¬ ∃ g : Link, Junction p q r g) :
    ∃ a b : Link,
      a ≠ b ∧ On p a ∧ (On q a ∨ On r a) ∧
        On p b ∧ (On q b ∨ On r b) := by
  classical
  have hWitness (g : Link) :
      ∃ target : Link,
        On p target ∧ (On q target ∨ On r target) ∧ target ≠ g := by
    by_contra hNone
    apply hNot
    refine ⟨g, ?_⟩
    intro target hp hqr
    by_contra hNe
    exact hNone ⟨target, hp, hqr, hNe⟩
  obtain ⟨a, ha, haq, _haNe⟩ := hWitness (e0 p)
  obtain ⟨b, hb, hbq, hNe⟩ := hWitness a
  exact ⟨a, b, hNe.symm, ha, haq, hb, hbq⟩

/-- Necessary configuration geometry for any genuine nonzero
two-crossing Haar contribution: EACH original plaquette has two
different physical links in its overlap with the other two. -/
theorem p4Q2PZ29_originalAllFaces_twoDistinctOverlaps_of_admissible
    (p q r : Plaq) (e f : Link)
    (hAdm : Adm p q r e f) :
    (∃ a b : Link,
        a ≠ b ∧ On p a ∧ (On q a ∨ On r a) ∧
          On p b ∧ (On q b ∨ On r b)) ∧
    (∃ a b : Link,
        a ≠ b ∧ On q a ∧ (On r a ∨ On p a) ∧
          On q b ∧ (On r b ∨ On p b)) ∧
    (∃ a b : Link,
        a ≠ b ∧ On r a ∧ (On p a ∨ On q a) ∧
          On r b ∧ (On p b ∨ On q b)) := by
  have hNotThin : ¬ Thin p q r := by
    intro hThin
    exact (p4Q2PZ29_originalTwoLinks_notCover_of_singleJunction
      H p q r e f hThin) hAdm
  have hp : ¬ ∃ g : Link, Junction p q r g := by
    intro hx
    exact hNotThin (Or.inl hx)
  have hq : ¬ ∃ g : Link, Junction q r p g := by
    intro hx
    exact hNotThin (Or.inr (Or.inl hx))
  have hr : ¬ ∃ g : Link, Junction r p q g := by
    intro hx
    exact hNotThin (Or.inr (Or.inr hx))
  exact ⟨
    p4Q2PZ29_originalTwoDistinctOverlapEdges_of_notJunction H p q r hp,
    p4Q2PZ29_originalTwoDistinctOverlapEdges_of_notJunction H q r p hq,
    p4Q2PZ29_originalTwoDistinctOverlapEdges_of_notJunction H r p q hr⟩

/-- True original Haar finite sum with only the as-yet-uneliminated
triples: repeated labels, isolated faces, and one-link junctions have
each been removed by THEIR OWN proven SU(2) Haar zero identities. -/
noncomputable def p4Q2PZ29_originalNonThinGeometricHaar
    (B : Cfg) : ℝ := by
  classical
  exact ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq,
    if p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ Geo p q r ∧ ¬ Thin p q r
    then Selected2 p q r B else 0

local notation "Residual3" => p4Q2PZ29_originalNonThinGeometricHaar H

/-- All deletions from PZ28 to PZ29 are certified Haar zeros. -/
theorem p4Q2PZ29_originalGeometricHaar_onlyNonThinTriples
    (B : Cfg) :
    Geometric3 B = Residual3 B := by
  classical
  unfold p4Q2PZ28_originalGeometricParitySelectedHaar
    p4Q2PZ29_originalNonThinGeometricHaar
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hDistinct : p ≠ q ∧ p ≠ r ∧ q ≠ r
  · by_cases hGeo : Geo p q r
    · by_cases hThin : Thin p q r
      · have hZero :=
          p4Q2PZ29_originalSelectedTwoLinkHaar_zero_of_singleJunction
            H p q r B hThin
        simp [hDistinct, hGeo, hThin, hZero]
      · simp [hDistinct, hGeo, hThin]
    · simp [hDistinct, hGeo]
  · have hNotGeo :
        ¬ (p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ Geo p q r) := by
      rintro ⟨hpq, hpr, hqr, _hGeo⟩
      exact hDistinct ⟨hpq, hpr, hqr⟩
    have hNot :
        ¬ (p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ Geo p q r ∧ ¬ Thin p q r) := by
      rintro ⟨hpq, hpr, hqr, _hGeo, _hThin⟩
      exact hDistinct ⟨hpq, hpr, hqr⟩
    simp [hNotGeo, hNot]

/-- Source-preserving exact PZ24 centered cubic Haar reduced further by
the genuine PZ29 single-junction selection. -/
theorem p4Q2PZ29_originalCenteredCube_onlyNonThinGeometricTriples
    (B : Cfg) :
    Z32 B = (1 / 8 : ℝ) * Residual3 B := by
  rw [p4Q2PZ28_originalCenteredCube_onlyGeometricTriples H B,
    p4Q2PZ29_originalGeometricHaar_onlyNonThinTriples H B]

/-- The genuine boundary-normalized D32 stays a TRUE SU(2) Haar
finite sum over geometrically more constrained triple plaquettes. -/
theorem p4Q2PZ29_originalCenteredCubicDefect_onlyNonThinGeometricTriples
    (B : Cfg) :
    D32 B = (1 / 8 : ℝ) * (Residual3 B - Residual3 I) := by
  rw [p4Q2PZ28_originalCenteredCubicDefect_onlyGeometricTriples H B,
    p4Q2PZ29_originalGeometricHaar_onlyNonThinTriples H B,
    p4Q2PZ29_originalGeometricHaar_onlyNonThinTriples H I]

end OriginalTriplePlaquetteSingleJunctionSelection
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ29_originalOddEdges_card_cyclic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ29_originalOddEdges_card_ge_three_of_junction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ29_originalOddEdges_card_ge_three_of_thin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ29_originalOddEdges_card_le_two_of_covered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ29_originalTwoLinks_notCover_of_singleJunction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ29_originalTripleTwoLinkHaar_zero_of_singleJunction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ29_originalSelectedTwoLinkHaar_zero_of_singleJunction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ29_originalTwoDistinctOverlapEdges_of_notJunction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ29_originalAllFaces_twoDistinctOverlaps_of_admissible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ29_originalGeometricHaar_onlyNonThinTriples
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ29_originalCenteredCube_onlyNonThinGeometricTriples
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ29_originalCenteredCubicDefect_onlyNonThinGeometricTriples
