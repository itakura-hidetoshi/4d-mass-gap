import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTriplePlaquetteTwoCrossingV5_PZ26
import Mathlib.Tactic

/-!
# P4-Q2-PZ27 — genuine SU(2) Haar triple-plaquette edge parity

PZ26 reduced the ORIGINAL centered cubic/two-crossing Wilson Haar
obstruction to ordered triples of pairwise distinct genuine spatial
plaquettes, with the original two temporal crossing links retained.

This file proves the additional, explicitly local SU(2) CENTER-PARITY
selection rule. On each original spatial link, a genuine plaquette
character is odd precisely when the link lies on its four oriented
plaquette edges; otherwise it is unchanged by the exact center flip.
The product of three plaquette characters is therefore odd when that
link has ODD incidence in the three plaquettes (one or three).
If that spatial link is not one of the TWO genuine temporal crossing
links, the original spatial product Haar integral is zero.

We retain only ordered pairs of actual temporal crossing links that
cover EVERY odd-incidence edge of a pairwise-distinct triple. This is
a necessary Haar SUPPORT condition, not an assertion that the
surviving terms are nonzero, boundary dependent or positive.

The original SU(2) Wilson one-slab action, plaquettes, spatial Haar,
Gauss-law physical source, both genuine posterior sectors, and PZ24
sixth Ward obstruction remain untouched. No surrogate, independent
posterior, Dobrushin, new axiom, sorry, admit, rank3 or gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ27_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ27_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ27_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ27_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ27_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ27_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ27_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair
local instance p4Q2PZ27_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section GenuineTriplePlaquetteOddEdgeSelection
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H
local notation "J2" => p4Q2PZ26_originalTriplePlaquetteTwoLinkHaar H
local notation "T3" => p4Q2PZ26_originalTriplePlaquetteCrossSquareHaar H
local notation "Distinct3" => p4Q2PZ26_originalDistinctPlaquetteTripleHaar H
local notation "Z32" => p4Q2PZ24_originalCenteredCubeCrossSquareHaar H
local notation "D32" => p4Q2PZ24_originalCenteredCubeSquareDefect H
local notation "I" => (fun _ : Link =>
  (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- Physical original plaquette incidence, defined from the four
actual oriented spatial links. No abstract parity surrogate. -/
def p4Q2PZ27_originalEdgeOnPlaquette (p : Plaq) (target : Link) : Prop :=
  target = e0 p ∨ target = e1 p ∨
    target = e2 p ∨ target = e3 p

local notation "On" => p4Q2PZ27_originalEdgeOnPlaquette H

/-- Odd incidence in the TRUE three spatial plaquettes means EXACTLY
one or all three original plaquette characters change sign under
this particular SU(2) center flip. -/
def p4Q2PZ27_originalTripleOddEdge
    (p q r : Plaq) (target : Link) : Prop :=
  (On p target ∧ ¬On q target ∧ ¬On r target) ∨
  (¬On p target ∧ On q target ∧ ¬On r target) ∨
  (¬On p target ∧ ¬On q target ∧ On r target) ∨
  (On p target ∧ On q target ∧ On r target)

local notation "Odd" => p4Q2PZ27_originalTripleOddEdge H

/-- A true ordered pair of temporal crossing links may carry a
three-plaquette Haar contribution ONLY if every odd-incidence spatial
link is among the two genuine temporal Wilson crossing links. -/
def p4Q2PZ27_originalTwoLinkCoversOddEdges
    (p q r : Plaq) (e f : Link) : Prop :=
  ∀ target : Link, target ≠ e → target ≠ f → ¬ Odd p q r target

local notation "Admissible" => p4Q2PZ27_originalTwoLinkCoversOddEdges H

/-- The original spatial plaquette character is center-ODD at any
one of its four genuine oriented spatial links. -/
theorem p4Q2PZ27_originalCharacter_centerOdd_of_edge
    (p : Plaq) (target : Link) (X : Cfg)
    (hp : On p target) :
    χ p (Flip target X) = -χ p X :=
  p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_four
    H p target hp X

/-- At any link OUTSIDE its four genuine spatial plaquette edges,
the original SU(2) plaquette character is center-INVARIANT. -/
theorem p4Q2PZ27_originalCharacter_centerEven_of_freeEdge
    (p : Plaq) (target : Link) (X : Cfg)
    (hp : ¬ On p target) :
    χ p (Flip target X) = χ p X :=
  p4Q2PY8_originalPlaquetteChar_centerUnchanged_of_freeEdge
    H p target hp X

/-- Exact sign of the original TRIPLE plaquette-character product
at a spatial edge of odd multiplicity, with no assumption of
pairwise distinct plaquettes. The four genuine parity cases are
proved separately, avoiding classical if-projection surrogates. -/
theorem p4Q2PZ27_originalTripleCharacter_centerOdd
    (p q r : Plaq) (target : Link)
    (hOdd : Odd p q r target) (X : Cfg) :
    ((χ p (Flip target X) * χ q (Flip target X)) *
      χ r (Flip target X)) =
        -((χ p X * χ q X) * χ r X) := by
  rcases hOdd with hOne | hTwo | hThree | hAll
  · obtain ⟨hp,hq,hr⟩ := hOne
    rw [p4Q2PZ27_originalCharacter_centerOdd_of_edge H p target X hp,
      p4Q2PZ27_originalCharacter_centerEven_of_freeEdge H q target X hq,
      p4Q2PZ27_originalCharacter_centerEven_of_freeEdge H r target X hr]
    ring
  · obtain ⟨hp,hq,hr⟩ := hTwo
    rw [p4Q2PZ27_originalCharacter_centerEven_of_freeEdge H p target X hp,
      p4Q2PZ27_originalCharacter_centerOdd_of_edge H q target X hq,
      p4Q2PZ27_originalCharacter_centerEven_of_freeEdge H r target X hr]
    ring
  · obtain ⟨hp,hq,hr⟩ := hThree
    rw [p4Q2PZ27_originalCharacter_centerEven_of_freeEdge H p target X hp,
      p4Q2PZ27_originalCharacter_centerEven_of_freeEdge H q target X hq,
      p4Q2PZ27_originalCharacter_centerOdd_of_edge H r target X hr]
    ring
  · obtain ⟨hp,hq,hr⟩ := hAll
    rw [p4Q2PZ27_originalCharacter_centerOdd_of_edge H p target X hp,
      p4Q2PZ27_originalCharacter_centerOdd_of_edge H q target X hq,
      p4Q2PZ27_originalCharacter_centerOdd_of_edge H r target X hr]
    ring

/-- GENUINE SU(2) Haar selection:
if an odd-incidence plaquette edge does not coincide with either
of the two temporal crossing links, the entire weighted ORIGINAL
three-plaquette/two-link Haar contribution vanishes. -/
theorem p4Q2PZ27_originalTripleTwoLinkHaar_zero_of_freeOddEdge
    (p q r : Plaq) (e f target : Link) (B : Cfg)
    (hOdd : Odd p q r target) (he : target ≠ e) (hf : target ≠ f) :
    J2 p q r e f B = 0 := by
  let obs : Cfg → ℝ := fun X =>
    ((χ p X * χ q X) * χ r X) *
      (E ((X e)⁻¹ * B e) * E ((X f)⁻¹ * B f))
  have hχ (v : Plaq) :
      Continuous (fun X : Cfg => χ v X) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H v
  have hE (d : Link) :
      Continuous (fun X : Cfg => E ((X d)⁻¹ * B d)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have hObs : Continuous obs :=
    ((((hχ p).mul (hχ q)).mul (hχ r)).mul
      ((hE e).mul (hE f)))
  have hOddObs (X : Cfg) : obs (Flip target X) = -obs X := by
    dsimp [obs]
    rw [p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target e he.symm X B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target f hf.symm X B,
      p4Q2PZ27_originalTripleCharacter_centerOdd H p q r target hOdd X]
    ring
  change (∫ X : Cfg, obs X ∂haar) = 0
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H target obs hObs hOddObs

/-- A nonadmissible genuine triple/two-link configuration has a
witnessing original spatial edge with odd incidence and no crossing
there. Its Haar integral is therefore rigorously zero. -/
theorem p4Q2PZ27_originalTripleTwoLinkHaar_zero_of_notAdmissible
    (p q r : Plaq) (e f : Link) (B : Cfg)
    (hNot : ¬ Admissible p q r e f) :
    J2 p q r e f B = 0 := by
  have hWitness :
      ∃ target : Link,
        target ≠ e ∧ target ≠ f ∧ Odd p q r target := by
    by_contra hNone
    apply hNot
    intro target he hf hOdd
    exact hNone ⟨target, he, hf, hOdd⟩
  obtain ⟨target, he, hf, hOdd⟩ := hWitness
  exact p4Q2PZ27_originalTripleTwoLinkHaar_zero_of_freeOddEdge
    H p q r e f target B hOdd he hf

/-- The remaining TRUE triple-plaquette Haar sector at two temporal
crossings has no support outside pairs covering ALL odd-incidence
spatial plaquette edges. No term was deleted without proving zero. -/
noncomputable def p4Q2PZ27_originalParityAdmissibleTripleTwoLinkHaar
    (p q r : Plaq) (B : Cfg) : ℝ := by
  classical
  exact ∑ e : Link, ∑ f : Link,
    if Admissible p q r e f then J2 p q r e f B else 0

local notation "Selected2" =>
  p4Q2PZ27_originalParityAdmissibleTripleTwoLinkHaar H

theorem p4Q2PZ27_originalTripleCrossSquare_onlyParityAdmissible
    (p q r : Plaq) (B : Cfg) :
    T3 p q r B = Selected2 p q r B := by
  classical
  rw [p4Q2PZ26_originalTriplePlaquetteCrossSquare_expand H p q r B]
  unfold p4Q2PZ27_originalParityAdmissibleTripleTwoLinkHaar
  apply Finset.sum_congr rfl
  intro e _he
  apply Finset.sum_congr rfl
  intro f _hf
  by_cases hAdm : Admissible p q r e f
  · simp [hAdm]
  · have hZero :=
      p4Q2PZ27_originalTripleTwoLinkHaar_zero_of_notAdmissible
        H p q r e f B hAdm
    simp [hAdm, hZero]

/-- The exact finite ORIGINAL SU(2) Haar sum that survives BOTH
PZ26's distinct-plaquette selection and PZ27's parity/edge
selection. Every term retains true intermediate spatial Wilson
plaquette interactions and the unmodified Haar. -/
noncomputable def p4Q2PZ27_originalDistinctParityAdmissibleHaar
    (B : Cfg) : ℝ := by
  classical
  exact ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq,
    if p ≠ q ∧ p ≠ r ∧ q ≠ r then
      Selected2 p q r B else 0

local notation "Surviving3" =>
  p4Q2PZ27_originalDistinctParityAdmissibleHaar H

/-- All discarded terms are zero by PZ26 genuine center parity
for repeated plaquettes, or PZ27 genuine odd-edge center parity
for uncovered odd-incidence links. -/
theorem p4Q2PZ27_originalDistinctTriple_eq_paritySelected
    (B : Cfg) :
    Distinct3 B = Surviving3 B := by
  classical
  unfold p4Q2PZ26_originalDistinctPlaquetteTripleHaar
    p4Q2PZ27_originalDistinctParityAdmissibleHaar
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hDistinct : p ≠ q ∧ p ≠ r ∧ q ≠ r
  · simpa only [if_pos hDistinct] using
      p4Q2PZ27_originalTripleCrossSquare_onlyParityAdmissible
        H p q r B
  · simp only [if_neg hDistinct]

/-- The only STILL UNSELECTED part of the original centered cubic
Wilson Haar is the true finite sum over three pairwise-distinct
plaquettes with all odd-incidence edges in the two actual temporal
crossing links. -/
theorem p4Q2PZ27_originalCenteredCube_onlyOddEdgeCovered
    (B : Cfg) :
    Z32 B = (1 / 8 : ℝ) * Surviving3 B := by
  rw [p4Q2PZ26_originalCenteredCube_onlyDistinctPlaquettes H B,
    p4Q2PZ27_originalDistinctTriple_eq_paritySelected H B]

/-- Source-preserving exact boundary-normalized PZ24 centered cubic
Ward defect. The right-hand side is the genuine SU(2) Haar sum,
NOT an independently sampled or postulated model. -/
theorem p4Q2PZ27_originalCenteredCubicDefect_onlyOddEdgeCovered
    (B : Cfg) :
    D32 B = (1 / 8 : ℝ) * (Surviving3 B - Surviving3 I) := by
  rw [p4Q2PZ26_originalCenteredCubeDefect_onlyDistinctPlaquettes H B,
    p4Q2PZ27_originalDistinctTriple_eq_paritySelected H B,
    p4Q2PZ27_originalDistinctTriple_eq_paritySelected H I]

end GenuineTriplePlaquetteOddEdgeSelection
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ27_originalCharacter_centerOdd_of_edge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ27_originalCharacter_centerEven_of_freeEdge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ27_originalTripleCharacter_centerOdd
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ27_originalTripleTwoLinkHaar_zero_of_freeOddEdge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ27_originalTripleTwoLinkHaar_zero_of_notAdmissible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ27_originalTripleCrossSquare_onlyParityAdmissible
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ27_originalDistinctTriple_eq_paritySelected
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ27_originalCenteredCube_onlyOddEdgeCovered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ27_originalCenteredCubicDefect_onlyOddEdgeCovered
