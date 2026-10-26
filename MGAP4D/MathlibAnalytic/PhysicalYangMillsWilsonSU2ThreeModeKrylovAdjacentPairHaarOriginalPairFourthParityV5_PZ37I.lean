import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalQuadraticPlaquetteFourthV5_PZ37I
import Mathlib.Tactic

/-!
# P4-Q2-PZ37I — exact original two-plaquette/four-crossing parity selection

Expand the original quadratic spatial-plaquette trace source K4 into
ordered pairs of genuine four-edge SU(2) plaquettes and ALL ordered
four-tuples of true temporal crossing links. The integration uses only
the original normalized full product Haar, without independence
assumptions or replacement posteriors.

A single true SU(2) centre flip kills a term if a link has odd incidence
in the original plaquette pair but is absent from the four selected
temporal insertions. Therefore only four-link tuples covering all
odd-incidence links remain, including diagonal pairs, repeated crossing
links, and the H=0 period-two case. This is only a support selection,
not an assumption that the surviving Haar integrals vanish.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37I_parity_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37I_parity_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37I_parity_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37I_parity_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37I_parity_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37I_parity_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37I_parity_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section PairParitySelection
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H
local notation "On" => p4Q2PZ27_originalEdgeOnPlaquette H
local notation "Pair4" => p4Q2PZ37I_originalPairTraceFourth H
local notation "K4" => p4Q2PZ37I_originalQuadraticTraceFourth H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "W" => p4Q2PZ37B_originalBoundaryWedge H

/-- Exactly one of two genuine original spatial plaquettes uses the link. -/
def p4Q2PZ37I_originalPairOddEdge (p q : Plaq) (target : Link) : Prop :=
  (On p target ∧ ¬On q target) ∨ (¬On p target ∧ On q target)
local notation "Odd" => p4Q2PZ37I_originalPairOddEdge H

/-- The real original pair trace is centre-odd on every edge of the
SYMMETRIC DIFFERENCE of its physical four-link plaquette boundaries. -/
theorem p4Q2PZ37I_originalPairCharacter_odd
    (p q : Plaq) (target : Link) (hOdd : Odd p q target)
    (X : Cfg) :
    χ p (Flip target X)*χ q (Flip target X) =
      -(χ p X*χ q X) := by
  rcases hOdd with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · rw [p4Q2PZ27_originalCharacter_centerOdd_of_edge H p target X hp,
      p4Q2PZ27_originalCharacter_centerEven_of_freeEdge H q target X hq]
    ring
  · rw [p4Q2PZ27_originalCharacter_centerEven_of_freeEdge H p target X hp,
      p4Q2PZ27_originalCharacter_centerOdd_of_edge H q target X hq]
    ring

/-- Pair-weighted genuine four-crossing original Haar term. No links are
assumed distinct; all coincidences remain as literal integrands. -/
noncomputable def p4Q2PZ37I_originalPairFourthTerm
    (p q : Plaq) (e f g k : Link) (B : Cfg) : ℝ :=
  ∫ X : Cfg, (χ p X*χ q X)*
    (E ((X e)⁻¹*B e)*E ((X f)⁻¹*B f)*
      E ((X g)⁻¹*B g)*E ((X k)⁻¹*B k)) ∂haar
local notation "Term4" => p4Q2PZ37I_originalPairFourthTerm H

/-- Only quadruples covering every true odd-incidence spatial edge can
survive the full original Haar integration. -/
def p4Q2PZ37I_originalQuadCoversOddPair
    (p q : Plaq) (e f g k : Link) : Prop :=
  ∀ target : Link, Odd p q target →
    (target = e ∨ target = f ∨ target = g ∨ target = k)
local notation "Covers" => p4Q2PZ37I_originalQuadCoversOddPair H

/-- Original centre-flip cancellation of any quadruple missing a
TRUE odd-incidence spatial plaquette-pair edge. -/
theorem p4Q2PZ37I_originalPairFourthTerm_zero_of_freeOddEdge
    (p q : Plaq) (e f g k target : Link) (B : Cfg)
    (hOdd : Odd p q target)
    (he : target ≠ e) (hf : target ≠ f)
    (hg : target ≠ g) (hk : target ≠ k) :
    Term4 p q e f g k B = 0 := by
  let obs : Cfg → ℝ := fun X =>
    (χ p X*χ q X)*
      (E ((X e)⁻¹*B e)*E ((X f)⁻¹*B f)*
        E ((X g)⁻¹*B g)*E ((X k)⁻¹*B k))
  have hχ (v : Plaq) : Continuous (fun X : Cfg => χ v X) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H v
  have hE (d : Link) : Continuous (fun X : Cfg => E ((X d)⁻¹*B d)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have hobs : Continuous obs :=
    ((hχ p).mul (hχ q)).mul
      ((((hE e).mul (hE f)).mul (hE g)).mul (hE k))
  have hoddobs (X : Cfg) : obs (Flip target X) = -obs X := by
    dsimp [obs]
    rw [p4Q2PZ37I_originalPairCharacter_odd H p q target hOdd X,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other H target e he.symm X B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other H target f hf.symm X B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other H target g hg.symm X B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other H target k hk.symm X B]
    ring
  change (∫ X : Cfg, obs X ∂haar) = 0
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H target obs hobs hoddobs

/-- The exact logical complement of the necessary parity-support
condition has a real unused odd-incidence spatial link. -/
theorem p4Q2PZ37I_originalPairFourthTerm_zero_of_notCovered
    (p q : Plaq) (e f g k : Link) (B : Cfg)
    (hNot : ¬Covers p q e f g k) :
    Term4 p q e f g k B = 0 := by
  have hWitness : ∃ target : Link,
      Odd p q target ∧
      target ≠ e ∧ target ≠ f ∧ target ≠ g ∧ target ≠ k := by
    by_contra hNo
    apply hNot
    intro target hOdd
    by_contra hNone
    simp only [not_or] at hNone
    exact hNo ⟨target,hOdd,hNone.1,hNone.2.1,hNone.2.2.1,hNone.2.2.2⟩
  obtain ⟨target,hOdd,he,hf,hg,hk⟩ := hWitness
  exact p4Q2PZ37I_originalPairFourthTerm_zero_of_freeOddEdge
    H p q e f g k target B hOdd he hf hg hk

/-- The complete original pair-weighted fourth crossing is the literal
ordered FOUR-link Haar sum; all repeated-link terms are retained. -/
theorem p4Q2PZ37I_originalPairFourth_quadrupleExpansion
    (p q : Plaq) (B : Cfg) :
    Pair4 p q B =
      ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
        Term4 p q e f g k B := by
  classical
  let T : Link → Cfg → ℝ := fun e X => E ((X e)⁻¹*B e)
  have hχ : Continuous (fun X : Cfg => χ p X*χ q X) :=
    (p4Q2PV_originalPlaquetteRealCharacter_continuous H p).mul
      (p4Q2PV_originalPlaquetteRealCharacter_continuous H q)
  have hT (e : Link) : Continuous (T e) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hEach (e f g k : Link) :
      Integrable (fun X : Cfg =>
        (χ p X*χ q X)*(T e X*T f X*T g X*T k X)) haar :=
    ((hχ.mul ((((hT e).mul (hT f)).mul (hT g)).mul (hT k))))
      .integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hInner (e f g : Link) :
      Continuous (fun X : Cfg =>
        ∑ k : Link, (χ p X*χ q X)*(T e X*T f X*T g X*T k X)) := by
    apply continuous_finset_sum
    intro k _hk
    exact hχ.mul ((((hT e).mul (hT f)).mul (hT g)).mul (hT k))
  have hMiddle (e f : Link) :
      Continuous (fun X : Cfg =>
        ∑ g : Link, ∑ k : Link,
          (χ p X*χ q X)*(T e X*T f X*T g X*T k X)) := by
    apply continuous_finset_sum
    intro g _hg
    exact hInner e f g
  have hOuter (e : Link) :
      Continuous (fun X : Cfg =>
        ∑ f : Link, ∑ g : Link, ∑ k : Link,
          (χ p X*χ q X)*(T e X*T f X*T g X*T k X)) := by
    apply continuous_finset_sum
    intro f _hf
    exact hMiddle e f
  have hIntegral :
      (∫ X : Cfg,
        ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
          (χ p X*χ q X)*(T e X*T f X*T g X*T k X) ∂haar) =
      ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
          (∫ X : Cfg,
            (χ p X*χ q X)*(T e X*T f X*T g X*T k X) ∂haar) := by
    rw [integral_finset_sum _ (fun e _ =>
      (hOuter e).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro e _he
    rw [integral_finset_sum _ (fun f _ =>
      (hMiddle e f).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro f _hf
    rw [integral_finset_sum _ (fun g _ =>
      (hInner e f g).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro g _hg
    rw [integral_finset_sum _ (fun k _ => hEach e f g k)]
  have hSquare (X : Cfg) :
      (∑ e : Link, T e X)*(∑ f : Link, T f X) =
      ∑ e : Link, ∑ f : Link, T e X*T f X := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _he
    rw [Finset.mul_sum]
  have hCube (X : Cfg) :
      (∑ e : Link, T e X)^3 =
      ∑ e : Link, ∑ f : Link, ∑ g : Link, T e X*T f X*T g X := by
    calc
      (∑ e : Link, T e X)^3 =
          ((∑ e : Link, T e X)*(∑ f : Link, T f X))*
            (∑ g : Link, T g X) := by ring
      _ = ∑ e : Link, ∑ f : Link, ∑ g : Link,
          T e X*T f X*T g X := by
        rw [hSquare X, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _he
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro f _hf
        rw [Finset.mul_sum]
  have hFourth (X : Cfg) :
      (∑ e : Link, T e X)^4 =
      ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
        T e X*T f X*T g X*T k X := by
    calc
      (∑ e : Link, T e X)^4 =
          (∑ e : Link, T e X)^3*(∑ k : Link, T k X) := by ring
      _ = (∑ e : Link, ∑ f : Link, ∑ g : Link,
          T e X*T f X*T g X)*(∑ k : Link, T k X) := by rw [hCube X]
      _ = ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
          T e X*T f X*T g X*T k X := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _he
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro f _hf
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _hg
        rw [Finset.mul_sum]
  have hPoint (X : Cfg) :
      (χ p X*χ q X)*(∑ e : Link, T e X)^4 =
      ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
        (χ p X*χ q X)*(T e X*T f X*T g X*T k X) := by
    rw [hFourth X, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _he
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _hf
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _hg
    rw [Finset.mul_sum]
  change (∫ X : Cfg, (χ p X*χ q X)*(Cross X B)^4 ∂haar) = _
  calc
    (∫ X : Cfg, (χ p X*χ q X)*(Cross X B)^4 ∂haar) =
      ∫ X : Cfg,
        ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
          (χ p X*χ q X)*(T e X*T f X*T g X*T k X) ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        rw [p4Q2PW_originalCrossing_eq_finsetSum H X B]
        have hUniv :
            (@Finset.univ Link (p4Q2PW_nativeFintype H)) =
              (Finset.univ : Finset Link) := by
          ext e
          simp
        simpa only [hUniv, T] using hPoint X
    _ = ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
      (∫ X : Cfg,
        (χ p X*χ q X)*(T e X*T f X*T g X*T k X) ∂haar) := hIntegral
    _ = ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
      Term4 p q e f g k B := rfl

/-- Only truly parity-supported original plaquette pairs and four-link
crossings are retained; all excluded terms have proven Haar zero. -/
noncomputable def p4Q2PZ37I_originalPairFourth_oddSelected
    (p q : Plaq) (B : Cfg) : ℝ := by
  classical
  exact ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
    if Covers p q e f g k then Term4 p q e f g k B else 0
local notation "Selected" => p4Q2PZ37I_originalPairFourth_oddSelected H

/-- Exact original Haar support selection for each original
pair and ALL quadruples, including repeated links at period two. -/
theorem p4Q2PZ37I_originalPairFourth_onlyOddCovered
    (p q : Plaq) (B : Cfg) :
    Pair4 p q B = Selected p q B := by
  classical
  rw [p4Q2PZ37I_originalPairFourth_quadrupleExpansion H p q B]
  unfold p4Q2PZ37I_originalPairFourth_oddSelected
  apply Finset.sum_congr rfl
  intro e _he
  apply Finset.sum_congr rfl
  intro f _hf
  apply Finset.sum_congr rfl
  intro g _hg
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases h : Covers p q e f g k
  · simp [h]
  · simp [h, p4Q2PZ37I_originalPairFourthTerm_zero_of_notCovered
      H p q e f g k B h]

/-- All original double-plaquette fourth-crossing Haar terms localize
to the genuine odd-incidence four-link support, with no discarded
nonzero terms, even at the minimal periodic torus. -/
theorem p4Q2PZ37I_originalQuadraticTraceFourth_onlyOddCovered
    (B : Cfg) :
    K4 B = ∑ p : Plaq, ∑ q : Plaq, Selected p q B := by
  classical
  rw [p4Q2PZ37I_originalQuadraticTraceFourth_pairSum H B]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  exact p4Q2PZ37I_originalPairFourth_onlyOddCovered H p q B

/-- Exact physical seventh Taylor jet on the fully original parity-selected
finite six-index Haar sum; no surviving integral is assumed zero. -/
theorem p4Q2PZ37I_originalPhysicalSeventhJet_oddPairSelected
    (A B C : Cfg) :
    p4Q2PZ37B_originalPhysicalSeventhCoefficient H A B C =
      -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512 -
        W w (fun D : Cfg => ∑ p : Plaq, ∑ q : Plaq, Selected p q D) A B C /64 := by
  rw [p4Q2PZ37I_originalPhysicalSeventhJet_pairTraceFourth H A B C]
  unfold p4Q2PZ37B_originalBoundaryWedge
  dsimp only
  rw [p4Q2PZ37I_originalQuadraticTraceFourth_onlyOddCovered H A,
    p4Q2PZ37I_originalQuadraticTraceFourth_onlyOddCovered H B,
    p4Q2PZ37I_originalQuadraticTraceFourth_onlyOddCovered H C]

end PairParitySelection
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalPairCharacter_odd
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalPairFourthTerm_zero_of_freeOddEdge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalPairFourthTerm_zero_of_notCovered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalPairFourth_quadrupleExpansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalPairFourth_onlyOddCovered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalQuadraticTraceFourth_onlyOddCovered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37I_originalPhysicalSeventhJet_oddPairSelected
