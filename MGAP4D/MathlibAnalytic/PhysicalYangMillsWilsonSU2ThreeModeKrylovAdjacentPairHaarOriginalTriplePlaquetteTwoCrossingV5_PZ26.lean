import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPlaquetteSupportV5_PZ25
import Mathlib.Tactic

/-!
# P4-Q2-PZ26 — true SU(2) centered cubic/two-crossing plaquette selection

On the UNMODIFIED finite-volume original Wilson SU(2) spatial Haar,
expand PZ24's remaining centered cubic × temporal crossing square
Z32(B) = ∫ h(X)^3 Cross(X,B)^2 dHaar(X)
into every ordered triple of original spatial plaquette characters.

The actual SU(2) single-link central flip shows that the Haar moment
of χ_p² χ_r times ANY TWO genuine temporal crossing energies is ZERO.
Indeed χ_p² is center-even at every original link, while a free edge
of the true four-edge plaquette r not occupied by either crossing
is center-odd. This gives zero for every triple of plaquettes with
ANY repeated plaquette label, including the fully diagonal case.

The entire true Haar Z32 and boundary defect D32 therefore contain
ONLY triples of pairwise DISTICT original plaquettes; all remaining
terms remain genuine, uncalculated SU(2) Haar integrals. All temporal
crossing-link coincidences are retained in the exact finite expansion.

No independent posterior, surrogate action, fabricated spectral row,
Dobrushin, rank3, physical witness, mass gap, new axiom, sorry, admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ26_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ26_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ26_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ26_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ26_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ26_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ26_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair
local instance p4Q2PZ26_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section GenuineTriplePlaquetteTwoCrossing

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Φ" => p4Q2PW2_originalAllPlaquetteRealTrace H
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H
local notation "Z32" => p4Q2PZ24_originalCenteredCubeCrossSquareHaar H
local notation "D32" => p4Q2PZ24_originalCenteredCubeSquareDefect H
local notation "I" => (fun _ : Link =>
  (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- The original weighted Haar moment of THREE genuine spatial
plaquette characters with TWO ordered crossing-link Wilson energies. -/
noncomputable def p4Q2PZ26_originalTriplePlaquetteTwoLinkHaar
    (p q r : Plaq) (e f : Link) (B : Cfg) : ℝ :=
  ∫ X : Cfg, ((χ p X * χ q X) * χ r X) *
    (E ((X e)⁻¹ * B e) * E ((X f)⁻¹ * B f)) ∂haar

/-- The unmodified centered spatial cube is expanded against the
complete original temporal two-crossing Wilson action. -/
noncomputable def p4Q2PZ26_originalTriplePlaquetteCrossSquareHaar
    (p q r : Plaq) (B : Cfg) : ℝ :=
  ∫ X : Cfg, ((χ p X * χ q X) * χ r X) *
    (Cross X B)^2 ∂haar

local notation "J2" => p4Q2PZ26_originalTriplePlaquetteTwoLinkHaar H
local notation "T3" => p4Q2PZ26_originalTriplePlaquetteCrossSquareHaar H

/-- Single repeated spatial plaquette χ_p² is center-even at
EVERY original spatial link; the third χ_r is odd at an unused
plaquette edge (four real edges versus two crossed links). -/
theorem p4Q2PZ26_originalSquarePlaquetteTwoLinkHaar_zero
    (p r : Plaq) (e f : Link) (B : Cfg) :
    (∫ X : Cfg, ((χ p X)^2 * χ r X) *
      (E ((X e)⁻¹ * B e) * E ((X f)⁻¹ * B f)) ∂haar) = 0 := by
  obtain ⟨target, hEdge, he, hf, _⟩ :=
    p4Q2PY3_originalPlaquette_freeLink_for_threeCrossings H r e f f
  let obs : Cfg → ℝ := fun X =>
    ((χ p X)^2 * χ r X) *
      (E ((X e)⁻¹ * B e) * E ((X f)⁻¹ * B f))
  have hχ (v : Plaq) :
      Continuous (fun X : Cfg => χ v X) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H v
  have hE (d : Link) :
      Continuous (fun X : Cfg => E ((X d)⁻¹ * B d)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have hObs : Continuous obs :=
    (((hχ p).pow 2).mul (hχ r)).mul ((hE e).mul (hE f))
  have hOdd (X : Cfg) : obs (Flip target X) = -obs X := by
    dsimp [obs]
    rw [p4Q2PY7_originalPlaquetteCharSquare_centerEven H p target X,
      p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_four
        H r target hEdge X,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target e he.symm X B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target f hf.symm X B]
    ring
  change (∫ X : Cfg, obs X ∂haar) = 0
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H target obs hObs hOdd

/-- Any coincidence among the THREE genuine plaquette labels
causes the two-link Haar moment to vanish, while crossing links
may coincide. -/
theorem p4Q2PZ26_originalTripleTwoLinkHaar_zero_of_repeated
    (p q r : Plaq) (e f : Link) (B : Cfg)
    (hRepeat : p = q ∨ p = r ∨ q = r) :
    J2 p q r e f B = 0 := by
  have hFirst (u v : Plaq) : J2 u u v e f B = 0 := by
    calc
      J2 u u v e f B =
        (∫ X : Cfg, ((χ u X)^2 * χ v X) *
          (E ((X e)⁻¹ * B e) * E ((X f)⁻¹ * B f)) ∂haar) := by
          unfold p4Q2PZ26_originalTriplePlaquetteTwoLinkHaar
          apply integral_congr_ae
          filter_upwards with X
          ring
      _ = 0 :=
        p4Q2PZ26_originalSquarePlaquetteTwoLinkHaar_zero H u v e f B
  rcases hRepeat with hPQ | hPR | hQR
  · subst q
    exact hFirst p r
  · subst r
    calc
      J2 p q p e f B = J2 p p q e f B := by
        unfold p4Q2PZ26_originalTriplePlaquetteTwoLinkHaar
        apply integral_congr_ae
        filter_upwards with X
        ring
      _ = 0 := hFirst p q
  · subst r
    calc
      J2 p q q e f B = J2 q q p e f B := by
        unfold p4Q2PZ26_originalTriplePlaquetteTwoLinkHaar
        apply integral_congr_ae
        filter_upwards with X
        ring
      _ = 0 := hFirst q p

/-- Exactly expand the original Haar two-crossing Wilson action
into ALL ordered pairs of physical spatial links. -/
theorem p4Q2PZ26_originalTriplePlaquetteCrossSquare_expand
    (p q r : Plaq) (B : Cfg) :
    T3 p q r B = ∑ e : Link, ∑ f : Link, J2 p q r e f B := by
  classical
  let T : Link → Cfg → ℝ := fun e X =>
    E ((X e)⁻¹ * B e)
  have hχ (v : Plaq) :
      Continuous (fun X : Cfg => χ v X) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H v
  have hT (e : Link) : Continuous (T e) := by
    change Continuous (fun X : Cfg => E ((X e)⁻¹ * B e))
    exact (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hEach (e f : Link) :
      Integrable (fun X : Cfg =>
        ((χ p X * χ q X) * χ r X) * (T e X * T f X)) haar :=
    ((((hχ p).mul (hχ q)).mul (hχ r)).mul
      ((hT e).mul (hT f))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hInner (e : Link) :
      Continuous (fun X : Cfg =>
        ∑ f : Link,
          ((χ p X * χ q X) * χ r X) * (T e X * T f X)) := by
    apply continuous_finset_sum
    intro f _hf
    exact (((hχ p).mul (hχ q)).mul (hχ r)).mul
      ((hT e).mul (hT f))
  have hDoubleIntegral :
      (∫ X : Cfg, ∑ e : Link, ∑ f : Link,
        ((χ p X * χ q X) * χ r X) * (T e X * T f X) ∂haar) =
      ∑ e : Link, ∑ f : Link,
        (∫ X : Cfg,
          ((χ p X * χ q X) * χ r X) * (T e X * T f X) ∂haar) := by
    rw [integral_finset_sum _ (fun e _ =>
      (hInner e).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro e _he
    rw [integral_finset_sum _ (fun f _ => hEach e f)]
  have hSquare (X : Cfg) :
      (∑ e : Link, T e X)^2 =
        ∑ e : Link, ∑ f : Link, T e X * T f X := by
    calc
      (∑ e : Link, T e X)^2 =
          (∑ e : Link, T e X) * (∑ f : Link, T f X) := by ring
      _ = ∑ e : Link, ∑ f : Link, T e X * T f X := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _he
        rw [Finset.mul_sum]
  have hPoint (X : Cfg) :
      ((χ p X * χ q X) * χ r X) * (Cross X B)^2 =
        ∑ e : Link, ∑ f : Link,
          ((χ p X * χ q X) * χ r X) * (T e X * T f X) := by
    rw [p4Q2PW_originalCrossing_eq_finsetSum H X B, hSquare X,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _he
    rw [Finset.mul_sum]
  change (∫ X : Cfg,
    ((χ p X * χ q X) * χ r X) * (Cross X B)^2 ∂haar) = _
  calc
    (∫ X : Cfg,
      ((χ p X * χ q X) * χ r X) * (Cross X B)^2 ∂haar) =
      (∫ X : Cfg, ∑ e : Link, ∑ f : Link,
        ((χ p X * χ q X) * χ r X) * (T e X * T f X) ∂haar) := by
      apply integral_congr_ae
      filter_upwards with X
      exact hPoint X
    _ = ∑ e : Link, ∑ f : Link, J2 p q r e f B := by
      rw [hDoubleIntegral]
      rfl

/-- All ORIGINAL χ_p χ_q χ_r Cross² Haar sectors with any repeated
plaquette vanish, independently of the temporal right boundary. -/
theorem p4Q2PZ26_originalTriplePlaquetteCrossSquare_zero_of_repeated
    (p q r : Plaq) (B : Cfg)
    (hRepeat : p = q ∨ p = r ∨ q = r) :
    T3 p q r B = 0 := by
  rw [p4Q2PZ26_originalTriplePlaquetteCrossSquare_expand H p q r B]
  apply Finset.sum_eq_zero
  intro e _he
  apply Finset.sum_eq_zero
  intro f _hf
  exact p4Q2PZ26_originalTripleTwoLinkHaar_zero_of_repeated
    H p q r e f B hRepeat

/-- The original centered SU(2) spatial cube is precisely the
TRIPLE Haar plaquette sum, including all repeated indices initially. -/
theorem p4Q2PZ26_originalPlaquetteTraceCube_Haar_tripleSum
    (B : Cfg) :
    (∫ X : Cfg, (Φ X)^3 * (Cross X B)^2 ∂haar) =
      ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq, T3 p q r B := by
  classical
  have hPair : Continuous (fun X : Cfg => (X,B)) :=
    continuous_id.prodMk continuous_const
  have hCross : Continuous (fun X : Cfg => Cross X B) := by
    have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hc
  have hχ (v : Plaq) :
      Continuous (fun X : Cfg => χ v X) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H v
  have hEach (p q r : Plaq) :
      Integrable (fun X : Cfg =>
        ((χ p X * χ q X) * χ r X) * (Cross X B)^2) haar :=
    ((((hχ p).mul (hχ q)).mul (hχ r)).mul
      (hCross.pow 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hInner (p q : Plaq) :
      Continuous (fun X : Cfg =>
        ∑ r : Plaq,
          ((χ p X * χ q X) * χ r X) * (Cross X B)^2) := by
    apply continuous_finset_sum
    intro r _hr
    exact (((hχ p).mul (hχ q)).mul (hχ r)).mul (hCross.pow 2)
  have hMiddle (p : Plaq) :
      Continuous (fun X : Cfg =>
        ∑ q : Plaq, ∑ r : Plaq,
          ((χ p X * χ q X) * χ r X) * (Cross X B)^2) := by
    apply continuous_finset_sum
    intro q _hq
    exact hInner p q
  have hSumIntegral :
      (∫ X : Cfg, ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq,
        ((χ p X * χ q X) * χ r X) * (Cross X B)^2 ∂haar) =
      ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq,
        (∫ X : Cfg,
          ((χ p X * χ q X) * χ r X) * (Cross X B)^2 ∂haar) := by
    rw [integral_finset_sum _ (fun p _ =>
      (hMiddle p).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [integral_finset_sum _ (fun q _ =>
      (hInner p q).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [integral_finset_sum _ (fun r _ => hEach p q r)]
  have hSquare (X : Cfg) :
      (∑ p : Plaq, χ p X) * (∑ q : Plaq, χ q X) =
        ∑ p : Plaq, ∑ q : Plaq, χ p X * χ q X := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [Finset.mul_sum]
  have hCube (X : Cfg) :
      (∑ p : Plaq, χ p X)^3 =
        ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq,
          (χ p X * χ q X) * χ r X := by
    calc
      (∑ p : Plaq, χ p X)^3 =
        ((∑ p : Plaq, χ p X) * (∑ q : Plaq, χ q X)) *
          (∑ r : Plaq, χ r X) := by ring
      _ = (∑ p : Plaq, ∑ q : Plaq, χ p X * χ q X) *
          (∑ r : Plaq, χ r X) := by rw [hSquare]
      _ = ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq,
          (χ p X * χ q X) * χ r X := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _hp
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q _hq
        rw [Finset.mul_sum]
  have hPoint (X : Cfg) :
      (Φ X)^3 * (Cross X B)^2 =
        ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq,
          ((χ p X * χ q X) * χ r X) * (Cross X B)^2 := by
    calc
      (Φ X)^3 * (Cross X B)^2 =
          (∑ p : Plaq, χ p X)^3 * (Cross X B)^2 := by
          unfold p4Q2PW2_originalAllPlaquetteRealTrace
          rfl
      _ = (∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq,
          (χ p X * χ q X) * χ r X) * (Cross X B)^2 := by
          rw [hCube]
      _ = ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq,
          ((χ p X * χ q X) * χ r X) * (Cross X B)^2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p _hp
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro q _hq
          rw [Finset.sum_mul]
  calc
    (∫ X : Cfg, (Φ X)^3 * (Cross X B)^2 ∂haar) =
      (∫ X : Cfg, ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq,
        ((χ p X * χ q X) * χ r X) * (Cross X B)^2 ∂haar) := by
        apply integral_congr_ae
        filter_upwards with X
        exact hPoint X
    _ = ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq, T3 p q r B := by
        rw [hSumIntegral]
        rfl

/-- Genuine centered Wilson cubic Haar has the EXACT 1/8 factor
from h=Φ/2; no approximation, gauge fixing or new measure. -/
theorem p4Q2PZ26_originalCenteredCube_tripleHaar
    (B : Cfg) :
    Z32 B = (1 / 8 : ℝ) *
      (∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq, T3 p q r B) := by
  calc
    Z32 B = (∫ X : Cfg,
      (1 / 8 : ℝ) * ((Φ X)^3 * (Cross X B)^2) ∂haar) := by
        unfold p4Q2PZ24_originalCenteredCubeCrossSquareHaar
        apply integral_congr_ae
        filter_upwards with X
        rw [p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H X]
        ring
    _ = (1 / 8 : ℝ) *
      (∫ X : Cfg, (Φ X)^3 * (Cross X B)^2 ∂haar) := by
        rw [integral_const_mul]
    _ = (1 / 8 : ℝ) *
      (∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq, T3 p q r B) := by
        rw [p4Q2PZ26_originalPlaquetteTraceCube_Haar_tripleSum H B]

/-- The surviving TRUE three-plaquette two-crossing Haar sum
contains only three distinct original spatial plaquettes. -/
noncomputable def p4Q2PZ26_originalDistinctPlaquetteTripleHaar
    (B : Cfg) : ℝ := by
  classical
  exact ∑ p : Plaq, ∑ q : Plaq, ∑ r : Plaq,
    if p ≠ q ∧ p ≠ r ∧ q ≠ r then T3 p q r B else 0

local notation "Distinct3" => p4Q2PZ26_originalDistinctPlaquetteTripleHaar H

/-- All repeated plaquette contributions were proved zero using
original SU(2) center flips, not discarded by an assumption. -/
theorem p4Q2PZ26_originalCenteredCube_onlyDistinctPlaquettes
    (B : Cfg) :
    Z32 B = (1 / 8 : ℝ) * Distinct3 B := by
  classical
  rw [p4Q2PZ26_originalCenteredCube_tripleHaar H B]
  unfold p4Q2PZ26_originalDistinctPlaquetteTripleHaar
  apply congrArg (fun t : ℝ => (1 / 8 : ℝ) * t)
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hDistinct : p ≠ q ∧ p ≠ r ∧ q ≠ r
  · simp [hDistinct]
  · have hRepeat : p = q ∨ p = r ∨ q = r := by
      by_contra hNone
      have hpq : p ≠ q := by
        intro hpq
        exact hNone (Or.inl hpq)
      have hpr : p ≠ r := by
        intro hpr
        exact hNone (Or.inr (Or.inl hpr))
      have hqr : q ≠ r := by
        intro hqr
        exact hNone (Or.inr (Or.inr hqr))
      exact hDistinct ⟨hpq, hpr, hqr⟩
    have hZero := p4Q2PZ26_originalTriplePlaquetteCrossSquare_zero_of_repeated
      H p q r B hRepeat
    simp [hDistinct, hZero]

/-- The true PZ24 centered cubic boundary Ward obstruction has
ONLY pairwise distinct original plaquette triples. Every coefficient
is the unchanged SU(2) Haar integral from the Wilson action. -/
theorem p4Q2PZ26_originalCenteredCubeDefect_onlyDistinctPlaquettes
    (B : Cfg) :
    D32 B = (1 / 8 : ℝ) * (Distinct3 B - Distinct3 I) := by
  unfold p4Q2PZ24_originalCenteredCubeSquareDefect
  rw [p4Q2PZ26_originalCenteredCube_onlyDistinctPlaquettes H B,
    p4Q2PZ26_originalCenteredCube_onlyDistinctPlaquettes H I]
  ring

end GenuineTriplePlaquetteTwoCrossing
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ26_originalSquarePlaquetteTwoLinkHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ26_originalTripleTwoLinkHaar_zero_of_repeated
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ26_originalTriplePlaquetteCrossSquare_expand
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ26_originalTriplePlaquetteCrossSquare_zero_of_repeated
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ26_originalPlaquetteTraceCube_Haar_tripleSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ26_originalCenteredCube_tripleHaar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ26_originalCenteredCube_onlyDistinctPlaquettes
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ26_originalCenteredCubeDefect_onlyDistinctPlaquettes
