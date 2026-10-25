import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCenteredHighVandermondeV5_PZ24
import Mathlib.Tactic

/-!
# P4-Q2-PZ25 — ORIGINAL SU(2) plaquette and four-link Haar selection

Keep exactly the finite-volume original SU(2) Wilson action, the
intermediate original spatial plaquettes, the original SU(2) spatial
Haar product and both physical posterior sectors.

PZ24 isolated the centered first spatial Wilson action times the
FOURTH power of the true temporal Wilson crossing as Z14. Here:
1. expand the genuine plaquette-character weighted fourth crossing
   into all ordered quadruples of original spatial links, including
   repeated-link indices;
2. prove using the genuine SU(2) single-link central -I flip that
   every term is ZERO if a spatial plaquette edge is absent from its
   four temporal crossing links;
3. express Z14 and its boundary-normalized original Ward defect
   EXACTLY as the finite selected sum over quadruples covering all
   four true spatial plaquette edges.

The selected quadruple sum is not assumed nonzero; no amplitude,
physical mass gap, rank-three witness, independent posterior,
Dobrushin shortcut, new axiom, sorry, or admit is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ25_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ25_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ25_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ25_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ25_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ25_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ25_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair
local instance p4Q2PZ25_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalFourthCrossingPlaquetteSupport
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
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H
local notation "Z14" => p4Q2PZ24_originalCenteredFirstCrossFourthHaar H
local notation "D14" => p4Q2PZ24_originalCenteredFirstFourthDefect H
local notation "I" => (fun _ : Link =>
  (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- Exact ORIGINAL Haar term, four ordered temporal crossing energies
with the actual SU(2) spatial plaquette character. -/
noncomputable def p4Q2PZ25_originalFourCrossingPlaquetteTerm
    (p : Plaq) (e f g k : Link) (B : Cfg) : ℝ :=
  ∫ A : Cfg, χ p A *
    (E ((A e)⁻¹ * B e) *
      E ((A f)⁻¹ * B f) *
      E ((A g)⁻¹ * B g) *
      E ((A k)⁻¹ * B k)) ∂haar

local notation "Term4" => p4Q2PZ25_originalFourCrossingPlaquetteTerm H

/-- Real plaquette character Haar moment against the COMPLETE fourth
power of the actual temporal crossing action. -/
noncomputable def p4Q2PZ25_originalPlaquetteFourthCrossingHaar
    (p : Plaq) (B : Cfg) : ℝ :=
  ∫ A : Cfg, χ p A * (Cross A B)^4 ∂haar

local notation "Row4" => p4Q2PZ25_originalPlaquetteFourthCrossingHaar H

/-- Every one of the FOUR genuine plaquette edges must be covered
by the ordered quadruple of temporal crossing links. The definition
makes no independent-link or gauge-fixing assumption. -/
def p4Q2PZ25_originalFourthCrossingCoversPlaquette
    (p : Plaq) (e f g k : Link) : Prop :=
  ∀ target : Link,
    (target = e0 p ∨ target = e1 p ∨
      target = e2 p ∨ target = e3 p) →
    (target = e ∨ target = f ∨ target = g ∨ target = k)

local notation "Covers" => p4Q2PZ25_originalFourthCrossingCoversPlaquette H

/-- A four-link Haar integrand missing ANY plaquette edge is center
ODD under the unchanged genuine spatial SU(2) Haar measure. -/
theorem p4Q2PZ25_originalFourCrossingTerm_zero_of_unusedEdge
    (p : Plaq) (e f g k target : Link) (B : Cfg)
    (hEdge : target = e0 p ∨ target = e1 p ∨
      target = e2 p ∨ target = e3 p)
    (he : target ≠ e) (hf : target ≠ f)
    (hg : target ≠ g) (hk : target ≠ k) :
    Term4 p e f g k B = 0 := by
  let obs : Cfg → ℝ := fun A =>
    χ p A *
      (E ((A e)⁻¹ * B e) *
        E ((A f)⁻¹ * B f) *
        E ((A g)⁻¹ * B g) *
        E ((A k)⁻¹ * B k))
  have hT (d : Link) :
      Continuous (fun A : Cfg => E ((A d)⁻¹ * B d)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have hObs : Continuous obs :=
    (p4Q2PV_originalPlaquetteRealCharacter_continuous H p).mul
      ((((hT e).mul (hT f)).mul (hT g)).mul (hT k))
  have hOdd (A : Cfg) : obs (Flip target A) = -obs A := by
    change
      χ p (Flip target A) *
        (E (((Flip target A) e)⁻¹ * B e) *
          E (((Flip target A) f)⁻¹ * B f) *
          E (((Flip target A) g)⁻¹ * B g) *
          E (((Flip target A) k)⁻¹ * B k)) =
      -(χ p A *
        (E ((A e)⁻¹ * B e) *
          E ((A f)⁻¹ * B f) *
          E ((A g)⁻¹ * B g) *
          E ((A k)⁻¹ * B k)))
    rw [p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_four
        H p target hEdge A,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target e he.symm A B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target f hf.symm A B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target g hg.symm A B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target k hk.symm A B]
    ring
  change (∫ A : Cfg, obs A ∂haar) = 0
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H target obs hObs hOdd

/-- Equivalently, ALL non-covering quadruple moments vanish by
original SU(2) center parity. This is a true zero theorem,
not a vanishing assertion about the surviving quadruples. -/
theorem p4Q2PZ25_originalFourCrossingTerm_zero_of_notCovered
    (p : Plaq) (e f g k : Link) (B : Cfg)
    (hNot : ¬ Covers p e f g k) :
    Term4 p e f g k B = 0 := by
  have hFree : ∃ target : Link,
      (target = e0 p ∨ target = e1 p ∨
        target = e2 p ∨ target = e3 p) ∧
      target ≠ e ∧ target ≠ f ∧
      target ≠ g ∧ target ≠ k := by
    by_contra hNo
    apply hNot
    intro target hEdge
    by_contra hNone
    simp only [not_or] at hNone
    exact hNo ⟨target, hEdge, hNone.1, hNone.2.1,
      hNone.2.2.1, hNone.2.2.2⟩
  obtain ⟨target, hEdge, he, hf, hg, hk⟩ := hFree
  exact p4Q2PZ25_originalFourCrossingTerm_zero_of_unusedEdge
    H p e f g k target B hEdge he hf hg hk

/-- The complete fourth temporal SU(2) Wilson crossing against a
plaquette is EXACTLY the ordered quadruple Haar sum, including all
coincident link indices. Nothing has been discarded yet. -/
theorem p4Q2PZ25_originalPlaquetteFourthCrossing_expand
    (p : Plaq) (B : Cfg) :
    Row4 p B =
      ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
        Term4 p e f g k B := by
  classical
  let T : Link → Cfg → ℝ := fun e A => E ((A e)⁻¹ * B e)
  have hχ : Continuous (fun A : Cfg => χ p A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hT (e : Link) : Continuous (T e) := by
    change Continuous (fun A : Cfg => E ((A e)⁻¹ * B e))
    exact (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hEach (e f g k : Link) :
      Integrable (fun A : Cfg =>
        χ p A * (T e A*T f A*T g A*T k A)) haar :=
    (hχ.mul ((((hT e).mul (hT f)).mul (hT g)).mul
      (hT k))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hInner (e f g : Link) :
      Continuous (fun A : Cfg =>
        ∑ k : Link, χ p A*(T e A*T f A*T g A*T k A)) := by
    apply continuous_finset_sum
    intro k _hk
    exact hχ.mul ((((hT e).mul (hT f)).mul (hT g)).mul (hT k))
  have hMiddle (e f : Link) :
      Continuous (fun A : Cfg =>
        ∑ g : Link, ∑ k : Link,
          χ p A*(T e A*T f A*T g A*T k A)) := by
    apply continuous_finset_sum
    intro g _hg
    exact hInner e f g
  have hOuter (e : Link) :
      Continuous (fun A : Cfg =>
        ∑ f : Link, ∑ g : Link, ∑ k : Link,
          χ p A*(T e A*T f A*T g A*T k A)) := by
    apply continuous_finset_sum
    intro f _hf
    exact hMiddle e f
  have hIntegral :
      (∫ A : Cfg,
        ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
          χ p A*(T e A*T f A*T g A*T k A) ∂haar) =
        ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
          (∫ A : Cfg,
            χ p A*(T e A*T f A*T g A*T k A) ∂haar) := by
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
  have hSquare (A : Cfg) :
      (∑ e : Link, T e A)*(∑ f : Link, T f A) =
        ∑ e : Link, ∑ f : Link, T e A*T f A := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _he
    rw [Finset.mul_sum]
  have hCube (A : Cfg) :
      (∑ e : Link, T e A)^3 =
        ∑ e : Link, ∑ f : Link, ∑ g : Link,
          T e A*T f A*T g A := by
    calc
      (∑ e : Link, T e A)^3 =
          ((∑ e : Link, T e A)*(∑ f : Link, T f A)) *
            (∑ g : Link, T g A) := by ring
      _ = ∑ e : Link, ∑ f : Link, ∑ g : Link,
          T e A*T f A*T g A := by
        rw [hSquare, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _he
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro f _hf
        rw [Finset.mul_sum]
  have hFourth (A : Cfg) :
      (∑ e : Link, T e A)^4 =
        ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
          T e A*T f A*T g A*T k A := by
    calc
      (∑ e : Link, T e A)^4 =
          (∑ e : Link, T e A)^3 * (∑ k : Link, T k A) := by ring
      _ = (∑ e : Link, ∑ f : Link, ∑ g : Link,
          T e A*T f A*T g A) * (∑ k : Link, T k A) := by rw [hCube]
      _ = ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
          T e A*T f A*T g A*T k A := by
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
  have hPoint (A : Cfg) :
      χ p A*(∑ e : Link, T e A)^4 =
        ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
          χ p A*(T e A*T f A*T g A*T k A) := by
    rw [hFourth, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _he
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _hf
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _hg
    rw [Finset.mul_sum]
  change (∫ A : Cfg, χ p A*(Cross A B)^4 ∂haar) = _
  calc
    (∫ A : Cfg, χ p A*(Cross A B)^4 ∂haar) =
      ∫ A : Cfg,
        ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
          χ p A*(T e A*T f A*T g A*T k A) ∂haar := by
        apply integral_congr_ae
        filter_upwards with A
        rw [p4Q2PW_originalCrossing_eq_finsetSum H A B]
        exact hPoint A
    _ = ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
          (∫ A : Cfg, χ p A*(T e A*T f A*T g A*T k A) ∂haar) :=
      hIntegral

/-- Genuine selected fourth crossing: retain only ordered four-link
tuples that cover all four original plaquette edges. -/
noncomputable def p4Q2PZ25_originalCoveredPlaquetteFourthHaar
    (p : Plaq) (B : Cfg) : ℝ :=
  ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
    if Covers p e f g k then Term4 p e f g k B else 0

local notation "Covered4" => p4Q2PZ25_originalCoveredPlaquetteFourthHaar H

/-- Exact complete Haar support selection, not merely a formal
decomposition: ALL non-covering fourth-crossing contributions vanish. -/
theorem p4Q2PZ25_originalPlaquetteFourthCrossing_onlyCovered
    (p : Plaq) (B : Cfg) :
    Row4 p B = Covered4 p B := by
  classical
  rw [p4Q2PZ25_originalPlaquetteFourthCrossing_expand H p B]
  unfold p4Q2PZ25_originalCoveredPlaquetteFourthHaar
  apply Finset.sum_congr rfl
  intro e _he
  apply Finset.sum_congr rfl
  intro f _hf
  apply Finset.sum_congr rfl
  intro g _hg
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hCov : Covers p e f g k
  · simp [hCov]
  · have hZero := p4Q2PZ25_originalFourCrossingTerm_zero_of_notCovered
      H p e f g k B hCov
    simp [hCov, hZero]

/-- The physical centered first spatial Wilson moment times FOUR
temporal crossings is exactly ONE HALF the finite genuine SU(2)
plaquette-character fourth crossing sum. -/
theorem p4Q2PZ25_originalCenteredFourth_plaquetteSum (B : Cfg) :
    Z14 B = (1 / 2 : ℝ) * ∑ p : Plaq, Row4 p B := by
  classical
  have hp : Continuous (fun A : Cfg => Cross A B) := by
    have hpair : Continuous (fun A : Cfg => (A,B)) :=
      continuous_id.prodMk continuous_const
    have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hpair
    simpa only [Function.comp_def] using hc
  have hχ (p : Plaq) :
      Continuous (fun A : Cfg => χ p A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hi (p : Plaq) :
      Integrable (fun A : Cfg => χ p A*(Cross A B)^4) haar :=
    ((hχ p).mul (hp.pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInt :
      (∫ A : Cfg,
        ∑ p : Plaq, χ p A*(Cross A B)^4 ∂haar) =
      ∑ p : Plaq, (∫ A : Cfg, χ p A*(Cross A B)^4 ∂haar) := by
    rw [integral_finset_sum _ (fun p _ => hi p)]
  change (∫ A : Cfg, h A*(Cross A B)^4 ∂haar) = _
  calc
    (∫ A : Cfg, h A*(Cross A B)^4 ∂haar) =
      (∫ A : Cfg, (1/2 : ℝ) *
        (∑ p : Plaq, χ p A*(Cross A B)^4) ∂haar) := by
          apply integral_congr_ae
          filter_upwards with A
          rw [p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H A]
          unfold p4Q2PW2_originalAllPlaquetteRealTrace
          rw [Finset.sum_mul]
          ring
    _ = (1/2 : ℝ) *
      (∫ A : Cfg, ∑ p : Plaq,
        χ p A*(Cross A B)^4 ∂haar) := by
          rw [integral_const_mul]
    _ = (1/2 : ℝ) * ∑ p : Plaq, Row4 p B := by
          rw [hInt]
          rfl

/-- Original D14 is supported ONLY on four-link tuples covering
all four edges of one genuine spatial SU(2) plaquette. -/
theorem p4Q2PZ25_originalCenteredFourth_onlyCovered (B : Cfg) :
    Z14 B = (1 / 2 : ℝ) * ∑ p : Plaq, Covered4 p B := by
  calc
    Z14 B = (1/2 : ℝ)*∑ p : Plaq, Row4 p B :=
      p4Q2PZ25_originalCenteredFourth_plaquetteSum H B
    _ = (1/2 : ℝ)*∑ p : Plaq, Covered4 p B := by
      apply congrArg (fun t : ℝ => (1/2 : ℝ)*t)
      apply Finset.sum_congr rfl
      intro p _hp
      exact p4Q2PZ25_originalPlaquetteFourthCrossing_onlyCovered H p B

/-- The PZ24 genuine centered spatial-linear/four-crossing boundary
Ward obstruction has NO support outside four-edge-covering temporal
link quadruples. Boundary dependence of the surviving true Haar
terms remains an open physical computation, not an axiom. -/
theorem p4Q2PZ25_originalFourthDefect_onlyCovered (B : Cfg) :
    D14 B = (1/2 : ℝ)*
      ((∑ p : Plaq, Covered4 p B) -
        (∑ p : Plaq, Covered4 p I)) := by
  unfold p4Q2PZ24_originalCenteredFirstFourthDefect
  rw [p4Q2PZ25_originalCenteredFourth_onlyCovered H B,
    p4Q2PZ25_originalCenteredFourth_onlyCovered H I]
  ring

end OriginalFourthCrossingPlaquetteSupport
end GroundStatePosteriorJoint
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ25_originalFourCrossingTerm_zero_of_unusedEdge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ25_originalFourCrossingTerm_zero_of_notCovered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ25_originalPlaquetteFourthCrossing_expand
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ25_originalPlaquetteFourthCrossing_onlyCovered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ25_originalCenteredFourth_plaquetteSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ25_originalCenteredFourth_onlyCovered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ25_originalFourthDefect_onlyCovered
