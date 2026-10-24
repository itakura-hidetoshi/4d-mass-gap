import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPairTripleCrossingWardV5_PZ9
import Mathlib.Tactic

/-!
# P4-Q2-PZ10 — the ORIGINAL full cubic crossing Haar is diagonal in spatial plaquettes

PZ9 proves that the true SU(2) spatial-Haar integral of chi_p chi_q
against any THREE actual temporal crossing energies vanishes for p ≠ q.
This file expands the CUBE of the ORIGINAL COMPLETE temporal Wilson
crossing action, including all ordered triples, repeated link indices,
and every physical spatial link. Original compact product-Haar
integrability allows exact termwise summation.

Consequently the complete spatial plaquette-character SQUARE
weighted cubic-crossing Haar moment reduces to its TRUE diagonal
plaquette-square terms. The centered spatial Wilson-square cubic
moment has the corresponding factor 1/4.

The diagonal cubic-crossing moments are NOT asserted to vanish or be
constant here. This is an analytic input to the genuine sixth Ward
obstruction, not a nonzero physical witness or a mass gap.
No posterior replacement, new axioms, sorry/admit, or spectral proxy.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ10_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ10_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ10_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ10_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ10_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ10_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ10_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalFullTripleCrossingDiagonal

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Φ" => p4Q2PW2_originalAllPlaquetteRealTrace H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H

/-- True original pair of four-edge spatial plaquette real characters
against the CUBE of the full temporal crossing Wilson action. -/
noncomputable def p4Q2PZ10_originalPlaquettePairThreeCrossingHaar
    (p q : Plaq) (B : Cfg) : ℝ :=
  ∫ A : Cfg, (χ p A * χ q A) * (Cross A B)^3 ∂haar

local notation "J3" => p4Q2PZ10_originalPlaquettePairThreeCrossingHaar H

/-- The original full crossing cube is EXACTLY the Haar-integrated
ordered triple spatial-link sum. No coincident indices are deleted. -/
theorem p4Q2PZ10_originalPlaquettePair_fullTripleCrossing_expand
    (p q : Plaq) (B : Cfg) :
    J3 p q B =
      ∑ e : Link, ∑ f : Link, ∑ g : Link,
        (∫ A : Cfg, (χ p A * χ q A) *
          (E ((A e)⁻¹ * B e) *
            E ((A f)⁻¹ * B f) *
            E ((A g)⁻¹ * B g)) ∂haar) := by
  classical
  let T : Link → Cfg → ℝ := fun e A => E ((A e)⁻¹ * B e)
  have hChi (v : Plaq) :
      Continuous (fun A : Cfg => χ v A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H v
  have hT (e : Link) : Continuous (T e) := by
    change Continuous (fun A : Cfg => E ((A e)⁻¹ * B e))
    exact (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hEach (e f g : Link) :
      Integrable (fun A : Cfg =>
        (χ p A * χ q A) *
          (T e A * T f A * T g A)) haar :=
    (((hChi p).mul (hChi q)).mul
      (((hT e).mul (hT f)).mul (hT g))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner (e f : Link) :
      Continuous (fun A : Cfg =>
        ∑ g : Link, (χ p A * χ q A) *
          (T e A * T f A * T g A)) := by
    apply continuous_finset_sum
    intro g _hg
    exact ((hChi p).mul (hChi q)).mul
      (((hT e).mul (hT f)).mul (hT g))
  have hMiddle (e : Link) :
      Continuous (fun A : Cfg =>
        ∑ f : Link, ∑ g : Link,
          (χ p A * χ q A) * (T e A * T f A * T g A)) := by
    apply continuous_finset_sum
    intro f _hf
    exact hInner e f
  have hTripleIntegral :
      (∫ A : Cfg,
        ∑ e : Link, ∑ f : Link, ∑ g : Link,
          (χ p A * χ q A) *
            (T e A * T f A * T g A) ∂haar) =
      ∑ e : Link, ∑ f : Link, ∑ g : Link,
        (∫ A : Cfg, (χ p A * χ q A) *
          (T e A * T f A * T g A) ∂haar) := by
    rw [integral_finset_sum _ (fun e _ =>
      (hMiddle e).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro e _he
    rw [integral_finset_sum _ (fun f _ =>
      (hInner e f).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro f _hf
    rw [integral_finset_sum _ (fun g _ => hEach e f g)]
  have hCube (A : Cfg) :
      (∑ e : Link, T e A)^3 =
        ∑ e : Link, ∑ f : Link, ∑ g : Link,
          T e A * T f A * T g A := by
    have hSquare :
        (∑ e : Link, T e A) * (∑ f : Link, T f A) =
          ∑ e : Link, ∑ f : Link, T e A * T f A := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _he
      rw [Finset.mul_sum]
    calc
      (∑ e : Link, T e A)^3 =
          ((∑ e : Link, T e A) * (∑ f : Link, T f A)) *
            (∑ g : Link, T g A) := by ring
      _ = ∑ e : Link, ∑ f : Link, ∑ g : Link,
          T e A * T f A * T g A := by
        rw [hSquare, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _he
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro f _hf
        rw [Finset.mul_sum]
  have hPoint (A : Cfg) :
      (χ p A * χ q A) * (∑ e : Link, T e A)^3 =
        ∑ e : Link, ∑ f : Link, ∑ g : Link,
          (χ p A * χ q A) *
            (T e A * T f A * T g A) := by
    rw [hCube, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _he
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _hf
    rw [Finset.mul_sum]
  change (∫ A : Cfg,
    (χ p A * χ q A) * (Cross A B)^3 ∂haar) = _
  calc
    (∫ A : Cfg, (χ p A * χ q A) * (Cross A B)^3 ∂haar) =
        ∫ A : Cfg, ∑ e : Link, ∑ f : Link, ∑ g : Link,
          (χ p A * χ q A) *
            (T e A * T f A * T g A) ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PW_originalCrossing_eq_finsetSum H A B]
      exact hPoint A
    _ = ∑ e : Link, ∑ f : Link, ∑ g : Link,
        (∫ A : Cfg, (χ p A * χ q A) *
          (T e A * T f A * T g A) ∂haar) := hTripleIntegral

/-- ALL off-diagonal original plaquette-character pairs have ZERO
Haar moment against the COMPLETE cubic crossing action. -/
theorem p4Q2PZ10_originalOffDiagonal_fullTripleCrossingHaar_zero
    (p q : Plaq) (hpq : p ≠ q) (B : Cfg) :
    J3 p q B = 0 := by
  rw [p4Q2PZ10_originalPlaquettePair_fullTripleCrossing_expand H p q B]
  apply Finset.sum_eq_zero
  intro e _he
  apply Finset.sum_eq_zero
  intro f _hf
  apply Finset.sum_eq_zero
  intro g _hg
  exact p4Q2PZ9_originalOffDiagonalPlaquettePair_tripleCrossingHaar_zero
    H p q hpq e f g B

/-- The true full spatial plaquette trace squared, against the
complete cubic temporal Wilson crossing action, is the sum over
ALL genuine ordered plaquette pairs. -/
theorem p4Q2PZ10_originalPlaquetteTraceSquare_fullCubicHaar_pairSum
    (B : Cfg) :
    (∫ A : Cfg, (Φ A)^2 * (Cross A B)^3 ∂haar) =
      ∑ p : Plaq, ∑ q : Plaq, J3 p q B := by
  classical
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCross : Continuous (fun A : Cfg => Cross A B) := by
    have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hc
  have hChi (p : Plaq) : Continuous (fun A : Cfg => χ p A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hEach (p q : Plaq) :
      Integrable (fun A : Cfg =>
        (χ p A * χ q A) * (Cross A B)^3) haar :=
    (((hChi p).mul (hChi q)).mul
      (hCross.pow 3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner (p : Plaq) :
      Continuous (fun A : Cfg =>
        ∑ q : Plaq, (χ p A * χ q A) * (Cross A B)^3) := by
    apply continuous_finset_sum
    intro q _hq
    exact ((hChi p).mul (hChi q)).mul (hCross.pow 3)
  have hSums :
      (∫ A : Cfg,
        ∑ p : Plaq, ∑ q : Plaq,
          (χ p A * χ q A) * (Cross A B)^3 ∂haar) =
        ∑ p : Plaq, ∑ q : Plaq,
          (∫ A : Cfg,
            (χ p A * χ q A) * (Cross A B)^3 ∂haar) := by
    rw [integral_finset_sum _ (fun p _ =>
      (hInner p).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [integral_finset_sum _ (fun q _ => hEach p q)]
  have hPoint (A : Cfg) :
      (Φ A)^2 * (Cross A B)^3 =
        ∑ p : Plaq, ∑ q : Plaq,
          (χ p A * χ q A) * (Cross A B)^3 := by
    have hSquare :
        (∑ p : Plaq, χ p A) * (∑ q : Plaq, χ q A) =
          ∑ p : Plaq, ∑ q : Plaq, χ p A * χ q A := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
    calc
      (Φ A)^2 * (Cross A B)^3 =
          ((∑ p : Plaq, χ p A) *
            (∑ q : Plaq, χ q A)) * (Cross A B)^3 := by
        unfold p4Q2PW2_originalAllPlaquetteRealTrace
        ring
      _ = (∑ p : Plaq, ∑ q : Plaq, χ p A * χ q A) *
          (Cross A B)^3 := by rw [hSquare]
      _ = ∑ p : Plaq, ∑ q : Plaq,
          (χ p A * χ q A) * (Cross A B)^3 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _hp
        rw [Finset.sum_mul]
  calc
    (∫ A : Cfg, (Φ A)^2 * (Cross A B)^3 ∂haar) =
      ∫ A : Cfg, ∑ p : Plaq, ∑ q : Plaq,
        (χ p A * χ q A) * (Cross A B)^3 ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      exact hPoint A
    _ = ∑ p : Plaq, ∑ q : Plaq, J3 p q B := by
      rw [hSums]
      rfl

/-- Universal off-diagonal triple-crossing Ward selection leaves
EXACTLY the true original diagonal plaquette-square sum. -/
theorem p4Q2PZ10_originalPlaquetteTraceSquare_fullCubicHaar_diagonal
    (B : Cfg) :
    (∫ A : Cfg, (Φ A)^2 * (Cross A B)^3 ∂haar) =
      ∑ p : Plaq,
        (∫ A : Cfg, (χ p A)^2 * (Cross A B)^3 ∂haar) := by
  rw [p4Q2PZ10_originalPlaquetteTraceSquare_fullCubicHaar_pairSum H B]
  calc
    (∑ p : Plaq, ∑ q : Plaq, J3 p q B) =
        ∑ p : Plaq, J3 p p B := by
      apply Finset.sum_congr rfl
      intro p _hp
      apply Finset.sum_eq_single p
      · intro q _hq hqp
        exact p4Q2PZ10_originalOffDiagonal_fullTripleCrossingHaar_zero
          H p q hqp.symm B
      · intro hp
        exact (hp (Finset.mem_univ p)).elim
    _ = ∑ p : Plaq,
        (∫ A : Cfg, (χ p A)^2 * (Cross A B)^3 ∂haar) := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp only [p4Q2PZ10_originalPlaquettePairThreeCrossingHaar, pow_two]

/-- The REAL centered Wilson-spatial-square / full temporal crossing
CUBE is exactly a quarter of the true diagonal plaquette-square sum.
All original intermediate interactions remain available for the
subsequent sixth-order Ward reduction; diagonal constancy is OPEN. -/
theorem p4Q2PZ10_originalCenteredSpatialSquare_fullCubicHaar_diagonal
    (B : Cfg) :
    (∫ A : Cfg,
      (h A)^2 * (Cross A B)^3 ∂haar) =
      (1 / 4 : ℝ) * (∑ p : Plaq,
        (∫ A : Cfg, (χ p A)^2 * (Cross A B)^3 ∂haar)) := by
  calc
    (∫ A : Cfg, (h A)^2 * (Cross A B)^3 ∂haar) =
        ∫ A : Cfg,
          (1 / 4 : ℝ) * ((Φ A)^2 * (Cross A B)^3) ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H A]
      ring
    _ = (1 / 4 : ℝ) *
        (∫ A : Cfg, (Φ A)^2 * (Cross A B)^3 ∂haar) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [p4Q2PZ10_originalPlaquetteTraceSquare_fullCubicHaar_diagonal H B]

end OriginalFullTripleCrossingDiagonal
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ10_originalPlaquettePair_fullTripleCrossing_expand
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ10_originalOffDiagonal_fullTripleCrossingHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ10_originalPlaquetteTraceSquare_fullCubicHaar_pairSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ10_originalPlaquetteTraceSquare_fullCubicHaar_diagonal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ10_originalCenteredSpatialSquare_fullCubicHaar_diagonal
