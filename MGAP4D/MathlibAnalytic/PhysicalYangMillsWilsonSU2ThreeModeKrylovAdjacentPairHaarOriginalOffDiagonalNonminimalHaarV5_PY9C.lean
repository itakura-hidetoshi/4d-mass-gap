import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalOffDiagonalGeometryV5_PY9A
import Mathlib.Tactic

/-!
# P4-Q2-PY9C — full original off-diagonal Haar orthogonality at period >= 4

PY9A supplies a genuine p-only physical Wilson edge, untouched by
any two specified temporal-crossing links, whenever distinct spatial
plaquettes p != q are in an even period >= 4. PY8D's true spatial SU(2)
center flip therefore kills EACH real plaquette-pair Haar integral with
the two genuine temporal Wilson energies.

This file restores the COMPLETE original temporal crossing action
through the exact finite-link square expansion; both ordered
off-diagonal crossing pairs and e=f terms are retained and then shown
to vanish in every off-diagonal spatial plaquette pair. No Wilson
interaction is suppressed or modified, and this is NOT a mass-gap
theorem or an assertion about minimal period H=0.
No new axioms/sorry/admit, artificial posterior, Dobrushin, fake rank.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY9C_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY9C_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY9C_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY9C_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY9C_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PY9C_nativeLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection

namespace GroundStatePosteriorJoint
section OriginalNonminimalOffDiagonalPairHaar
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "J" => p4Q2PY7_originalPlaquettePairTwoCrossingHaar H

/-- Exact PY8D center-flip cancellation now holds for EVERY distinct
original spatial plaquette pair at any even side length >= 4,
without any geometric existence hypothesis in the theorem statement. -/
theorem p4Q2PY9_originalOffDiagonal_twoCrossingHaar_zero_nonminimal
    (hH : 0 < H) (p q : Plaq) (hpq : p ≠ q)
    (e f : Link) (B : Cfg) :
    (∫ A : Cfg, (χ p A * χ q A) *
      (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) = 0 := by
  obtain ⟨target, hp, hq, he, hf⟩ :=
    p4Q2PY9_originalDistinctPlaquettes_freeLink_for_twoCrossings
      H hH p q hpq e f
  have hp' :
      target = p4Q2PU3_originalPlaquetteEdge0 H p ∨
      target = p4Q2PU3_originalPlaquetteEdge1 H p ∨
      target = p4Q2PU3_originalPlaquetteEdge2 H p ∨
      target = p4Q2PU3_originalPlaquetteEdge3 H p :=
    (p4Q2PY9_originalPlaquettePhysicalEdges_mem H p target).mp hp
  have hq' :
      ¬ (target = p4Q2PU3_originalPlaquetteEdge0 H q ∨
      target = p4Q2PU3_originalPlaquetteEdge1 H q ∨
      target = p4Q2PU3_originalPlaquetteEdge2 H q ∨
      target = p4Q2PU3_originalPlaquetteEdge3 H q) := by
    intro hmember
    exact hq ((p4Q2PY9_originalPlaquettePhysicalEdges_mem H q target).mpr
      hmember)
  exact p4Q2PY8_originalPlaquettePair_twoCrossingHaar_zero_of_freeEdge
    H p q e f target hp' hq' he hf B

/-- Exact double-crossing expansion against ANY original spatial
plaquette-character PAIR. This retains all ordered crossing links. -/
theorem p4Q2PY9_originalPlaquettePair_fullCrossingSquare_expand
    (p q : Plaq) (B : Cfg) :
    J p q B =
      ∑ e : Link, ∑ f : Link,
        (∫ A : Cfg, (χ p A * χ q A) *
          (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) := by
  classical
  let S : Link → Cfg → ℝ := fun e A => E ((A e)⁻¹ * B e)
  have hChi : Continuous (fun A : Cfg => χ p A * χ q A) :=
    (p4Q2PV_originalPlaquetteRealCharacter_continuous H p).mul
      (p4Q2PV_originalPlaquetteRealCharacter_continuous H q)
  have hS (e : Link) : Continuous (S e) := by
    change Continuous (fun A : Cfg => E ((A e)⁻¹ * B e))
    exact (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hEach (e f : Link) :
      Integrable (fun A : Cfg =>
        (χ p A * χ q A) * (S e A * S f A)) haar :=
    (hChi.mul ((hS e).mul (hS f))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner (e : Link) :
      Continuous (fun A : Cfg =>
        ∑ f : Link, (χ p A * χ q A) * (S e A * S f A)) := by
    apply continuous_finset_sum
    intro f _hf
    exact hChi.mul ((hS e).mul (hS f))
  have hSums :
      (∫ A : Cfg,
        ∑ e : Link, ∑ f : Link,
          (χ p A * χ q A) * (S e A * S f A) ∂haar) =
      ∑ e : Link, ∑ f : Link,
        (∫ A : Cfg, (χ p A * χ q A) * (S e A * S f A) ∂haar) := by
    rw [integral_finset_sum _ (fun e _ =>
      (hInner e).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro e _he
    rw [integral_finset_sum _ (fun f _ => hEach e f)]
  have hPoint (A : Cfg) :
      (χ p A * χ q A) * (∑ e : Link, S e A)^2 =
      ∑ e : Link, ∑ f : Link,
        (χ p A * χ q A) * (S e A * S f A) := by
    have hProduct :
        (∑ e : Link, S e A) * (∑ f : Link, S f A) =
        ∑ e : Link, ∑ f : Link, S e A * S f A := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _he
      rw [Finset.mul_sum]
    calc
      (χ p A * χ q A) * (∑ e : Link, S e A)^2 =
          (χ p A * χ q A) *
            ((∑ e : Link, S e A) * (∑ f : Link, S f A)) := by ring
      _ = (χ p A * χ q A) *
            (∑ e : Link, ∑ f : Link, S e A * S f A) := by
        rw [hProduct]
      _ = ∑ e : Link, ∑ f : Link,
            (χ p A * χ q A) * (S e A * S f A) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _he
        rw [Finset.mul_sum]
  calc
    J p q B = ∫ A : Cfg,
      ∑ e : Link, ∑ f : Link,
        (χ p A * χ q A) * (S e A * S f A) ∂haar := by
      unfold p4Q2PY7_originalPlaquettePairTwoCrossingHaar
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PW_originalCrossing_eq_finsetSum H A B]
      exact hPoint A
    _ = ∑ e : Link, ∑ f : Link,
        (∫ A : Cfg, (χ p A * χ q A) *
          (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) := by
      rw [hSums]

/-- Every distinct ORIGINAL spatial SU(2) plaquette pair is Haar-orthogonal
to the COMPLETE temporal Wilson two-crossing square for even side >= 4. -/
theorem p4Q2PY9_originalOffDiagonalPlaquettePairHaar_zero_nonminimal
    (hH : 0 < H) (p q : Plaq) (hpq : p ≠ q) (B : Cfg) :
    J p q B = 0 := by
  rw [p4Q2PY9_originalPlaquettePair_fullCrossingSquare_expand H p q B]
  apply Finset.sum_eq_zero
  intro e _he
  apply Finset.sum_eq_zero
  intro f _hf
  exact p4Q2PY9_originalOffDiagonal_twoCrossingHaar_zero_nonminimal
    H hH p q hpq e f B

end OriginalNonminimalOffDiagonalPairHaar
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalOffDiagonal_twoCrossingHaar_zero_nonminimal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalPlaquettePair_fullCrossingSquare_expand
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY9_originalOffDiagonalPlaquettePairHaar_zero_nonminimal
