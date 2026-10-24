import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDistinctTwoCrossingDiagonalV5_PY8B
import Mathlib.Tactic

/-!
# P4-Q2-PY8C — FULL original diagonal plaquette square/two-crossing Haar invariance

The original complete temporal crossing Wilson action is the SUM of
all true spatial-link temporal SU(2) Wilson energies, and its square
is the complete ordered two-link sum, with every diagonal e=f
and every off-diagonal e≠f pair retained.

For e=f, PY8 gives right-boundary invariance of χ_p² times the
genuine temporal E_e² by the exact spatial gauge Haar Ward action.
For e≠f, PY8B gives right-boundary invariance by original
SU(2) center parity and exact trace orthogonality.

Integrating the unchanged finite link double sum termwise proves
the ENTIRE original χ_p² * Cross(A,B)² reference-Haar pairing is
right-boundary independent, for every true spatial plaquette.
It follows that ALL diagonal p=q terms in PY7's finite
plaquette-pair fifth Ward obstruction are boundary constants.
No nonzero or vanishing result is claimed for the full off-diagonal
p≠q sector. No independent interacting posterior, new axiom,
Dobrushin, sorry/admit or spectral surrogate.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY8C_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY8C_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY8C_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY8C_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY8C_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PY8C_nativeLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection

namespace GroundStatePosteriorJoint
section OriginalDiagonalFullCrossingWard
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
local notation "J" => p4Q2PY7_originalPlaquettePairTwoCrossingHaar H

/-- Each ordered pair of temporal Wilson energies, including e=f,
has exactly the same χ_p²-weighted ORIGINAL spatial Haar moment
for any true right boundary as for the identity right boundary. -/
theorem p4Q2PY8_originalPlaquetteSquare_crossingPairHaar_invariant
    (p : Plaq) (e f : Link) (B : Cfg) :
    (∫ A : Cfg, (χ p A)^2 *
      (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) =
    (∫ A : Cfg, (χ p A)^2 *
      (E ((A e)⁻¹) * E ((A f)⁻¹)) ∂haar) := by
  by_cases hef : e = f
  · subst f
    simpa only [pow_two] using
      (p4Q2PY8_originalPlaquetteSquare_temporalLinkSquareHaar_invariant
        H p e B)
  · exact p4Q2PY8_originalPlaquetteSquare_distinctCrossingPair_Haar_invariant
      H p e f hef B

/-- The TRUE complete two-crossing Wilson action square, with all
ordered link pairs and repeated-link contributions retained, has
boundary-INDEPENDENT spatial Haar pairing with χ_p². -/
theorem p4Q2PY8_originalPlaquetteSquare_fullCrossingSquareHaar_invariant
    (p : Plaq) (B : Cfg) :
    (∫ A : Cfg, (χ p A)^2 * (Cross A B)^2 ∂haar) =
      (∫ A : Cfg, (χ p A)^2 *
        (Cross A (fun _ => 1))^2 ∂haar) := by
  classical
  let T : Cfg → Link → ℝ := fun D e => 0
  have hExpand (D : Cfg) :
      (∫ A : Cfg, (χ p A)^2 * (Cross A D)^2 ∂haar) =
      ∑ e : Link, ∑ f : Link,
        (∫ A : Cfg, (χ p A)^2 *
          (E ((A e)⁻¹ * D e) * E ((A f)⁻¹ * D f)) ∂haar) := by
    let S : Link → Cfg → ℝ := fun e A => E ((A e)⁻¹ * D e)
    have hChi : Continuous (fun A : Cfg => (χ p A)^2) :=
      (p4Q2PV_originalPlaquetteRealCharacter_continuous H p).pow 2
    have hS (e : Link) : Continuous (S e) := by
      change Continuous (fun A : Cfg => E ((A e)⁻¹ * D e))
      exact (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
        ((continuous_apply e).inv.mul continuous_const)
    have hEach (e f : Link) :
        Integrable (fun A : Cfg =>
          (χ p A)^2 * (S e A * S f A)) haar :=
      (hChi.mul ((hS e).mul (hS f))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hInner (e : Link) :
        Continuous (fun A : Cfg =>
          ∑ f : Link, (χ p A)^2 * (S e A * S f A)) := by
      apply continuous_finset_sum
      intro f _hf
      exact hChi.mul ((hS e).mul (hS f))
    have hSums :
        (∫ A : Cfg,
          ∑ e : Link, ∑ f : Link,
            (χ p A)^2 * (S e A * S f A) ∂haar) =
        ∑ e : Link, ∑ f : Link,
          (∫ A : Cfg, (χ p A)^2 * (S e A * S f A) ∂haar) := by
      rw [integral_finset_sum _ (fun e _ =>
        (hInner e).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))]
      apply Finset.sum_congr rfl
      intro e _he
      rw [integral_finset_sum _ (fun f _ => hEach e f)]
    have hPoint (A : Cfg) :
        (χ p A)^2 * (∑ e : Link, S e A)^2 =
        ∑ e : Link, ∑ f : Link,
          (χ p A)^2 * (S e A * S f A) := by
      have hProduct :
          (∑ e : Link, S e A) * (∑ f : Link, S f A) =
          ∑ e : Link, ∑ f : Link, S e A * S f A := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _he
        rw [Finset.mul_sum]
      calc
        (χ p A)^2 * (∑ e : Link, S e A)^2 =
            (χ p A)^2 * ((∑ e : Link, S e A) *
              (∑ f : Link, S f A)) := by ring
        _ = (χ p A)^2 *
              (∑ e : Link, ∑ f : Link, S e A * S f A) := by
          rw [hProduct]
        _ = ∑ e : Link, ∑ f : Link,
              (χ p A)^2 * (S e A * S f A) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _he
          rw [Finset.mul_sum]
    calc
      (∫ A : Cfg, (χ p A)^2 * (Cross A D)^2 ∂haar) =
        ∫ A : Cfg, ∑ e : Link, ∑ f : Link,
          (χ p A)^2 * (S e A * S f A) ∂haar := by
        apply integral_congr_ae
        filter_upwards with A
        rw [p4Q2PW_originalCrossing_eq_finsetSum H A D]
        exact hPoint A
      _ = ∑ e : Link, ∑ f : Link,
        (∫ A : Cfg, (χ p A)^2 *
          (E ((A e)⁻¹ * D e) * E ((A f)⁻¹ * D f)) ∂haar) := by
        rw [hSums]
        rfl
  calc
    (∫ A : Cfg, (χ p A)^2 * (Cross A B)^2 ∂haar) =
      ∑ e : Link, ∑ f : Link,
        (∫ A : Cfg, (χ p A)^2 *
          (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) :=
      hExpand B
    _ = ∑ e : Link, ∑ f : Link,
        (∫ A : Cfg, (χ p A)^2 *
          (E ((A e)⁻¹) * E ((A f)⁻¹)) ∂haar) := by
        apply Finset.sum_congr rfl
        intro e _he
        apply Finset.sum_congr rfl
        intro f _hf
        exact p4Q2PY8_originalPlaquetteSquare_crossingPairHaar_invariant
          H p e f B
    _ = (∫ A : Cfg, (χ p A)^2 *
        (Cross A (fun _ => 1))^2 ∂haar) := by
      simpa only [Pi.one_apply, mul_one] using (hExpand (fun _ => 1)).symm

/-- Every actual diagonal p=q term in the original finite
plaquette-pair obstruction PY7 is independent of the right SU(2)
spatial boundary. Nothing is asserted about p≠q here. -/
theorem p4Q2PY8_originalDiagonalPlaquettePairHaar_invariant
    (p : Plaq) (B : Cfg) :
    J p p B = J p p (fun _ => 1) := by
  unfold p4Q2PY7_originalPlaquettePairTwoCrossingHaar
  simpa only [pow_two] using
    (p4Q2PY8_originalPlaquetteSquare_fullCrossingSquareHaar_invariant H p B)

end OriginalDiagonalFullCrossingWard
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY8_originalPlaquetteSquare_crossingPairHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY8_originalPlaquetteSquare_fullCrossingSquareHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY8_originalDiagonalPlaquettePairHaar_invariant
