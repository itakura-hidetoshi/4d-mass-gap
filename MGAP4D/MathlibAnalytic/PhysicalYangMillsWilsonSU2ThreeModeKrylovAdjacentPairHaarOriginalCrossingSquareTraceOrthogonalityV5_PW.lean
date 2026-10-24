import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPlaquetteTwoCrossingOrthogonalityV5_PV2
import Mathlib.Tactic

/-!
# P4-Q2-PW — full original temporal crossing SQUARE is orthogonal to each spatial plaquette trace

PV2 proves exact spatial Haar orthogonality of each real SU(2) Wilson
plaquette character χ_p to ANY genuine ordered pair of temporal
crossing Wilson plaquette energies. Here the ORIGINAL complete crossing
action is rewritten as the finite sum over the true spatial link list;
its square is the full double sum, including all diagonal e=f terms.
Compact-continuous Haar integrability and Mathlib's finite-sum
integral identity let us apply PV2 term by term. This proves
  ∫ χ_p(A) * Cross(A,B)^2 dHaar(A) = 0
without independent-link posterior replacement, rank, or additional
Ward assumptions. It also proves the pure χ_p Haar mean is zero.

This does NOT yet identify the full centered first-action moment with
the sum of χ_p: that final finite plaquette-sum bridge is the next step.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PW_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PW_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PW_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PW_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PW_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PW_spatialLinksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualOriginalCrossingSquareHaar
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
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H

/-- Exact original full crossing action as a finite LINK sum, with
all temporal Wilson terms and no interaction removed. -/
theorem p4Q2PW_originalCrossing_eq_finsetSum (A B : Cfg) :
    Cross A B = ∑ e : Link, E ((A e)⁻¹ * B e) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
    periodicHypercubicEvenSpatialSliceLinkList
  simpa using
    (Finset.sum_map_toList
      (Finset.univ : Finset Link)
      (fun e : Link => E ((A e)⁻¹ * B e)))

/-- A single original SU(2) spatial plaquette normalized trace
has exactly zero Haar mean, by the actual one-link center symmetry. -/
theorem p4Q2PW_originalPlaquetteChar_HaarMean_zero (p : Plaq) :
    (∫ A : Cfg, χ p A ∂haar) = 0 := by
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H (e0 p) (χ p)
    (p4Q2PV_originalPlaquetteRealCharacter_continuous H p)
    (p4Q2PV_originalPlaquetteRealCharacter_centerOdd
      H p (e0 p) (Or.inl rfl))

/-- The ORIGINAL complete temporal-crossing action squared is orthogonal
to every genuine spatial Wilson plaquette normalized SU(2) trace,
for every finite H and original right spatial boundary B. -/
theorem p4Q2PW_originalPlaquetteChar_crossingSquareHaar_zero
    (p : Plaq) (B : Cfg) :
    (∫ A : Cfg, χ p A * (Cross A B) ^ 2 ∂haar) = 0 := by
  classical
  let T : Link → Cfg → ℝ :=
    fun e A => E ((A e)⁻¹ * B e)
  have hChi : Continuous (fun A : Cfg => χ p A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hT (e : Link) : Continuous (T e) := by
    change Continuous (fun A : Cfg => E ((A e)⁻¹ * B e))
    exact (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hEach (e f : Link) :
      Integrable (fun A : Cfg =>
        χ p A * (T e A * T f A)) haar :=
    (hChi.mul ((hT e).mul (hT f))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInnerCont (e : Link) :
      Continuous (fun A : Cfg =>
        ∑ f : Link, χ p A * (T e A * T f A)) := by
    apply continuous_finset_sum
    intro f _hf
    exact hChi.mul ((hT e).mul (hT f))
  have hDoubleIntegral :
      (∫ A : Cfg,
        ∑ e : Link, ∑ f : Link,
          χ p A * (T e A * T f A) ∂haar) =
      ∑ e : Link, ∑ f : Link,
        (∫ A : Cfg, χ p A * (T e A * T f A) ∂haar) := by
    rw [integral_finset_sum _ (fun e _ =>
      (hInnerCont e).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro e _he
    rw [integral_finset_sum _ (fun f _ => hEach e f)]
  have hPoint (A : Cfg) :
      χ p A * (∑ e : Link, T e A) ^ 2 =
        ∑ e : Link, ∑ f : Link,
          χ p A * (T e A * T f A) := by
    have hProduct :
        (∑ e : Link, T e A) * (∑ f : Link, T f A) =
          ∑ e : Link, ∑ f : Link, T e A * T f A := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _he
      rw [Finset.mul_sum]
    calc
      χ p A * (∑ e : Link, T e A) ^ 2 =
          χ p A * ((∑ e : Link, T e A) *
            (∑ f : Link, T f A)) := by ring
      _ = χ p A *
            (∑ e : Link, ∑ f : Link, T e A * T f A) := by rw [hProduct]
      _ = ∑ e : Link, ∑ f : Link,
          χ p A * (T e A * T f A) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _he
        rw [Finset.mul_sum]
  have hEachZero (e f : Link) :
      (∫ A : Cfg, χ p A * (T e A * T f A) ∂haar) = 0 :=
    p4Q2PV2_originalPlaquette_twoCrossingHaar_zero H p e f B
  calc
    (∫ A : Cfg, χ p A * (Cross A B) ^ 2 ∂haar) =
        ∫ A : Cfg, ∑ e : Link, ∑ f : Link,
          χ p A * (T e A * T f A) ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PW_originalCrossing_eq_finsetSum H A B]
      exact hPoint A
    _ = ∑ e : Link, ∑ f : Link,
        (∫ A : Cfg, χ p A * (T e A * T f A) ∂haar) :=
      hDoubleIntegral
    _ = 0 := by simp [hEachZero]

end ActualOriginalCrossingSquareHaar
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PW_originalCrossing_eq_finsetSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PW_originalPlaquetteChar_HaarMean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PW_originalPlaquetteChar_crossingSquareHaar_zero
