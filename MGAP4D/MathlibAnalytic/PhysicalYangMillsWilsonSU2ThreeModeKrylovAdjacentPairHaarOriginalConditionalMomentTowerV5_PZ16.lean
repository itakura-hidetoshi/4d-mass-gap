import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthBoundaryPolarizationV5_PZ15
import Mathlib.Tactic

/-!
# P4-Q2-PZ16 — exact original interacting two-slab Haar moment tower

For the ORIGINAL complete SU(2) two-slab Wilson action
  Q(X,A,B) = S(X,A) + S(A,B),
the PZ15 fourth-degree polarization has an exact translated
polynomial in the GENUINE left-slab action S(X,A).

Its left Haar integral is an explicit tower M1(A),...,M4(A), where
  Mk(A) = integral_X S(X,A)^k dHaar(X).
The fifth left moment M5(A) cancels exactly from boundary differences:
this follows from polynomial differentiation and not from any
factorization or replacement of the original posterior.

The physical right-boundary response retains S(A,B), its spatial
plaquettes at A, and the complete second Haar integration over A.
The PZ15 residual Ward response and W6 are thereby expressed through
the genuine left conditional moment tower (and the unchanged one-slab
boundary response). No new axiom, sorry/admit, independent posterior,
surrogate or assertion of W6 nonvanishing or mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ16_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ16_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ16_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ16_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ16_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ16_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ16_productProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalConditionalLeftMomentTower

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "P4" => p4Q2PZ15_originalFourthPolarization
local notation "J1" => p4Q2PZ15_originalOneSlabFifthBoundaryResponse H
local notation "J2" => p4Q2PZ15_originalTwoSlabFifthBoundaryResponse H
local notation "r1" => p4Q2PZ13_originalOneSlabFifthResidual H
local notation "r2" => p4Q2PZ14_originalTwoSlabFifthResidual H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H

/-- A fifth-degree action difference has only the four lower
left-slab moments in its fourth-degree boundary-polarization kernel. -/
theorem p4Q2PZ16_originalFourthPolarization_translate
    (s t u : ℝ) :
    P4 (s+t) (s+u) =
      ((((5*s^4 + 10*(t+u)*s^3) +
          10*(t^2+t*u+u^2)*s^2) +
          5*(t^3+t^2*u+t*u^2+u^3)*s) + P4 t u) := by
  unfold p4Q2PZ15_originalFourthPolarization
  ring

/-- Genuine Haar moment of the original FULL one-slab Wilson action,
with right boundary A, NOT a posterior or a replacement measure. -/
noncomputable def p4Q2PZ16_originalLeftSlabMoment
    (k : ℕ) (A : Cfg) : ℝ :=
  ∫ X : Cfg, (S X A)^k ∂haar

local notation "M" => p4Q2PZ16_originalLeftSlabMoment H

/-- Full left Haar-averaged polarizing kernel: a concrete Wilson
moment tower M1,...,M4; NO independent-posterior separation. -/
noncomputable def p4Q2PZ16_originalConditionalFourthTower
    (A : Cfg) (t u : ℝ) : ℝ :=
  ((((5 * M 4 A + 10*(t+u)*M 3 A) +
      10*(t^2+t*u+u^2)*M 2 A) +
      5*(t^3+t^2*u+t*u^2+u^3)*M 1 A) + P4 t u)

local notation "K" => p4Q2PZ16_originalConditionalFourthTower H

private theorem p4Q2PZ16_slab_continuous (A : Cfg) :
    Continuous (fun X : Cfg => S X A) := by
  have hPair : Continuous (fun X : Cfg => (X,A)) :=
    continuous_id.prodMk continuous_const
  have hCont :=
    (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
  simpa only [Function.comp_def] using hCont

/-- Integrate a fourth-degree polynomial against the true finite
compact SU(2) spatial Haar probability. Only genuine linearity is used. -/
private theorem p4Q2PZ16_integral_fourthPolynomial
    (f : Cfg → ℝ) (hf : Continuous f)
    (c4 c3 c2 c1 c0 : ℝ) :
    (∫ X : Cfg,
      ((((c4*(f X)^4 + c3*(f X)^3) + c2*(f X)^2) + c1*f X) + c0)
      ∂haar) =
      ((((c4*(∫ X : Cfg, (f X)^4 ∂haar) +
          c3*(∫ X : Cfg, (f X)^3 ∂haar)) +
          c2*(∫ X : Cfg, (f X)^2 ∂haar)) +
          c1*(∫ X : Cfg, f X ∂haar)) + c0) := by
  have hi4 : Integrable (fun X : Cfg => c4*(f X)^4) haar :=
    (continuous_const.mul (hf.pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi3 : Integrable (fun X : Cfg => c3*(f X)^3) haar :=
    (continuous_const.mul (hf.pow 3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun X : Cfg => c2*(f X)^2) haar :=
    (continuous_const.mul (hf.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun X : Cfg => c1*f X) haar :=
    (continuous_const.mul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi0 : Integrable (fun _ : Cfg => c0) haar := integrable_const c0
  have hadd1 :
      (∫ X : Cfg, c4*(f X)^4 + c3*(f X)^3 ∂haar) =
        (∫ X : Cfg, c4*(f X)^4 ∂haar) +
          (∫ X : Cfg, c3*(f X)^3 ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add hi4 hi3)
  have hadd2 :
      (∫ X : Cfg, (c4*(f X)^4 + c3*(f X)^3) + c2*(f X)^2 ∂haar) =
        (∫ X : Cfg, c4*(f X)^4 + c3*(f X)^3 ∂haar) +
          (∫ X : Cfg, c2*(f X)^2 ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add (hi4.add hi3) hi2)
  have hadd3 :
      (∫ X : Cfg,
        ((c4*(f X)^4 + c3*(f X)^3) + c2*(f X)^2) + c1*f X ∂haar) =
        (∫ X : Cfg, (c4*(f X)^4 + c3*(f X)^3) + c2*(f X)^2 ∂haar) +
          (∫ X : Cfg, c1*f X ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add ((hi4.add hi3).add hi2) hi1)
  have hadd4 :
      (∫ X : Cfg,
        (((c4*(f X)^4 + c3*(f X)^3) + c2*(f X)^2) + c1*f X) + c0 ∂haar) =
        (∫ X : Cfg,
          ((c4*(f X)^4 + c3*(f X)^3) + c2*(f X)^2) + c1*f X ∂haar) +
          (∫ X : Cfg, c0 ∂haar) := by
    simpa only [Pi.add_apply] using
      (integral_add (((hi4.add hi3).add hi2).add hi1) hi0)
  rw [hadd4, hadd3, hadd2, hadd1]
  simp [integral_const_mul]

/-- Exact original left-slab conditional moment expansion of the
fourth-degree polarization of the unchanged two-slab Wilson action.
The constant term uses Haar probability mass one, not a normalization
of the interacting posterior. -/
theorem p4Q2PZ16_originalLeftHaar_polarization_tower
    (A : Cfg) (t u : ℝ) :
    (∫ X : Cfg, P4 (S X A+t) (S X A+u) ∂haar) =
      K A t u := by
  have hSlab : Continuous (fun X : Cfg => S X A) :=
    p4Q2PZ16_slab_continuous H A
  calc
    (∫ X : Cfg, P4 (S X A+t) (S X A+u) ∂haar) =
      ∫ X : Cfg,
        ((((5*(S X A)^4 + 10*(t+u)*(S X A)^3) +
          10*(t^2+t*u+u^2)*(S X A)^2) +
          5*(t^3+t^2*u+t*u^2+u^3)*(S X A)) + P4 t u)
        ∂haar := by
          apply integral_congr_ae
          filter_upwards with X
          exact p4Q2PZ16_originalFourthPolarization_translate (S X A) t u
    _ = ((((5*(∫ X : Cfg, (S X A)^4 ∂haar) +
          10*(t+u)*(∫ X : Cfg, (S X A)^3 ∂haar)) +
          10*(t^2+t*u+u^2)*(∫ X : Cfg, (S X A)^2 ∂haar)) +
          5*(t^3+t^2*u+t*u^2+u^3)*(∫ X : Cfg, S X A ∂haar)) +
          P4 t u) := by
          exact p4Q2PZ16_integral_fourthPolynomial H
            (fun X : Cfg => S X A) hSlab
            5 (10*(t+u)) (10*(t^2+t*u+u^2))
            (5*(t^3+t^2*u+t*u^2+u^3)) (P4 t u)
    _ = K A t u := by
      simp only [p4Q2PZ16_originalConditionalFourthTower,
        p4Q2PZ16_originalLeftSlabMoment, pow_one]

/-- Genuine right-boundary double Haar response, with full spatial
Wilson contribution at the intermediate slice A in every M_k(A). -/
noncomputable def p4Q2PZ16_originalTwoSlabMomentTowerBoundaryResponse
    (B C : Cfg) : ℝ :=
  ∫ A : Cfg, (S A B - S A C) * K A (S A B) (S A C) ∂haar

local notation "T2" => p4Q2PZ16_originalTwoSlabMomentTowerBoundaryResponse H

/-- Actual original TWO-SLAB fifth-response J2 equals the explicit
left-slab Haar-moment tower. It is NOT a factorization of posteriors:
the left conditioned action is averaged at the original boundary A
inside the outer Haar integral. -/
theorem p4Q2PZ16_originalTwoSlabResponse_eq_tower (B C : Cfg) :
    J2 B C = T2 B C := by
  unfold p4Q2PZ15_originalTwoSlabFifthBoundaryResponse
    p4Q2PZ16_originalTwoSlabMomentTowerBoundaryResponse
  apply integral_congr_ae
  filter_upwards with A
  calc
    (∫ X : Cfg,
      ((w B-w C) + (Cross A B-Cross A C)) *
        P4 (Q X A B) (Q X A C) ∂haar) =
      (∫ X : Cfg,
        (S A B - S A C) *
          P4 (S X A + S A B) (S X A + S A C) ∂haar) := by
            apply integral_congr_ae
            filter_upwards with X
            change
              ((w B-w C) + (Cross A B-Cross A C)) *
                P4 (S X A + S A B) (S X A + S A C) = _
            rw [← p4Q2PZ15_originalOneSlabAction_boundaryDifference H A B C]
    _ = (S A B - S A C) *
          (∫ X : Cfg, P4 (S X A+S A B) (S X A+S A C) ∂haar) := by
            rw [integral_const_mul]
    _ = (S A B - S A C) * K A (S A B) (S A C) := by
          rw [p4Q2PZ16_originalLeftHaar_polarization_tower H A (S A B) (S A C)]

/-- Fifth residual boundary gap is the true conditional moment tower
minus the unchanged original one-slab Haar boundary response. -/
theorem p4Q2PZ16_originalResidualGap_eq_towerMinusOneSlab
    (B C : Cfg) :
    (r2 B-r1 B) - (r2 C-r1 C) =
      T2 B C - J1 B C := by
  rw [p4Q2PZ15_originalResidualGap_boundaryResponse H B C]
  unfold p4Q2PZ15_originalWardResidualResponseGap
  rw [p4Q2PZ16_originalTwoSlabResponse_eq_tower H B C]

/-- True sixth Ward obstruction in the full SU(2) Wilson model,
now reduced to the original one-slab response and the original
LEFT SLAB Haar moments M1..M4, with all intermediate spatial
plaquettes and the outer Haar measure still present. -/
theorem p4Q2PZ16_originalSixthWard_conditionalMomentTower
    (A B C : Cfg) :
    W6 A B C =
      720 * C6 A B C -
      6 * ((a B-a A) * (T2 C A-J1 C A) -
           (a C-a A) * (T2 B A-J1 B A)) := by
  rw [p4Q2PZ15_originalSixthWard_physicalBoundaryResponse H A B C]
  unfold p4Q2PZ15_originalWardResidualResponseGap
  rw [p4Q2PZ16_originalTwoSlabResponse_eq_tower H C A,
    p4Q2PZ16_originalTwoSlabResponse_eq_tower H B A]

/-- Boundary responses from the original double Haar action form an
exact cocycle under concatenation of boundary differences. -/
theorem p4Q2PZ16_originalTwoSlabMomentTower_cocycle
    (A B C : Cfg) :
    T2 A B + T2 B C = T2 A C := by
  rw [← p4Q2PZ16_originalTwoSlabResponse_eq_tower H A B,
    ← p4Q2PZ16_originalTwoSlabResponse_eq_tower H B C,
    ← p4Q2PZ16_originalTwoSlabResponse_eq_tower H A C,
    ← p4Q2PZ15_originalTwoSlabFifth_difference_response H A B,
    ← p4Q2PZ15_originalTwoSlabFifth_difference_response H B C,
    ← p4Q2PZ15_originalTwoSlabFifth_difference_response H A C]
  ring

/-- The genuine Ward residual response gap also obeys the same
boundary cocycle; no assumption that it vanishes is used. -/
theorem p4Q2PZ16_originalResidualResponseGap_cocycle
    (A B C : Cfg) :
    p4Q2PZ15_originalWardResidualResponseGap H A B +
      p4Q2PZ15_originalWardResidualResponseGap H B C =
      p4Q2PZ15_originalWardResidualResponseGap H A C := by
  rw [← p4Q2PZ15_originalResidualGap_boundaryResponse H A B,
    ← p4Q2PZ15_originalResidualGap_boundaryResponse H B C,
    ← p4Q2PZ15_originalResidualGap_boundaryResponse H A C]
  ring

end OriginalConditionalLeftMomentTower
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ16_originalFourthPolarization_translate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ16_originalLeftHaar_polarization_tower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ16_originalTwoSlabResponse_eq_tower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ16_originalResidualGap_eq_towerMinusOneSlab
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ16_originalSixthWard_conditionalMomentTower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ16_originalTwoSlabMomentTower_cocycle
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ16_originalResidualResponseGap_cocycle
