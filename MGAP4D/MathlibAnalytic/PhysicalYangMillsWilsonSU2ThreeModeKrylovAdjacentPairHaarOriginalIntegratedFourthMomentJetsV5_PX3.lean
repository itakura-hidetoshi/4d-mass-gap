import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalQuarticExponentialQuinticRemainderV5_PX2
import Mathlib.Tactic

/-!
# P4-Q2-PX3 — identify genuine Haar-integrated quartic Wilson kernels with PX jets

PX2 proves a fifth-order real exponential remainder for the
ORIGINAL one- and two-slab SU(2) Wilson kernels before and after
unmodified spatial Haar integration. This file bridges the exact
integrals of the quartic kernel polynomials to PX's full authentic
fourth action-moment jets, not hypothetical formal coefficients:
 ∫ Taylor4(-beta*S(X,B)) dHaar(X) = J4_one(beta,B)
 ∫∫Taylor4(-beta*Q(X,A,B)) dHaar(X) dHaar(A) = J4_two(beta,B).

All actions retain the ORIGINAL intermediate spatial Wilson
plaquette energy and crossing interactions. The two-slab identity
uses true continuity in the intermediate boundary and Bochner
evaluation of the authentic inner Haar integral; no factorization
of interacting Wilson posteriors. No extra axiom, sorry or admit.

Combining these exact integral identifications with the PX2
remainder into true row bounds, then determinant sixth-order
stability, remains the following step.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PX3_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PX3_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PX3_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PX3_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PX3_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalIntegratedQuarticMoments
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "C1" => p4Q2PP_originalOneSlabCubicTaylor H
local notation "C2" => p4Q2PP_originalTwoSlabCubicTaylor H
local notation "T1" => p4Q2PX2_originalOneSlabQuarticTaylor H
local notation "T2" => p4Q2PX2_originalTwoSlabQuarticTaylor H
local notation "J1" => p4Q2PX_originalOneSlabFormalTaylor4 H
local notation "J2" => p4Q2PX_originalTwoSlabFormalTaylor4 H

private theorem p4Q2PX3_oneSlabAction_row_continuous (B : Cfg) :
    Continuous (fun X : Cfg => S X B) := by
  have hPair : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have h := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
  simpa only [Function.comp_def] using h

private theorem p4Q2PX3_twoSlabAction_pair_continuous (B : Cfg) :
    Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) := by
  have hSlab : Continuous (fun p : Cfg × Cfg => S p.1 p.2) :=
    p4Q2IW_originalWilsonOneSlabAction_continuous H
  have hRow : Continuous (fun A : Cfg => S A B) :=
    p4Q2PX3_oneSlabAction_row_continuous H B
  have hRight : Continuous (fun p : Cfg × Cfg => S p.2 B) :=
    hRow.comp continuous_snd
  change Continuous (fun p : Cfg × Cfg => S p.1 p.2 + S p.2 B)
  exact hSlab.add hRight

/-- The original double spatial Haar really depends continuously on
its intermediate SU(2) boundary, by Bochner evaluation. -/
private theorem p4Q2PX3_integral_first_continuous
    (f : C(Cfg × Cfg, ℝ)) :
    Continuous (fun A : Cfg => ∫ X : Cfg, f (X, A) ∂haar) := by
  let v : C(Cfg, C(Cfg, ℝ)) := f.curry
  have hv : Integrable (fun X : Cfg => v X) haar :=
    v.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfun :
      (fun A : Cfg => ∫ X : Cfg, f (X, A) ∂haar) =
        (fun A : Cfg => (∫ X : Cfg, v X ∂haar) A) := by
    funext A
    rw [ContinuousMap.integral_apply hv A]
    rfl
  rw [hfun]
  exact (∫ X : Cfg, v X ∂haar).continuous

/-- The unchanged one-slab quartic Wilson kernel polynomial integrates
EXACTLY to the fourth-moment one-slab jet proved in PX. -/
theorem p4Q2PX3_originalOneSlab_integratedQuartic_eq_jet
    (beta : ℝ) (B : Cfg) :
    (∫ X : Cfg, T1 beta X B ∂haar) = J1 beta B := by
  have hS : Continuous (fun X : Cfg => S X B) :=
    p4Q2PX3_oneSlabAction_row_continuous H B
  have ht : Continuous (fun X : Cfg => beta * S X B) :=
    continuous_const.mul hS
  have hC : Continuous (fun X : Cfg => C1 beta X B) := by
    unfold p4Q2PP_originalOneSlabCubicTaylor
    exact ((continuous_const.sub ht).add ((ht.pow 2).div_const 2)).sub
      ((ht.pow 3).div_const 6)
  have hS4 : Continuous (fun X : Cfg => (S X B) ^ 4) := hS.pow 4
  have hCI : Integrable (fun X : Cfg => C1 beta X B) haar :=
    hC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hS4I : Integrable (fun X : Cfg => (S X B) ^ 4) haar :=
    hS4.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (X : Cfg) :
      T1 beta X B =
        C1 beta X B + (beta ^ 4 / 24) * (S X B) ^ 4 := by
    unfold p4Q2PX2_originalOneSlabQuarticTaylor
    ring
  have hIntegral :
      (∫ X : Cfg,
        C1 beta X B + (beta ^ 4 / 24) * (S X B) ^ 4 ∂haar) =
      (∫ X : Cfg, C1 beta X B ∂haar) +
        (beta ^ 4 / 24) * (∫ X : Cfg, (S X B) ^ 4 ∂haar) := by
    simpa only [Pi.add_apply, integral_const_mul] using
      (integral_add hCI (hS4I.const_mul (beta ^ 4 / 24)))
  calc
    (∫ X : Cfg, T1 beta X B ∂haar) =
        ∫ X : Cfg,
          C1 beta X B + (beta ^ 4 / 24) * (S X B) ^ 4 ∂haar := by
      apply integral_congr_ae
      filter_upwards with X
      exact hPoint X
    _ = (∫ X : Cfg, C1 beta X B ∂haar) +
        (beta ^ 4 / 24) * (∫ X : Cfg, (S X B) ^ 4 ∂haar) := hIntegral
    _ = J1 beta B := by
      rw [p4Q2PP3_originalOneSlab_integratedCubic_eq_jet H beta B]
      unfold p4Q2PX_originalOneSlabFormalTaylor4
        p4Q2PX_originalOneSlabFourthActionMoment
      ring

/-- The ORIGINAL two-slab quartic interacting Wilson polynomial,
integrated against BOTH unchanged spatial Haar measures, equals the
literal genuine fourth action-moment jet in PX. No posterior change. -/
theorem p4Q2PX3_originalTwoSlab_integratedQuartic_eq_jet
    (beta : ℝ) (B : Cfg) :
    (∫ A : Cfg, ∫ X : Cfg, T2 beta X A B ∂haar ∂haar) =
      J2 beta B := by
  have hQ : Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) :=
    p4Q2PX3_twoSlabAction_pair_continuous H B
  have ht : Continuous (fun p : Cfg × Cfg =>
      beta * Q p.1 p.2 B) := continuous_const.mul hQ
  have hC : Continuous (fun p : Cfg × Cfg => C2 beta p.1 p.2 B) := by
    unfold p4Q2PP_originalTwoSlabCubicTaylor
    exact ((continuous_const.sub ht).add ((ht.pow 2).div_const 2)).sub
      ((ht.pow 3).div_const 6)
  have hQ4 : Continuous (fun p : Cfg × Cfg =>
      (Q p.1 p.2 B) ^ 4) := hQ.pow 4
  let fC : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => C2 beta p.1 p.2 B), hC⟩
  let fQ4 : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (Q p.1 p.2 B) ^ 4), hQ4⟩
  have hOuterC : Integrable
      (fun A : Cfg => ∫ X : Cfg, C2 beta X A B ∂haar) haar :=
    (p4Q2PX3_integral_first_continuous H fC).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hOuterQ4 : Integrable
      (fun A : Cfg => ∫ X : Cfg, (Q X A B) ^ 4 ∂haar) haar :=
    (p4Q2PX3_integral_first_continuous H fQ4).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner (A : Cfg) :
      (∫ X : Cfg, T2 beta X A B ∂haar) =
      (∫ X : Cfg, C2 beta X A B ∂haar) +
        (beta ^ 4 / 24) * (∫ X : Cfg, (Q X A B) ^ 4 ∂haar) := by
    have hPair : Continuous (fun X : Cfg => (X, A)) :=
      continuous_id.prodMk continuous_const
    have hCI : Integrable (fun X : Cfg => C2 beta X A B) haar :=
      (hC.comp hPair).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hQI : Integrable (fun X : Cfg => (Q X A B) ^ 4) haar :=
      (hQ4.comp hPair).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hPoint (X : Cfg) :
        T2 beta X A B =
          C2 beta X A B + (beta ^ 4 / 24) * (Q X A B) ^ 4 := by
      unfold p4Q2PX2_originalTwoSlabQuarticTaylor
      ring
    calc
      (∫ X : Cfg, T2 beta X A B ∂haar) =
          ∫ X : Cfg,
            C2 beta X A B + (beta ^ 4 / 24) * (Q X A B) ^ 4 ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        exact hPoint X
      _ = (∫ X : Cfg, C2 beta X A B ∂haar) +
            (beta ^ 4 / 24) * (∫ X : Cfg, (Q X A B) ^ 4 ∂haar) := by
        simpa only [Pi.add_apply, integral_const_mul] using
          (integral_add hCI (hQI.const_mul (beta ^ 4 / 24)))
  have hOuter :
      (∫ A : Cfg,
        (∫ X : Cfg, C2 beta X A B ∂haar) +
          (beta ^ 4 / 24) * (∫ X : Cfg, (Q X A B) ^ 4 ∂haar) ∂haar) =
      (∫ A : Cfg, ∫ X : Cfg, C2 beta X A B ∂haar ∂haar) +
        (beta ^ 4 / 24) *
          (∫ A : Cfg, ∫ X : Cfg, (Q X A B) ^ 4 ∂haar ∂haar) := by
    simpa only [Pi.add_apply, integral_const_mul] using
      (integral_add hOuterC (hOuterQ4.const_mul (beta ^ 4 / 24)))
  calc
    (∫ A : Cfg, ∫ X : Cfg, T2 beta X A B ∂haar ∂haar) =
        ∫ A : Cfg,
          (∫ X : Cfg, C2 beta X A B ∂haar) +
            (beta ^ 4 / 24) * (∫ X : Cfg, (Q X A B) ^ 4 ∂haar) ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      exact hInner A
    _ = (∫ A : Cfg, ∫ X : Cfg, C2 beta X A B ∂haar ∂haar) +
          (beta ^ 4 / 24) *
            (∫ A : Cfg, ∫ X : Cfg, (Q X A B) ^ 4 ∂haar ∂haar) := hOuter
    _ = J2 beta B := by
      rw [p4Q2PP3_originalTwoSlab_integratedCubic_eq_jet H beta B]
      unfold p4Q2PX_originalTwoSlabFormalTaylor4
        p4Q2PX_originalTwoSlabFourthActionMoment
      ring

end OriginalIntegratedQuarticMoments
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX3_originalOneSlab_integratedQuartic_eq_jet
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX3_originalTwoSlab_integratedQuartic_eq_jet
