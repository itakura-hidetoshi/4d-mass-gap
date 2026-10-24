import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalQuinticExponentialSixthRemainderV5_PZ2
import Mathlib.Tactic

/-!
# P4-Q2-PZ3 — EXACT original Haar-integrated quintic Wilson moment jets

PZ2 proves the sixth-order exponential kernel remainder before and
after original Haar integration. PZ1 defines the ACTUAL genuine
one-slab and two-slab fifth Wilson moments and the corrected sixth jet.

This file identifies the quintic kernel polynomials integrated
against the ORIGINAL SU(2) spatial Haar (once and twice) with those
exact PZ1 fifth-moment jets, retaining the entire intermediate
spatial Wilson action Q(X,A,B)=S(X,A)+S(A,B).

The two-slab bridge uses the real Bochner integral continuity in the
intermediate boundary, not an independently factorized posterior.
No posterior substitution, spectral surrogate, axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ3_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ3_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ3_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ3_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ3_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalIntegratedFifthMoments
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
local notation "T4₁" => p4Q2PX2_originalOneSlabQuarticTaylor H
local notation "T4₂" => p4Q2PX2_originalTwoSlabQuarticTaylor H
local notation "T5₁" => p4Q2PZ2_originalOneSlabQuinticTaylor H
local notation "T5₂" => p4Q2PZ2_originalTwoSlabQuinticTaylor H
local notation "J5₁" => p4Q2PZ1_originalOneSlabFormalTaylor5 H
local notation "J5₂" => p4Q2PZ1_originalTwoSlabFormalTaylor5 H

private theorem p4Q2PZ3_oneSlabAction_row_continuous (B : Cfg) :
    Continuous (fun X : Cfg => S X B) := by
  have hPair : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have h := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
  simpa only [Function.comp_def] using h

private theorem p4Q2PZ3_twoSlabAction_pair_continuous (B : Cfg) :
    Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) := by
  have hSlab : Continuous (fun p : Cfg × Cfg => S p.1 p.2) :=
    p4Q2IW_originalWilsonOneSlabAction_continuous H
  have hRow : Continuous (fun A : Cfg => S A B) :=
    p4Q2PZ3_oneSlabAction_row_continuous H B
  have hRight : Continuous (fun p : Cfg × Cfg => S p.2 B) :=
    hRow.comp continuous_snd
  change Continuous (fun p : Cfg × Cfg => S p.1 p.2 + S p.2 B)
  exact hSlab.add hRight

/-- Continuity of the genuine inner Haar integral as a function
of the intermediate Wilson spatial boundary via Bochner evaluation. -/
private theorem p4Q2PZ3_integral_first_continuous
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

/-- The ORIGINAL single Haar integral of the literal quintic
Wilson kernel POLYNOMIAL is EXACTLY PZ1's one-slab fifth moment jet. -/
theorem p4Q2PZ3_originalOneSlab_integratedQuintic_eq_jet
    (beta : ℝ) (B : Cfg) :
    (∫ X : Cfg, T5₁ beta X B ∂haar) = J5₁ beta B := by
  have hS : Continuous (fun X : Cfg => S X B) :=
    p4Q2PZ3_oneSlabAction_row_continuous H B
  have ht : Continuous (fun X : Cfg => beta * S X B) :=
    continuous_const.mul hS
  have hC : Continuous (fun X : Cfg => C1 beta X B) := by
    unfold p4Q2PP_originalOneSlabCubicTaylor
    exact ((continuous_const.sub ht).add ((ht.pow 2).div_const 2)).sub
      ((ht.pow 3).div_const 6)
  have hT4 : Continuous (fun X : Cfg => T4₁ beta X B) := by
    unfold p4Q2PX2_originalOneSlabQuarticTaylor
    exact hC.add ((ht.pow 4).div_const 24)
  have hS5 : Continuous (fun X : Cfg => (S X B) ^ 5) := hS.pow 5
  have hi4 : Integrable (fun X : Cfg => T4₁ beta X B) haar :=
    hT4.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi5 : Integrable (fun X : Cfg => (S X B) ^ 5) haar :=
    hS5.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (X : Cfg) :
      T5₁ beta X B =
        T4₁ beta X B - (beta ^ 5 / 120) * (S X B) ^ 5 := by
    unfold p4Q2PZ2_originalOneSlabQuinticTaylor
    ring
  have hInt :
      (∫ X : Cfg,
        T4₁ beta X B - (beta ^ 5 / 120) * (S X B) ^ 5 ∂haar) =
      (∫ X : Cfg, T4₁ beta X B ∂haar) -
        (beta ^ 5 / 120) * (∫ X : Cfg, (S X B) ^ 5 ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub hi4 (hi5.const_mul (beta ^ 5 / 120)))
  calc
    (∫ X : Cfg, T5₁ beta X B ∂haar) =
      ∫ X : Cfg,
        T4₁ beta X B - (beta ^ 5 / 120) * (S X B) ^ 5 ∂haar := by
      apply integral_congr_ae
      filter_upwards with X
      exact hPoint X
    _ = (∫ X : Cfg, T4₁ beta X B ∂haar) -
      (beta ^ 5 / 120) * (∫ X : Cfg, (S X B) ^ 5 ∂haar) := hInt
    _ = J5₁ beta B := by
      rw [p4Q2PX3_originalOneSlab_integratedQuartic_eq_jet H beta B]
      unfold p4Q2PZ1_originalOneSlabFormalTaylor5
        p4Q2PZ1_originalOneSlabFifthActionMoment
      ring

/-- The ORIGINAL genuinely INTERACTING double spatial Haar integral
of the fifth exponential polynomial equals the original fifth
moment two-slab jet, with the full intermediate spatial action. -/
theorem p4Q2PZ3_originalTwoSlab_integratedQuintic_eq_jet
    (beta : ℝ) (B : Cfg) :
    (∫ A : Cfg, ∫ X : Cfg, T5₂ beta X A B ∂haar ∂haar) =
      J5₂ beta B := by
  have hQ : Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) :=
    p4Q2PZ3_twoSlabAction_pair_continuous H B
  have ht : Continuous (fun p : Cfg × Cfg =>
      beta * Q p.1 p.2 B) := continuous_const.mul hQ
  have hC : Continuous (fun p : Cfg × Cfg => C2 beta p.1 p.2 B) := by
    unfold p4Q2PP_originalTwoSlabCubicTaylor
    exact ((continuous_const.sub ht).add ((ht.pow 2).div_const 2)).sub
      ((ht.pow 3).div_const 6)
  have hT4 : Continuous (fun p : Cfg × Cfg => T4₂ beta p.1 p.2 B) := by
    unfold p4Q2PX2_originalTwoSlabQuarticTaylor
    exact hC.add ((ht.pow 4).div_const 24)
  have hQ5 : Continuous (fun p : Cfg × Cfg =>
      (Q p.1 p.2 B) ^ 5) := hQ.pow 5
  let fT4 : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => T4₂ beta p.1 p.2 B), hT4⟩
  let fQ5 : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (Q p.1 p.2 B) ^ 5), hQ5⟩
  have hOuterT4 : Integrable
      (fun A : Cfg => ∫ X : Cfg, T4₂ beta X A B ∂haar) haar :=
    (p4Q2PZ3_integral_first_continuous H fT4).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hOuterQ5 : Integrable
      (fun A : Cfg => ∫ X : Cfg, (Q X A B) ^ 5 ∂haar) haar :=
    (p4Q2PZ3_integral_first_continuous H fQ5).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner (A : Cfg) :
      (∫ X : Cfg, T5₂ beta X A B ∂haar) =
      (∫ X : Cfg, T4₂ beta X A B ∂haar) -
        (beta ^ 5 / 120) * (∫ X : Cfg, (Q X A B) ^ 5 ∂haar) := by
    have hPair : Continuous (fun X : Cfg => (X, A)) :=
      continuous_id.prodMk continuous_const
    have hi4 : Integrable (fun X : Cfg => T4₂ beta X A B) haar :=
      (hT4.comp hPair).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hi5 : Integrable (fun X : Cfg => (Q X A B) ^ 5) haar :=
      (hQ5.comp hPair).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hPoint (X : Cfg) :
        T5₂ beta X A B =
          T4₂ beta X A B - (beta ^ 5 / 120) * (Q X A B) ^ 5 := by
      unfold p4Q2PZ2_originalTwoSlabQuinticTaylor
      ring
    calc
      (∫ X : Cfg, T5₂ beta X A B ∂haar) =
        ∫ X : Cfg,
          T4₂ beta X A B - (beta ^ 5 / 120) * (Q X A B) ^ 5 ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        exact hPoint X
      _ = (∫ X : Cfg, T4₂ beta X A B ∂haar) -
          (beta ^ 5 / 120) * (∫ X : Cfg, (Q X A B) ^ 5 ∂haar) := by
        simpa only [Pi.sub_apply, integral_const_mul] using
          (integral_sub hi4 (hi5.const_mul (beta ^ 5 / 120)))
  have hOuter :
      (∫ A : Cfg,
        (∫ X : Cfg, T4₂ beta X A B ∂haar) -
          (beta ^ 5 / 120) * (∫ X : Cfg, (Q X A B) ^ 5 ∂haar) ∂haar) =
      (∫ A : Cfg, ∫ X : Cfg, T4₂ beta X A B ∂haar ∂haar) -
        (beta ^ 5 / 120) *
          (∫ A : Cfg, ∫ X : Cfg, (Q X A B) ^ 5 ∂haar ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub hOuterT4 (hOuterQ5.const_mul (beta ^ 5 / 120)))
  calc
    (∫ A : Cfg, ∫ X : Cfg, T5₂ beta X A B ∂haar ∂haar) =
      ∫ A : Cfg,
        (∫ X : Cfg, T4₂ beta X A B ∂haar) -
          (beta ^ 5 / 120) * (∫ X : Cfg, (Q X A B) ^ 5 ∂haar) ∂haar := by
        apply integral_congr_ae
        filter_upwards with A
        exact hInner A
    _ = (∫ A : Cfg, ∫ X : Cfg, T4₂ beta X A B ∂haar ∂haar) -
          (beta ^ 5 / 120) *
            (∫ A : Cfg, ∫ X : Cfg, (Q X A B) ^ 5 ∂haar ∂haar) := hOuter
    _ = J5₂ beta B := by
      rw [p4Q2PX3_originalTwoSlab_integratedQuartic_eq_jet H beta B]
      unfold p4Q2PZ1_originalTwoSlabFormalTaylor5
        p4Q2PZ1_originalTwoSlabFifthActionMoment
      ring

end OriginalIntegratedFifthMoments
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ3_originalOneSlab_integratedQuintic_eq_jet
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ3_originalTwoSlab_integratedQuintic_eq_jet
