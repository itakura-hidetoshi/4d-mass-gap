import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalIntegratedFourthMomentJetsV5_PX3
import Mathlib.Tactic

/-!
# P4-Q2-PX4 — true original Wilson Haar rows with quartic jets and quintic remainder

The one-slab Wilson Haar row and the fully interacting two-slab Wilson
double-Haar row differ from their true fourth-action-moment jets
by O(beta^5) under the original SU(2) spatial Haar measure.
All middle spatial plaquettes are retained, with neither posterior
factorization nor fabricated nonzero Wilson witness.
No new axiom, sorry/admit, spectral surrogate or continuum claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PX4_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PX4_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PX4_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PX4_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PX4_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalLiteralQuinticRemainder
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "T1" => p4Q2PX2_originalOneSlabQuarticTaylor H
local notation "T2" => p4Q2PX2_originalTwoSlabQuarticTaylor H
local notation "J1" => p4Q2PX_originalOneSlabFormalTaylor4 H
local notation "J2" => p4Q2PX_originalTwoSlabFormalTaylor4 H

private theorem p4Q2PX4_oneSlabAction_row_continuous (B : Cfg) :
    Continuous (fun X : Cfg => S X B) := by
  have hPair : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have h := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
  simpa only [Function.comp_def] using h

private theorem p4Q2PX4_twoSlabAction_pair_continuous (B : Cfg) :
    Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) := by
  have hSlab : Continuous (fun p : Cfg × Cfg => S p.1 p.2) :=
    p4Q2IW_originalWilsonOneSlabAction_continuous H
  have hRow : Continuous (fun A : Cfg => S A B) :=
    p4Q2PX4_oneSlabAction_row_continuous H B
  have hRight : Continuous (fun p : Cfg × Cfg => S p.2 B) :=
    hRow.comp continuous_snd
  change Continuous (fun p : Cfg × Cfg => S p.1 p.2 + S p.2 B)
  exact hSlab.add hRight

/-- The original double spatial Haar really depends continuously on
its intermediate SU(2) boundary, by Bochner evaluation. -/
private theorem p4Q2PX4_integral_first_continuous
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

/-- The true one-slab Haar row has the exact PP2 fourth moment jet
with a uniform original-kernel quintic error. -/
theorem p4Q2PX4_originalOneSlabHaarRow_quarticJet_quinticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1) (B : Cfg) :
    ‖p4Q2IV_originalWilsonUnitHaarKernelSection H beta B -
        J1 beta B‖ ≤ ‖beta * M‖ ^ 5 := by
  have hPair : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have hS : Continuous (fun X : Cfg => S X B) :=
    p4Q2PX4_oneSlabAction_row_continuous H B
  have hK : Continuous (fun X : Cfg => K beta X B) := by
    have h := (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp hPair
    simpa only [Function.comp_def] using h
  have ht : Continuous (fun X : Cfg => beta * S X B) :=
    continuous_const.mul hS
  have hC : Continuous (fun X : Cfg => T1 beta X B) := by
    unfold p4Q2PX2_originalOneSlabQuarticTaylor
      p4Q2PP_originalOneSlabCubicTaylor
    exact (((continuous_const.sub ht).add ((ht.pow 2).div_const 2)).sub
      ((ht.pow 3).div_const 6)).add ((ht.pow 4).div_const 24)
  have hKInt : Integrable (fun X : Cfg => K beta X B) haar :=
    hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCInt : Integrable (fun X : Cfg => T1 beta X B) haar :=
    hC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSub :
      (∫ X : Cfg, K beta X B - T1 beta X B ∂haar) =
        (∫ X : Cfg, K beta X B ∂haar) -
          (∫ X : Cfg, T1 beta X B ∂haar) := by
    simpa only [Pi.sub_apply] using (integral_sub hKInt hCInt)
  have hRem := p4Q2PX2_originalOneSlabHaar_quinticRemainder_le
    H beta hsmall B
  rw [hSub, p4Q2PX3_originalOneSlab_integratedQuartic_eq_jet H beta B] at hRem
  exact hRem

/-- The actual original literal double-Haar Wilson row differs from
its genuine fourth-moment jet by at most a quartic order, uniformly
over every right spatial SU(2) configuration at fixed finite H. -/
theorem p4Q2PX4_originalTwoSlabHaarRow_quarticJet_quinticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * (2 * M)‖ ≤ 1)
    (B : Cfg) :
    ‖p4Q2PJ_originalWilsonLiteralTwoSlabKernel H beta B -
        J2 beta B‖ ≤ ‖beta * (2 * M)‖ ^ 5 := by
  have hQ : Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) :=
    p4Q2PX4_twoSlabAction_pair_continuous H B
  have ht : Continuous (fun p : Cfg × Cfg =>
      beta * Q p.1 p.2 B) := continuous_const.mul hQ
  have hC : Continuous (fun p : Cfg × Cfg =>
      T2 beta p.1 p.2 B) := by
    unfold p4Q2PX2_originalTwoSlabQuarticTaylor
      p4Q2PP_originalTwoSlabCubicTaylor
    exact (((continuous_const.sub ht).add ((ht.pow 2).div_const 2)).sub
      ((ht.pow 3).div_const 6)).add ((ht.pow 4).div_const 24)
  have hK : Continuous (fun p : Cfg × Cfg =>
      K beta p.2 B * K beta p.1 p.2) := by
    have hPair : Continuous (fun A : Cfg => (A, B)) :=
      continuous_id.prodMk continuous_const
    have hKrow : Continuous (fun A : Cfg => K beta A B) := by
      have h := (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H 2 beta).comp hPair
      simpa only [Function.comp_def] using h
    have hKright : Continuous (fun p : Cfg × Cfg => K beta p.2 B) :=
      hKrow.comp continuous_snd
    have hKpair : Continuous (fun p : Cfg × Cfg => K beta p.1 p.2) :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H 2 beta
    exact hKright.mul hKpair
  let fK : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => K beta p.2 B * K beta p.1 p.2), hK⟩
  let fC : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => T2 beta p.1 p.2 B), hC⟩
  have hOuterK : Integrable
      (fun A : Cfg =>
        ∫ X : Cfg, K beta A B * K beta X A ∂haar) haar :=
    (p4Q2PX4_integral_first_continuous H fK).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hOuterC : Integrable
      (fun A : Cfg => ∫ X : Cfg, T2 beta X A B ∂haar) haar :=
    (p4Q2PX4_integral_first_continuous H fC).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner (A : Cfg) :
      (∫ X : Cfg,
        K beta A B * K beta X A - T2 beta X A B ∂haar) =
        (∫ X : Cfg, K beta A B * K beta X A ∂haar) -
          (∫ X : Cfg, T2 beta X A B ∂haar) := by
    have hPair : Continuous (fun X : Cfg => (X, A)) :=
      continuous_id.prodMk continuous_const
    have hKI : Integrable (fun X : Cfg => K beta A B * K beta X A) haar :=
      (hK.comp hPair).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hCI : Integrable (fun X : Cfg => T2 beta X A B) haar :=
      (hC.comp hPair).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simpa only [Pi.sub_apply] using (integral_sub hKI hCI)
  have hOuter :
      (∫ A : Cfg, ∫ X : Cfg,
        K beta A B * K beta X A - T2 beta X A B ∂haar ∂haar) =
        (∫ A : Cfg, ∫ X : Cfg,
          K beta A B * K beta X A ∂haar ∂haar) -
        (∫ A : Cfg, ∫ X : Cfg, T2 beta X A B ∂haar ∂haar) := by
    calc
      (∫ A : Cfg, ∫ X : Cfg,
        K beta A B * K beta X A - T2 beta X A B ∂haar ∂haar) =
        ∫ A : Cfg,
          (∫ X : Cfg, K beta A B * K beta X A ∂haar) -
          (∫ X : Cfg, T2 beta X A B ∂haar) ∂haar := by
        apply integral_congr_ae
        filter_upwards with A
        exact hInner A
      _ = (∫ A : Cfg, ∫ X : Cfg,
            K beta A B * K beta X A ∂haar ∂haar) -
          (∫ A : Cfg, ∫ X : Cfg, T2 beta X A B ∂haar ∂haar) := by
        simpa only [Pi.sub_apply] using (integral_sub hOuterK hOuterC)
  have hRem := p4Q2PX2_originalTwoSlabDoubleHaar_quinticRemainder_le
    H beta hsmall B
  rw [hOuter, p4Q2PX3_originalTwoSlab_integratedQuartic_eq_jet H beta B] at hRem
  exact hRem

end OriginalLiteralQuinticRemainder
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX4_originalOneSlabHaarRow_quarticJet_quinticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX4_originalTwoSlabHaarRow_quarticJet_quinticRemainder_le
