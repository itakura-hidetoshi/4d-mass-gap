import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalThirdMomentFourthJetV5_PP2
import Mathlib.Tactic

/-!
# P4-Q2-PP3 — exact original one- and two-slab integrated cubic coefficients

The degree-three original SU(2) Wilson action Taylor polynomials are
integrated against the *same genuine spatial Haar*, once and twice.
The resulting expressions are exactly the original action moment
cubics from PP2 and the original PK lower moments, not substitute
posteriors. The uniform quartic remainder of PP then transfers to
the actual one- and two-slab physical Haar rows.
The intermediate Wilson spatial action remains FULL in every formula.
No nonzero quartic coefficient, third-mode rank or new axiom is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PP3_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PP3_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PP3_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PP3_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PP3_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalIntegratedCubicMoments
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
local notation "P1" => p4Q2PN_originalOneSlabQuadraticTaylor H
local notation "P2" => p4Q2PN_originalTwoSlabQuadraticTaylor H
local notation "C1" => p4Q2PP_originalOneSlabCubicTaylor H
local notation "C2" => p4Q2PP_originalTwoSlabCubicTaylor H
local notation "J1" => p4Q2PP2_originalOneSlabFormalTaylor3 H
local notation "J2" => p4Q2PP2_originalTwoSlabFormalTaylor3 H

private theorem p4Q2PP3_oneSlabAction_pair_continuous :
    Continuous (fun p : Cfg × Cfg => S p.1 p.2) :=
  p4Q2IW_originalWilsonOneSlabAction_continuous H

private theorem p4Q2PP3_twoSlabAction_pair_continuous (B : Cfg) :
    Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) := by
  unfold p4Q2PK_originalTwoSlabAction
  exact (p4Q2IW_originalWilsonOneSlabAction_continuous H).add
    ((p4Q2IW_originalWilsonOneSlabAction_continuous H).comp
      (continuous_snd.prodMk continuous_const))

/-- Bochner evaluation gives continuity of the genuine spatial Haar
integral in its remaining right-boundary configuration. -/
private theorem p4Q2PP3_integral_first_continuous (f : C(Cfg × Cfg, ℝ)) :
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

/-- Cubic original one-slab action polynomial integrates to PP2's
genuine third-order one-slab moment jet, exactly. -/
theorem p4Q2PP3_originalOneSlab_integratedCubic_eq_jet
    (beta : ℝ) (B : Cfg) :
    (∫ X : Cfg, C1 beta X B ∂haar) = J1 beta B := by
  have hPair : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have hS : Continuous (fun X : Cfg => S X B) :=
    (p4Q2PP3_oneSlabAction_pair_continuous H).comp hPair
  have ht : Continuous (fun X : Cfg => beta * S X B) :=
    continuous_const.mul hS
  have hP1 : Continuous (fun X : Cfg => P1 beta X B) := by
    unfold p4Q2PN_originalOneSlabQuadraticTaylor
    exact (continuous_const.sub ht).add ((ht.pow 2).div_const 2)
  have hS3 : Continuous (fun X : Cfg => (S X B) ^ 3) := hS.pow 3
  have hP1Int : Integrable (fun X : Cfg => P1 beta X B) haar :=
    hP1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hS3Int : Integrable (fun X : Cfg => (S X B) ^ 3) haar :=
    hS3.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (X : Cfg) :
      C1 beta X B =
        P1 beta X B - (beta ^ 3 / 6) * (S X B) ^ 3 := by
    unfold p4Q2PP_originalOneSlabCubicTaylor
      p4Q2PN_originalOneSlabQuadraticTaylor
    ring
  have hIntegral :
      (∫ X : Cfg,
        P1 beta X B - (beta ^ 3 / 6) * (S X B) ^ 3 ∂haar) =
        (∫ X : Cfg, P1 beta X B ∂haar) -
          (beta ^ 3 / 6) * (∫ X : Cfg, (S X B) ^ 3 ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub hP1Int (hS3Int.const_mul (beta ^ 3 / 6)))
  calc
    (∫ X : Cfg, C1 beta X B ∂haar) =
        ∫ X : Cfg,
          P1 beta X B - (beta ^ 3 / 6) * (S X B) ^ 3 ∂haar := by
      apply integral_congr_ae
      filter_upwards with X
      exact hPoint X
    _ = (∫ X : Cfg, P1 beta X B ∂haar) -
          (beta ^ 3 / 6) * (∫ X : Cfg, (S X B) ^ 3 ∂haar) := hIntegral
    _ = J1 beta B := by
      rw [p4Q2PO_originalOneSlab_integratedQuadratic_eq_formal H beta B]
      unfold p4Q2PP2_originalOneSlabFormalTaylor3
        p4Q2PP2_originalOneSlabThirdActionMoment
      ring

/-- The true one-slab Haar row has the exact PP2 third moment jet
with a uniform original-kernel quartic error. -/
theorem p4Q2PP3_originalOneSlabHaarRow_cubicJet_quarticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1) (B : Cfg) :
    ‖p4Q2IV_originalWilsonUnitHaarKernelSection H beta B -
        J1 beta B‖ ≤ ‖beta * M‖ ^ 4 := by
  have hPair : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have hS : Continuous (fun X : Cfg => S X B) :=
    (p4Q2PP3_oneSlabAction_pair_continuous H).comp hPair
  have hK : Continuous (fun X : Cfg => K beta X B) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp hPair
  have ht : Continuous (fun X : Cfg => beta * S X B) :=
    continuous_const.mul hS
  have hC : Continuous (fun X : Cfg => C1 beta X B) := by
    unfold p4Q2PP_originalOneSlabCubicTaylor
    exact ((continuous_const.sub ht).add ((ht.pow 2).div_const 2)).sub
      ((ht.pow 3).div_const 6)
  have hKInt : Integrable (fun X : Cfg => K beta X B) haar :=
    hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCInt : Integrable (fun X : Cfg => C1 beta X B) haar :=
    hC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSub :
      (∫ X : Cfg, K beta X B - C1 beta X B ∂haar) =
        (∫ X : Cfg, K beta X B ∂haar) -
          (∫ X : Cfg, C1 beta X B ∂haar) := by
    simpa only [Pi.sub_apply] using (integral_sub hKInt hCInt)
  have hRem := p4Q2PP_originalOneSlabHaar_quarticRemainder_le
    H beta hsmall B
  rw [hSub, p4Q2PP3_originalOneSlab_integratedCubic_eq_jet H beta B] at hRem
  exact hRem

/-- The exact two-slab degree-three polynomial integrates into the
original full double-Haar third-moment jet. This uses no independence
of the two Wilson kernels and no posterior replacement. -/
theorem p4Q2PP3_originalTwoSlab_integratedCubic_eq_jet
    (beta : ℝ) (B : Cfg) :
    (∫ A : Cfg, ∫ X : Cfg, C2 beta X A B ∂haar ∂haar) =
        J2 beta B := by
  have hQ : Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) :=
    p4Q2PP3_twoSlabAction_pair_continuous H B
  have ht : Continuous (fun p : Cfg × Cfg =>
      beta * Q p.1 p.2 B) := continuous_const.mul hQ
  have hP2 : Continuous (fun p : Cfg × Cfg =>
      P2 beta p.1 p.2 B) := by
    unfold p4Q2PN_originalTwoSlabQuadraticTaylor
    exact (continuous_const.sub ht).add ((ht.pow 2).div_const 2)
  have hQ3 : Continuous (fun p : Cfg × Cfg =>
      (Q p.1 p.2 B) ^ 3) := hQ.pow 3
  let fP2 : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => P2 beta p.1 p.2 B), hP2⟩
  let fQ3 : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (Q p.1 p.2 B) ^ 3), hQ3⟩
  have hOuterP2 : Integrable
      (fun A : Cfg => ∫ X : Cfg, P2 beta X A B ∂haar) haar :=
    (p4Q2PP3_integral_first_continuous H fP2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hOuterQ3 : Integrable
      (fun A : Cfg => ∫ X : Cfg, (Q X A B) ^ 3 ∂haar) haar :=
    (p4Q2PP3_integral_first_continuous H fQ3).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner (A : Cfg) :
      (∫ X : Cfg, C2 beta X A B ∂haar) =
        (∫ X : Cfg, P2 beta X A B ∂haar) -
          (beta ^ 3 / 6) * (∫ X : Cfg, (Q X A B) ^ 3 ∂haar) := by
    have hPair : Continuous (fun X : Cfg => (X, A)) :=
      continuous_id.prodMk continuous_const
    have hPI : Integrable (fun X : Cfg => P2 beta X A B) haar :=
      (hP2.comp hPair).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hQI : Integrable (fun X : Cfg => (Q X A B) ^ 3) haar :=
      (hQ3.comp hPair).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hPoint (X : Cfg) :
        C2 beta X A B =
          P2 beta X A B - (beta ^ 3 / 6) * (Q X A B) ^ 3 := by
      unfold p4Q2PP_originalTwoSlabCubicTaylor
        p4Q2PN_originalTwoSlabQuadraticTaylor
      ring
    calc
      (∫ X : Cfg, C2 beta X A B ∂haar) =
          ∫ X : Cfg,
            P2 beta X A B - (beta ^ 3 / 6) * (Q X A B) ^ 3 ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        exact hPoint X
      _ = (∫ X : Cfg, P2 beta X A B ∂haar) -
            (beta ^ 3 / 6) * (∫ X : Cfg, (Q X A B) ^ 3 ∂haar) := by
        simpa only [Pi.sub_apply, integral_const_mul] using
          (integral_sub hPI (hQI.const_mul (beta ^ 3 / 6)))
  have hOuter :
      (∫ A : Cfg,
        (∫ X : Cfg, P2 beta X A B ∂haar) -
          (beta ^ 3 / 6) * (∫ X : Cfg, (Q X A B) ^ 3 ∂haar) ∂haar) =
        (∫ A : Cfg, ∫ X : Cfg, P2 beta X A B ∂haar ∂haar) -
          (beta ^ 3 / 6) *
            (∫ A : Cfg, ∫ X : Cfg, (Q X A B) ^ 3 ∂haar ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub hOuterP2 (hOuterQ3.const_mul (beta ^ 3 / 6)))
  calc
    (∫ A : Cfg, ∫ X : Cfg, C2 beta X A B ∂haar ∂haar) =
        ∫ A : Cfg,
          (∫ X : Cfg, P2 beta X A B ∂haar) -
            (beta ^ 3 / 6) * (∫ X : Cfg, (Q X A B) ^ 3 ∂haar) ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      exact hInner A
    _ = (∫ A : Cfg, ∫ X : Cfg, P2 beta X A B ∂haar ∂haar) -
          (beta ^ 3 / 6) *
            (∫ A : Cfg, ∫ X : Cfg, (Q X A B) ^ 3 ∂haar ∂haar) := hOuter
    _ = J2 beta B := by
      rw [p4Q2PO2_originalTwoSlab_integratedQuadratic_eq_formal H beta B]
      unfold p4Q2PP2_originalTwoSlabFormalTaylor3
        p4Q2PP2_originalTwoSlabThirdActionMoment
      ring

/-- The actual original literal double-Haar Wilson row differs from
its genuine third-moment jet by at most a quartic order, uniformly
over every right spatial SU(2) configuration at fixed finite H. -/
theorem p4Q2PP3_originalTwoSlabHaarRow_cubicJet_quarticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * (2 * M)‖ ≤ 1)
    (B : Cfg) :
    ‖p4Q2PJ_originalWilsonLiteralTwoSlabKernel H beta B -
        J2 beta B‖ ≤ ‖beta * (2 * M)‖ ^ 4 := by
  have hQ : Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) :=
    p4Q2PP3_twoSlabAction_pair_continuous H B
  have ht : Continuous (fun p : Cfg × Cfg =>
      beta * Q p.1 p.2 B) := continuous_const.mul hQ
  have hC : Continuous (fun p : Cfg × Cfg =>
      C2 beta p.1 p.2 B) := by
    unfold p4Q2PP_originalTwoSlabCubicTaylor
    exact ((continuous_const.sub ht).add ((ht.pow 2).div_const 2)).sub
      ((ht.pow 3).div_const 6)
  have hK : Continuous (fun p : Cfg × Cfg =>
      K beta p.2 B * K beta p.1 p.2) := by
    have hLeft := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta
    have hRight : Continuous (fun p : Cfg × Cfg => K beta p.2 B) :=
      hLeft.comp (continuous_snd.prodMk continuous_const)
    exact hRight.mul hLeft
  let fK : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => K beta p.2 B * K beta p.1 p.2), hK⟩
  let fC : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => C2 beta p.1 p.2 B), hC⟩
  have hOuterK : Integrable
      (fun A : Cfg =>
        ∫ X : Cfg, K beta A B * K beta X A ∂haar) haar :=
    (p4Q2PP3_integral_first_continuous H fK).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hOuterC : Integrable
      (fun A : Cfg => ∫ X : Cfg, C2 beta X A B ∂haar) haar :=
    (p4Q2PP3_integral_first_continuous H fC).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner (A : Cfg) :
      (∫ X : Cfg,
        K beta A B * K beta X A - C2 beta X A B ∂haar) =
        (∫ X : Cfg, K beta A B * K beta X A ∂haar) -
          (∫ X : Cfg, C2 beta X A B ∂haar) := by
    have hPair : Continuous (fun X : Cfg => (X, A)) :=
      continuous_id.prodMk continuous_const
    have hKI : Integrable (fun X : Cfg => K beta A B * K beta X A) haar :=
      (hK.comp hPair).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hCI : Integrable (fun X : Cfg => C2 beta X A B) haar :=
      (hC.comp hPair).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simpa only [Pi.sub_apply] using (integral_sub hKI hCI)
  have hOuter :
      (∫ A : Cfg, ∫ X : Cfg,
        K beta A B * K beta X A - C2 beta X A B ∂haar ∂haar) =
        (∫ A : Cfg, ∫ X : Cfg,
          K beta A B * K beta X A ∂haar ∂haar) -
        (∫ A : Cfg, ∫ X : Cfg, C2 beta X A B ∂haar ∂haar) := by
    calc
      (∫ A : Cfg, ∫ X : Cfg,
        K beta A B * K beta X A - C2 beta X A B ∂haar ∂haar) =
        ∫ A : Cfg,
          (∫ X : Cfg, K beta A B * K beta X A ∂haar) -
          (∫ X : Cfg, C2 beta X A B ∂haar) ∂haar := by
        apply integral_congr_ae
        filter_upwards with A
        exact hInner A
      _ = (∫ A : Cfg, ∫ X : Cfg,
            K beta A B * K beta X A ∂haar ∂haar) -
          (∫ A : Cfg, ∫ X : Cfg, C2 beta X A B ∂haar ∂haar) := by
        simpa only [Pi.sub_apply] using (integral_sub hOuterK hOuterC)
  have hRem := p4Q2PP_originalTwoSlabDoubleHaar_quarticRemainder_le
    H beta hsmall B
  rw [hOuter, p4Q2PP3_originalTwoSlab_integratedCubic_eq_jet H beta B] at hRem
  exact hRem

end OriginalIntegratedCubicMoments
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP3_originalOneSlab_integratedCubic_eq_jet
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP3_originalOneSlabHaarRow_cubicJet_quarticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP3_originalTwoSlab_integratedCubic_eq_jet
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP3_originalTwoSlabHaarRow_cubicJet_quarticRemainder_le
