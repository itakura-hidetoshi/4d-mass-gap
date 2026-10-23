import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalIntegratedTaylorWardV5_PO
import Mathlib.Tactic

/-!
# P4-Q2-PO2 — second original Wilson Haar integral coefficient identification

The genuine two-slab quadratic action polynomial is integrated first in
the left field X, then in the intermediate field A, with the FULL
original middle spatial action. Its coefficients are identified with
PK's genuine a, b, d Haar moments. Consequently PN's original physical
double-Haar remainder bounds the difference from PK's second jet.
No changed model, external posterior, assumed rank or auxiliary axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PO2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PO2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PO2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PO2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PO2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalTwoSlabIntegratedCoefficients
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H
local notation "P" => p4Q2PN_originalOneSlabQuadraticTaylor H
local notation "Q" => p4Q2PN_originalTwoSlabQuadraticTaylor H
local notation "J1" => p4Q2PK_originalOneSlabFormalTaylor2 H
local notation "J2" => p4Q2PK_originalTwoSlabFormalTaylor2 H

private theorem p4Q2PO2_actionRow_continuous (B : Cfg) :
    Continuous (fun X : Cfg => S X B) := by
  have hPair : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have h := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
  simpa only [Function.comp_def] using h

private theorem p4Q2PO2_oneSlabPolynomial_continuous (beta : ℝ) (B : Cfg) :
    Continuous (fun X : Cfg => P beta X B) := by
  have hS := p4Q2PO2_actionRow_continuous H B
  have hs : Continuous (fun X : Cfg => beta * S X B) :=
    continuous_const.mul hS
  unfold p4Q2PN_originalOneSlabQuadraticTaylor
  exact (continuous_const.sub hs).add ((hs.pow 2).div_const 2)

/-- The original squared one-slab action mean has a genuine continuous
spatial representative obtained by Bochner integration in C(Cfg,R). -/
noncomputable def p4Q2PO2_originalSecondActionMomentContinuous : C(Cfg, ℝ) :=
  let g : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (S p.1 p.2) ^ 2),
      (p4Q2IW_originalWilsonOneSlabAction_continuous H).pow 2⟩
  ∫ X : Cfg, g.curry X ∂haar

/-- Pointwise realization of the continuous second moment. -/
theorem p4Q2PO2_originalSecondActionMomentContinuous_apply (B : Cfg) :
    p4Q2PO2_originalSecondActionMomentContinuous H B = b B := by
  let g : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (S p.1 p.2) ^ 2),
      (p4Q2IW_originalWilsonOneSlabAction_continuous H).pow 2⟩
  let v : C(Cfg, C(Cfg, ℝ)) := g.curry
  have hv : Integrable (fun X : Cfg => v X) haar :=
    v.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ X : Cfg, v X ∂haar) B =
    ∫ X : Cfg, (S X B) ^ 2 ∂haar
  rw [ContinuousMap.integral_apply hv B]
  rfl

private theorem p4Q2PO2_firstActionMoment_continuous :
    Continuous (fun X : Cfg => a X) := by
  have hW : Continuous
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2) :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hEq : (fun X : Cfg => a X) =
      (fun X : Cfg => -(1 / 2 : ℝ) *
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 X -
        p4Q2JE_originalWilsonHaarZeroDerivativeConstant H) := by
    funext X
    exact p4Q2PM_originalFirstMoment_spatialWilson H X
  rw [hEq]
  exact (continuous_const.mul hW).sub continuous_const

private theorem p4Q2PO2_secondActionMoment_continuous :
    Continuous (fun X : Cfg => b X) := by
  have heq : (fun X : Cfg => b X) =
      fun X : Cfg => p4Q2PO2_originalSecondActionMomentContinuous H X := by
    funext X
    exact (p4Q2PO2_originalSecondActionMomentContinuous_apply H X).symm
  rw [heq]
  exact (p4Q2PO2_originalSecondActionMomentContinuous H).continuous

private theorem p4Q2PO2_jetOne_continuous (beta : ℝ) :
    Continuous (fun X : Cfg => J1 beta X) := by
  unfold p4Q2PK_originalOneSlabFormalTaylor2
  exact (continuous_const.add
      (continuous_const.mul (p4Q2PO2_firstActionMoment_continuous H))).add
    (continuous_const.mul (p4Q2PO2_secondActionMoment_continuous H))

/-- Integrating the ORIGINAL two-slab quadratic Wilson polynomial over
the FIRST spatial Haar variable produces exactly the one-slab jet
and the true mixed original action term. -/
theorem p4Q2PO2_originalTwoSlab_innerQuadratic
    (beta : ℝ) (A B : Cfg) :
    (∫ X : Cfg, Q beta X A B ∂haar) =
      J1 beta A + (P beta A B - 1) -
        beta ^ 2 * S A B * a A := by
  have hS := p4Q2PO2_actionRow_continuous H A
  have hSInt : Integrable (fun X : Cfg => S X A) haar :=
    hS.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPInt : Integrable (fun X : Cfg => P beta X A) haar :=
    (p4Q2PO2_oneSlabPolynomial_continuous H beta A).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp (X : Cfg) :
      Q beta X A B =
        (P beta X A + (P beta A B - 1)) +
          (beta ^ 2 * S A B) * S X A := by
    unfold p4Q2PN_originalTwoSlabQuadraticTaylor
      p4Q2PN_originalOneSlabQuadraticTaylor
      p4Q2PK_originalTwoSlabAction
    ring
  have hFirst :
      (∫ X : Cfg, P beta X A + (P beta A B - 1) ∂haar) =
        (∫ X : Cfg, P beta X A ∂haar) + (P beta A B - 1) := by
    have h := integral_add hPInt (integrable_const (P beta A B - 1))
    simpa only [Pi.add_apply, integral_const] using h
  have hBoth :
      (∫ X : Cfg,
        (P beta X A + (P beta A B - 1)) +
          (beta ^ 2 * S A B) * S X A ∂haar) =
        (∫ X : Cfg, P beta X A + (P beta A B - 1) ∂haar) +
          (beta ^ 2 * S A B) * (∫ X : Cfg, S X A ∂haar) := by
    have h := integral_add
      (hPInt.add (integrable_const (P beta A B - 1)))
      (hSInt.const_mul (beta ^ 2 * S A B))
    simpa only [Pi.add_apply, integral_const_mul] using h
  calc
    (∫ X : Cfg, Q beta X A B ∂haar) =
        ∫ X : Cfg,
          (P beta X A + (P beta A B - 1)) +
            (beta ^ 2 * S A B) * S X A ∂haar := by
      apply integral_congr_ae
      filter_upwards with X
      exact hp X
    _ = (∫ X : Cfg, P beta X A ∂haar) +
          (P beta A B - 1) +
          (beta ^ 2 * S A B) * (∫ X : Cfg, S X A ∂haar) := by
      rw [hBoth, hFirst]
    _ = J1 beta A + (P beta A B - 1) -
          beta ^ 2 * S A B * a A := by
      rw [p4Q2PO_originalOneSlab_integratedQuadratic_eq_formal H beta A]
      unfold p4Q2PK_originalOneSlabFirstActionMoment
      ring

private theorem p4Q2PO2_originalJetOne_integral (beta : ℝ) :
    (∫ A : Cfg, J1 beta A ∂haar) =
      1 + beta * (∫ A : Cfg, a A ∂haar) +
        beta ^ 2 / 2 * (∫ A : Cfg, b A ∂haar) := by
  have haInt : Integrable (fun A : Cfg => a A) haar :=
    (p4Q2PO2_firstActionMoment_continuous H).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hbInt : Integrable (fun A : Cfg => b A) haar :=
    (p4Q2PO2_secondActionMoment_continuous H).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFirst :
      (∫ A : Cfg, (1 : ℝ) + beta * a A ∂haar) =
        (∫ _A : Cfg, (1 : ℝ) ∂haar) +
          (∫ A : Cfg, beta * a A ∂haar) := by
    simpa only [Pi.add_apply] using
      (integral_add (integrable_const (1 : ℝ)) (haInt.const_mul beta))
  have hBoth :
      (∫ A : Cfg, ((1 : ℝ) + beta * a A) +
        (beta ^ 2 / 2) * b A ∂haar) =
        (∫ A : Cfg, (1 : ℝ) + beta * a A ∂haar) +
          (∫ A : Cfg, (beta ^ 2 / 2) * b A ∂haar) := by
    simpa only [Pi.add_apply] using
      (integral_add
        ((integrable_const (1 : ℝ)).add (haInt.const_mul beta))
        (hbInt.const_mul (beta ^ 2 / 2)))
  change (∫ A : Cfg,
    ((1 : ℝ) + beta * a A) + (beta ^ 2 / 2) * b A ∂haar) = _
  rw [hBoth, hFirst, integral_const_mul, integral_const_mul]
  simp
  ring

/-- Full identification of the double-integrated original two-slab
quadratic polynomial with PK's physically derived mixed-moment jet. -/
theorem p4Q2PO2_originalTwoSlab_integratedQuadratic_eq_formal
    (beta : ℝ) (B : Cfg) :
    (∫ A : Cfg, ∫ X : Cfg,
      Q beta X A B ∂haar ∂haar) = J2 beta B := by
  have hJetCont := p4Q2PO2_jetOne_continuous H beta
  have hPCont := p4Q2PO2_oneSlabPolynomial_continuous H beta B
  have hSCont := p4Q2PO2_actionRow_continuous H B
  have haCont := p4Q2PO2_firstActionMoment_continuous H
  have hJetInt : Integrable (fun A : Cfg => J1 beta A) haar :=
    hJetCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPInt : Integrable (fun A : Cfg => P beta A B) haar :=
    hPCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hMixInt : Integrable (fun A : Cfg => S A B * a A) haar :=
    (hSCont.mul haCont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInner :
      (∫ A : Cfg, ∫ X : Cfg, Q beta X A B ∂haar ∂haar) =
        (∫ A : Cfg,
          (J1 beta A + (P beta A B - 1)) -
            beta ^ 2 * (S A B * a A) ∂haar) := by
    apply integral_congr_ae
    filter_upwards with A
    rw [p4Q2PO2_originalTwoSlab_innerQuadratic H beta A B]
    ring
  have hSubP :
      (∫ A : Cfg, P beta A B - (1 : ℝ) ∂haar) =
        (∫ A : Cfg, P beta A B ∂haar) - 1 := by
    have h := integral_sub hPInt (integrable_const (1 : ℝ))
    simpa only [Pi.sub_apply, integral_const] using h
  have hAdd :
      (∫ A : Cfg, J1 beta A + (P beta A B - 1) ∂haar) =
        (∫ A : Cfg, J1 beta A ∂haar) +
          (∫ A : Cfg, P beta A B ∂haar) - 1 := by
    have h := integral_add hJetInt (hPInt.sub (integrable_const (1 : ℝ)))
    simpa only [Pi.add_apply] using
      (h.trans (by rw [hSubP]; ring))
  have hSub :
      (∫ A : Cfg, (J1 beta A + (P beta A B - 1)) -
        beta ^ 2 * (S A B * a A) ∂haar) =
        (∫ A : Cfg, J1 beta A + (P beta A B - 1) ∂haar) -
          beta ^ 2 * (∫ A : Cfg, S A B * a A ∂haar) := by
    have h := integral_sub
      (hJetInt.add (hPInt.sub (integrable_const (1 : ℝ))))
      (hMixInt.const_mul (beta ^ 2))
    simpa only [Pi.sub_apply, integral_const_mul] using h
  calc
    (∫ A : Cfg, ∫ X : Cfg, Q beta X A B ∂haar ∂haar) =
        (∫ A : Cfg, (J1 beta A + (P beta A B - 1)) -
          beta ^ 2 * (S A B * a A) ∂haar) := hInner
    _ = (∫ A : Cfg, J1 beta A ∂haar) +
          (∫ A : Cfg, P beta A B ∂haar) - 1 -
          beta ^ 2 * (∫ A : Cfg, S A B * a A ∂haar) := by
      rw [hSub, hAdd]
    _ = J2 beta B := by
      rw [p4Q2PO2_originalJetOne_integral H beta,
        p4Q2PO_originalOneSlab_integratedQuadratic_eq_formal H beta B]
      unfold p4Q2PK_originalOneSlabFormalTaylor2
        p4Q2PK_originalTwoSlabFormalTaylor2
        p4Q2PK_originalMixedTwoSlabActionMoment
      dsimp only
      ring

/-- The actual original physical two-slab double-Haar row is equal to
PK's correct second jet up to PN's proven cubic Taylor error. -/
theorem p4Q2PO2_originalTwoSlabHaarRow_eqFormal_cubicRemainder
    (beta : ℝ) (hsmall : ‖beta * (2 * M)‖ ≤ 1)
    (B : Cfg) :
    ‖p4Q2PJ_originalWilsonLiteralTwoSlabKernel H beta B -
        J2 beta B‖ ≤ ‖beta * (2 * M)‖ ^ 3 := by
  have hK (A : Cfg) :
      Continuous (fun X : Cfg => K beta A B * K beta X A) := by
    have hPair : Continuous (fun X : Cfg => (X, A)) :=
      continuous_id.prodMk continuous_const
    have hc := (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp hPair
    exact continuous_const.mul (by simpa only [Function.comp_def] using hc)
  have hQ (A : Cfg) :
      Continuous (fun X : Cfg => Q beta X A B) := by
    have hS := p4Q2PO2_actionRow_continuous H A
    have hq : Continuous (fun X : Cfg =>
        p4Q2PK_originalTwoSlabAction H X A B) := by
      unfold p4Q2PK_originalTwoSlabAction
      exact hS.add continuous_const
    have ht : Continuous (fun X : Cfg =>
        beta * p4Q2PK_originalTwoSlabAction H X A B) :=
      continuous_const.mul hq
    unfold p4Q2PN_originalTwoSlabQuadraticTaylor
    exact (continuous_const.sub ht).add ((ht.pow 2).div_const 2)
  have hKInt (A : Cfg) :
      Integrable (fun X : Cfg => K beta A B * K beta X A) haar :=
    (hK A).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQInt (A : Cfg) :
      Integrable (fun X : Cfg => Q beta X A B) haar :=
    (hQ A).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hInner (A : Cfg) :
      (∫ X : Cfg, K beta A B * K beta X A -
        Q beta X A B ∂haar) =
      (∫ X : Cfg, K beta A B * K beta X A ∂haar) -
        (∫ X : Cfg, Q beta X A B ∂haar) := by
    simpa only [Pi.sub_apply] using (integral_sub (hKInt A) (hQInt A))
  have hOriginal :
      (∫ A : Cfg, ∫ X : Cfg, K beta A B * K beta X A ∂haar ∂haar) -
        (∫ A : Cfg, ∫ X : Cfg, Q beta X A B ∂haar ∂haar) =
        (∫ A : Cfg, ∫ X : Cfg,
          K beta A B * K beta X A - Q beta X A B ∂haar ∂haar) := by
    have hOuterK : Integrable (fun A : Cfg =>
        ∫ X : Cfg, K beta A B * K beta X A ∂haar) haar := by
      have hEq : (fun A : Cfg =>
          ∫ X : Cfg, K beta A B * K beta X A ∂haar) =
          (fun A : Cfg =>
            K beta A B * p4Q2IV_originalWilsonUnitHaarKernelSection H beta A) := by
        funext A
        rw [integral_const_mul]
        rfl
      rw [hEq]
      have hKrow : Continuous (fun A : Cfg => K beta A B) := by
        have hPair : Continuous (fun A : Cfg => (A, B)) :=
          continuous_id.prodMk continuous_const
        have ht := (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
          H 2 beta).comp hPair
        simpa only [Function.comp_def] using ht
      exact (hKrow.mul
        (p4Q2IV_originalWilsonUnitHaarKernelSection_continuous H beta)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have hOuterQ : Integrable (fun A : Cfg =>
        ∫ X : Cfg, Q beta X A B ∂haar) haar := by
      have hEq : (fun A : Cfg => ∫ X : Cfg, Q beta X A B ∂haar) =
          (fun A : Cfg => J1 beta A + (P beta A B - 1) -
            beta ^ 2 * S A B * a A) := by
        funext A
        exact p4Q2PO2_originalTwoSlab_innerQuadratic H beta A B
      rw [hEq]
      have h := ((p4Q2PO2_jetOne_continuous H beta).add
          ((p4Q2PO2_oneSlabPolynomial_continuous H beta B).sub continuous_const)).sub
          ((continuous_const.mul (p4Q2PO2_actionRow_continuous H B)).mul
            (p4Q2PO2_firstActionMoment_continuous H))
      exact h.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h := integral_sub hOuterK hOuterQ
    have hRight :
        (∫ A : Cfg,
          (∫ X : Cfg, K beta A B * K beta X A ∂haar) -
            (∫ X : Cfg, Q beta X A B ∂haar) ∂haar) =
          (∫ A : Cfg, ∫ X : Cfg,
            K beta A B * K beta X A - Q beta X A B ∂haar ∂haar) := by
      apply integral_congr_ae
      filter_upwards with A
      exact (hInner A).symm
    exact (by
      rw [← hRight]
      simpa only [Pi.sub_apply] using h.symm)
  have hPN :=
    p4Q2PN_originalLiteralTwoSlabDoubleHaarRemainder_le H beta hsmall B
  change ‖(∫ A : Cfg, ∫ X : Cfg, K beta A B * K beta X A ∂haar ∂haar) -
      J2 beta B‖ ≤ _
  rw [← p4Q2PO2_originalTwoSlab_integratedQuadratic_eq_formal H beta B,
    hOriginal]
  exact hPN

end OriginalTwoSlabIntegratedCoefficients
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PO2_originalSecondActionMomentContinuous_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PO2_originalTwoSlab_innerQuadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PO2_originalTwoSlab_integratedQuadratic_eq_formal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PO2_originalTwoSlabHaarRow_eqFormal_cubicRemainder
