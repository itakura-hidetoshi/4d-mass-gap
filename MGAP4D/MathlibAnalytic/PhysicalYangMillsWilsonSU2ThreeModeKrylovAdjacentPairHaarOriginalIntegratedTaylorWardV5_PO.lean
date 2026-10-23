import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoSlabDoubleHaarCubicRemainderV5_PN
import Mathlib.Tactic

/-!
# P4-Q2-PO — identify the original integrated Wilson Taylor coefficients

The authentic one-slab spatial-Haar Taylor polynomial is integrated
exactly and identified with the existing PK moment jet. This is a
necessary step in transporting the PM Ward cancellation from the
formal moment minor into the literal Wilson kernel. The original
Wilson SU(2) action, Gauss-law physical transfer and fixed reference
Haar are not modified. Higher-order minor control is addressed only
after the two-slab integral identity is established.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PO_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PO_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PO_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PO_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PO_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Polynomial integration over a genuine probability measure, including
both first and second moments with their correct factors. -/
theorem p4Q2PO_integral_quadratic
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (beta : ℝ) :
    (∫ x, (1 : ℝ) - beta * f x + (beta * f x) ^ 2 / 2 ∂μ) =
      1 - beta * (∫ x, f x ∂μ) +
        beta ^ 2 / 2 * (∫ x, f x ^ 2 ∂μ) := by
  have hp (x : α) :
      (1 : ℝ) - beta * f x + (beta * f x) ^ 2 / 2 =
        (1 + (-beta) * f x) + (beta ^ 2 / 2) * f x ^ 2 := by
    ring
  have hfirst :
      (∫ x, (1 : ℝ) + (-beta) * f x ∂μ) =
        (∫ _x : α, (1 : ℝ) ∂μ) +
          (∫ x, (-beta) * f x ∂μ) := by
    simpa only [Pi.add_apply] using
      (integral_add (integrable_const (1 : ℝ)) (hf.const_mul (-beta)))
  have hsum :
      (∫ x, ((1 : ℝ) + (-beta) * f x) +
          (beta ^ 2 / 2) * f x ^ 2 ∂μ) =
        (∫ x, (1 : ℝ) + (-beta) * f x ∂μ) +
          (∫ x, (beta ^ 2 / 2) * f x ^ 2 ∂μ) := by
    simpa only [Pi.add_apply] using
      (integral_add
        ((integrable_const (1 : ℝ)).add (hf.const_mul (-beta)))
        (hf2.const_mul (beta ^ 2 / 2)))
  calc
    (∫ x, (1 : ℝ) - beta * f x + (beta * f x) ^ 2 / 2 ∂μ) =
        ∫ x, ((1 : ℝ) + (-beta) * f x) +
          (beta ^ 2 / 2) * f x ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          exact hp x
    _ = (∫ x, (1 : ℝ) + (-beta) * f x ∂μ) +
          (∫ x, (beta ^ 2 / 2) * f x ^ 2 ∂μ) := hsum
    _ = 1 - beta * (∫ x, f x ∂μ) +
          beta ^ 2 / 2 * (∫ x, f x ^ 2 ∂μ) := by
          rw [hfirst, integral_const_mul, integral_const_mul]
          simp only [integral_const]
          simp
          ring

section OriginalIntegratedTaylor
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

private theorem p4Q2PO_oneSlabAction_row_continuous (B : Cfg) :
    Continuous (fun X : Cfg => S X B) := by
  have hPair : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have h := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
  simpa only [Function.comp_def] using h

/-- Exact, not merely formal, identity of the integral of the ORIGINAL
one-slab quadratic Boltzmann polynomial with PK's Haar moment jet. -/
theorem p4Q2PO_originalOneSlab_integratedQuadratic_eq_formal
    (beta : ℝ) (B : Cfg) :
    (∫ X : Cfg,
      p4Q2PN_originalOneSlabQuadraticTaylor H beta X B ∂haar) =
        p4Q2PK_originalOneSlabFormalTaylor2 H beta B := by
  have hS := p4Q2PO_oneSlabAction_row_continuous H B
  have hSInt : Integrable (fun X : Cfg => S X B) haar :=
    hS.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hS2Int : Integrable (fun X : Cfg => (S X B) ^ 2) haar :=
    (hS.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := p4Q2PO_integral_quadratic haar
    (fun X : Cfg => S X B) hSInt hS2Int beta
  unfold p4Q2PK_originalOneSlabFormalTaylor2
    p4Q2PK_originalOneSlabFirstActionMoment
    p4Q2PK_originalOneSlabSecondActionMoment
    p4Q2PN_originalOneSlabQuadraticTaylor
  rw [h]
  ring

/-- The exact original one-slab Haar row therefore has PK's proper
quadratic Taylor jet with PN's uniform cubic norm remainder. -/
theorem p4Q2PO_originalOneSlabHaarRow_eqFormal_cubicRemainder
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1) (B : Cfg) :
    ‖p4Q2IV_originalWilsonUnitHaarKernelSection H beta B -
        p4Q2PK_originalOneSlabFormalTaylor2 H beta B‖ ≤
        ‖beta * M‖ ^ 3 := by
  have hS := p4Q2PO_oneSlabAction_row_continuous H B
  have hK : Continuous (fun X : Cfg => K beta X B) := by
    have hPair : Continuous (fun X : Cfg => (X, B)) :=
      continuous_id.prodMk continuous_const
    have h := (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp hPair
    simpa only [Function.comp_def] using h
  have hBetaS : Continuous (fun X : Cfg => beta * S X B) :=
    continuous_const.mul hS
  have hP : Continuous
      (fun X : Cfg => p4Q2PN_originalOneSlabQuadraticTaylor H beta X B) := by
    unfold p4Q2PN_originalOneSlabQuadraticTaylor
    exact (continuous_const.sub hBetaS).add
      ((hBetaS.pow 2).div_const 2)
  have hKInt : Integrable (fun X : Cfg => K beta X B) haar :=
    hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPInt : Integrable
      (fun X : Cfg => p4Q2PN_originalOneSlabQuadraticTaylor H beta X B) haar :=
    hP.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSub :
      (∫ X : Cfg,
        K beta X B - p4Q2PN_originalOneSlabQuadraticTaylor H beta X B ∂haar) =
        (∫ X : Cfg, K beta X B ∂haar) -
          (∫ X : Cfg,
            p4Q2PN_originalOneSlabQuadraticTaylor H beta X B ∂haar) := by
    simpa only [Pi.sub_apply] using (integral_sub hKInt hPInt)
  have hReal :=
    p4Q2PN_originalLiteralOneSlabHaarRemainder_le H beta hsmall B
  rw [hSub, p4Q2PO_originalOneSlab_integratedQuadratic_eq_formal H beta B] at hReal
  exact hReal

end OriginalIntegratedTaylor
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PO_integral_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PO_originalOneSlab_integratedQuadratic_eq_formal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PO_originalOneSlabHaarRow_eqFormal_cubicRemainder
