import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLiteralFourthOrderBoundV5_PO3
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# P4-Q2-PP — true full Wilson cubic Taylor polynomial and quartic remainder

PO proves the original Haar-integrated two-slab third-mode spatial
minor is O(beta^4), not that its coefficient is nonzero.
This file strengthens PN's one-/two-slab exponential remainder
through the cubic action term. Its two Haar integrations are the
ACTUAL unchanged SU(2) Wilson kernel, with the entire spatial Wilson
action on the intermediate boundary. The estimates are uniform for
each finite volume and each original spatial boundary configuration.
No independent posterior, assumed rank, auxiliary spectral measure,
sorry, admit or additional axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PP_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PP_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PP_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PP_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PP_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The degree-three finite exponential series has a quartic norm
remainder on the unit interval, derived from mathlib Real.exp_bound. -/
theorem p4Q2PP_realExp_cubicRemainder_le
    (x : ℝ) (hx : ‖x‖ ≤ 1) :
    ‖Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)‖ ≤ ‖x‖ ^ 4 := by
  have h := Real.exp_bound (x := x) (n := 4)
    (by simpa only [Real.norm_eq_abs] using hx) (by norm_num)
  have hSeries :
      (∑ m ∈ Finset.range 4, x ^ m / (m.factorial : ℝ)) =
        1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hSeries] at h
  norm_num at h
  have hpow : 0 ≤ |x| ^ 4 := pow_nonneg (abs_nonneg x) _
  have hb :
      |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)| ≤ |x| ^ 4 := by
    nlinarith
  simpa only [Real.norm_eq_abs] using hb

section OriginalWilsonCubics
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
local notation "Q" => p4Q2PK_originalTwoSlabAction H

/-- Cubic polynomial of the ORIGINAL full one-slab Wilson action. -/
noncomputable def p4Q2PP_originalOneSlabCubicTaylor
    (beta : ℝ) (X B : Cfg) : ℝ :=
  1 - beta * S X B + (beta * S X B) ^ 2 / 2 -
    (beta * S X B) ^ 3 / 6

/-- Cubic polynomial of the ORIGINAL full two-slab Wilson action;
the intermediate spatial plaquette field has its correct full weight. -/
noncomputable def p4Q2PP_originalTwoSlabCubicTaylor
    (beta : ℝ) (X A B : Cfg) : ℝ :=
  1 - beta * Q X A B + (beta * Q X A B) ^ 2 / 2 -
    (beta * Q X A B) ^ 3 / 6

/-- Quartic error in the literal ORIGINAL one-slab Boltzmann kernel. -/
theorem p4Q2PP_originalOneSlabKernel_quarticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1)
    (X B : Cfg) :
    ‖K beta X B - p4Q2PP_originalOneSlabCubicTaylor H beta X B‖ ≤
      ‖beta * M‖ ^ 4 := by
  have hM : 0 ≤ M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hSnonneg : 0 ≤ S X B :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by decide) X B
  have hSle : S X B ≤ M :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H 2 (by decide) X B
  have hNorm : ‖-(beta * S X B)‖ ≤ ‖beta * M‖ := by
    calc
      ‖-(beta * S X B)‖ = ‖beta‖ * S X B := by
        simp only [norm_neg, norm_mul, Real.norm_eq_abs, abs_of_nonneg hSnonneg]
      _ ≤ ‖beta‖ * M :=
        mul_le_mul_of_nonneg_left hSle (norm_nonneg _)
      _ = ‖beta * M‖ := by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hM]
  have hExp := p4Q2PP_realExp_cubicRemainder_le
    (-(beta * S X B)) (le_trans hNorm hsmall)
  have hPolynomial :
      1 - beta * S X B + (beta * S X B) ^ 2 / 2 -
        (beta * S X B) ^ 3 / 6 =
        1 + (-(beta * S X B)) + (-(beta * S X B)) ^ 2 / 2 +
          (-(beta * S X B)) ^ 3 / 6 := by
    ring
  change ‖K beta X B -
    (1 - beta * S X B + (beta * S X B) ^ 2 / 2 -
      (beta * S X B) ^ 3 / 6)‖ ≤ _
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    hPolynomial]
  exact hExp.trans (pow_le_pow_left₀ (norm_nonneg _) hNorm 4)

/-- Quartic error for two genuinely adjacent interacting Wilson slabs. -/
theorem p4Q2PP_originalTwoSlabKernel_quarticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * (2 * M)‖ ≤ 1)
    (X A B : Cfg) :
    ‖K beta A B * K beta X A -
      p4Q2PP_originalTwoSlabCubicTaylor H beta X A B‖ ≤
        ‖beta * (2 * M)‖ ^ 4 := by
  have hM : 0 ≤ M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hQnonneg : 0 ≤ Q X A B :=
    p4Q2PK_originalTwoSlabAction_nonneg H X A B
  have hQle : Q X A B ≤ 2 * M :=
    p4Q2PN_originalTwoSlabAction_le_twoBudget H X A B
  have hNorm : ‖-(beta * Q X A B)‖ ≤ ‖beta * (2 * M)‖ := by
    calc
      ‖-(beta * Q X A B)‖ = ‖beta‖ * Q X A B := by
        simp only [norm_neg, norm_mul, Real.norm_eq_abs, abs_of_nonneg hQnonneg]
      _ ≤ ‖beta‖ * (2 * M) :=
        mul_le_mul_of_nonneg_left hQle (norm_nonneg _)
      _ = ‖beta * (2 * M)‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg hM]
  have hExp := p4Q2PP_realExp_cubicRemainder_le
    (-(beta * Q X A B)) (le_trans hNorm hsmall)
  have hPolynomial :
      1 - beta * Q X A B + (beta * Q X A B) ^ 2 / 2 -
        (beta * Q X A B) ^ 3 / 6 =
        1 + (-(beta * Q X A B)) + (-(beta * Q X A B)) ^ 2 / 2 +
          (-(beta * Q X A B)) ^ 3 / 6 := by
    ring
  change ‖K beta A B * K beta X A -
    (1 - beta * Q X A B + (beta * Q X A B) ^ 2 / 2 -
      (beta * Q X A B) ^ 3 / 6)‖ ≤ _
  rw [p4Q2PK_originalTwoSlabKernel_product_eq_exp H beta X A B,
    hPolynomial]
  exact hExp.trans (pow_le_pow_left₀ (norm_nonneg _) hNorm 4)

/-- Same reference Haar and original action, integrated once. -/
theorem p4Q2PP_originalOneSlabHaar_quarticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1)
    (B : Cfg) :
    ‖∫ X : Cfg,
      K beta X B - p4Q2PP_originalOneSlabCubicTaylor H beta X B ∂haar‖ ≤
        ‖beta * M‖ ^ 4 := by
  have hb :=
    norm_integral_le_of_norm_le_const (μ := haar)
      (Filter.Eventually.of_forall
        (fun X => p4Q2PP_originalOneSlabKernel_quarticRemainder_le
          H beta hsmall X B))
  simpa using hb

/-- Same physical two-slab Haar expression, integrated twice. -/
theorem p4Q2PP_originalTwoSlabDoubleHaar_quarticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * (2 * M)‖ ≤ 1)
    (B : Cfg) :
    ‖∫ A : Cfg, ∫ X : Cfg,
      K beta A B * K beta X A -
        p4Q2PP_originalTwoSlabCubicTaylor H beta X A B ∂haar ∂haar‖ ≤
        ‖beta * (2 * M)‖ ^ 4 := by
  have hInner (A : Cfg) :
      ‖∫ X : Cfg,
        K beta A B * K beta X A -
          p4Q2PP_originalTwoSlabCubicTaylor H beta X A B ∂haar‖ ≤
            ‖beta * (2 * M)‖ ^ 4 := by
    have hb :=
      norm_integral_le_of_norm_le_const (μ := haar)
        (Filter.Eventually.of_forall
          (fun X => p4Q2PP_originalTwoSlabKernel_quarticRemainder_le
            H beta hsmall X A B))
    simpa using hb
  have hb :=
    norm_integral_le_of_norm_le_const (μ := haar)
      (Filter.Eventually.of_forall hInner)
  simpa using hb

end OriginalWilsonCubics
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP_realExp_cubicRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP_originalOneSlabKernel_quarticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP_originalTwoSlabKernel_quarticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP_originalOneSlabHaar_quarticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP_originalTwoSlabDoubleHaar_quarticRemainder_le
