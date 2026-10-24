import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourthActionMomentsFifthJetV5_PX
import Mathlib.Tactic

/-!
# P4-Q2-PX2 — original Wilson quartic exponential and genuine fifth-order kernel remainders

On the unit interval, the degree-four real exponential Taylor
polynomial has a fifth-order remainder, proved from Mathlib's
Real.exp_bound, not assumed.

Applied to the UNCHANGED original SU(2) Wilson one-slab
S(X,B) and the fully interacting two-slab Q(X,A,B), including
the entire intermediate spatial Wilson plaquette action, the
same bound holds for the literal kernels. We also integrate
the pointwise bounds against the ORIGINAL normalized spatial
Haar, once and twice, with no independent-posterior replacement.

This is an analytic fifth-order bound for actual quartic action
kernel polynomials. Identifying the Haar-integrated polynomials
with PX's fourth-moment jets, and obtaining sixth-order error of
the literal three-configuration minor, are separate next steps.
No spectral surrogate, Dobrushin, nonzero coefficient/rank
assumption, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PX2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PX2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PX2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PX2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PX2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- True degree-four exponential series: the fifth remainder bound
for all real x with |x| ≤ 1, derived from Mathlib Real.exp_bound. -/
theorem p4Q2PX2_realExp_quarticRemainder_le
    (x : ℝ) (hx : ‖x‖ ≤ 1) :
    ‖Real.exp x -
      (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24)‖ ≤
      ‖x‖ ^ 5 := by
  have h := Real.exp_bound (x := x) (n := 5)
    (by simpa only [Real.norm_eq_abs] using hx) (by norm_num)
  have hSeries :
      (∑ m ∈ Finset.range 5, x ^ m / (m.factorial : ℝ)) =
        1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hSeries] at h
  norm_num at h
  have hpow : 0 ≤ |x| ^ 5 := pow_nonneg (abs_nonneg x) _
  have hb :
      |Real.exp x -
        (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24)| ≤ |x| ^ 5 := by
    nlinarith
  simpa only [Real.norm_eq_abs] using hb

section GenuineOriginalWilsonQuarticKernel
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

/-- The full original one-slab Wilson action's quartic exponential
Taylor polynomial, including both spatial halfweights. -/
noncomputable def p4Q2PX2_originalOneSlabQuarticTaylor
    (beta : ℝ) (X B : Cfg) : ℝ :=
  p4Q2PP_originalOneSlabCubicTaylor H beta X B +
    (beta * S X B) ^ 4 / 24

/-- The unchanged interacting two-slab action's quartic exponential
polynomial: Q includes the full intermediate spatial plaquette action. -/
noncomputable def p4Q2PX2_originalTwoSlabQuarticTaylor
    (beta : ℝ) (X A B : Cfg) : ℝ :=
  p4Q2PP_originalTwoSlabCubicTaylor H beta X A B +
    (beta * Q X A B) ^ 4 / 24

/-- Fifth-order remainder for the genuine original single-slab
SU(2) Wilson kernel under its same global action budget. -/
theorem p4Q2PX2_originalOneSlabKernel_quinticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1)
    (X B : Cfg) :
    ‖K beta X B -
      p4Q2PX2_originalOneSlabQuarticTaylor H beta X B‖ ≤
      ‖beta * M‖ ^ 5 := by
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
  have hExp := p4Q2PX2_realExp_quarticRemainder_le
    (-(beta * S X B)) (le_trans hNorm hsmall)
  have hPolynomial :
      p4Q2PX2_originalOneSlabQuarticTaylor H beta X B =
        1 + (-(beta * S X B)) + (-(beta * S X B)) ^ 2 / 2 +
          (-(beta * S X B)) ^ 3 / 6 +
          (-(beta * S X B)) ^ 4 / 24 := by
    unfold p4Q2PX2_originalOneSlabQuarticTaylor
      p4Q2PP_originalOneSlabCubicTaylor
    ring
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    hPolynomial]
  exact hExp.trans (pow_le_pow_left₀ (norm_nonneg _) hNorm 5)

/-- Fifth-order remainder for the fully interacting original SU(2)
two-slab Wilson kernel before either genuine Haar integration. -/
theorem p4Q2PX2_originalTwoSlabKernel_quinticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * (2 * M)‖ ≤ 1)
    (X A B : Cfg) :
    ‖K beta A B * K beta X A -
      p4Q2PX2_originalTwoSlabQuarticTaylor H beta X A B‖ ≤
      ‖beta * (2 * M)‖ ^ 5 := by
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
  have hExp := p4Q2PX2_realExp_quarticRemainder_le
    (-(beta * Q X A B)) (le_trans hNorm hsmall)
  have hPolynomial :
      p4Q2PX2_originalTwoSlabQuarticTaylor H beta X A B =
        1 + (-(beta * Q X A B)) + (-(beta * Q X A B)) ^ 2 / 2 +
          (-(beta * Q X A B)) ^ 3 / 6 +
          (-(beta * Q X A B)) ^ 4 / 24 := by
    unfold p4Q2PX2_originalTwoSlabQuarticTaylor
      p4Q2PP_originalTwoSlabCubicTaylor
    ring
  rw [p4Q2PK_originalTwoSlabKernel_product_eq_exp H beta X A B,
    hPolynomial]
  exact hExp.trans (pow_le_pow_left₀ (norm_nonneg _) hNorm 5)

/-- Quintic error after the original single spatial Haar integration. -/
theorem p4Q2PX2_originalOneSlabHaar_quinticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1)
    (B : Cfg) :
    ‖∫ X : Cfg,
      K beta X B -
        p4Q2PX2_originalOneSlabQuarticTaylor H beta X B ∂haar‖ ≤
        ‖beta * M‖ ^ 5 := by
  have hb :=
    norm_integral_le_of_norm_le_const (μ := haar)
      (Filter.Eventually.of_forall
        (fun X => p4Q2PX2_originalOneSlabKernel_quinticRemainder_le
          H beta hsmall X B))
  simpa using hb

/-- Quintic error after both exact spatial Haar integrals, retaining
the full original Wilson intermediate-slice interaction. -/
theorem p4Q2PX2_originalTwoSlabDoubleHaar_quinticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * (2 * M)‖ ≤ 1)
    (B : Cfg) :
    ‖∫ A : Cfg, ∫ X : Cfg,
      K beta A B * K beta X A -
        p4Q2PX2_originalTwoSlabQuarticTaylor H beta X A B ∂haar ∂haar‖ ≤
        ‖beta * (2 * M)‖ ^ 5 := by
  have hInner (A : Cfg) :
      ‖∫ X : Cfg,
        K beta A B * K beta X A -
          p4Q2PX2_originalTwoSlabQuarticTaylor H beta X A B ∂haar‖ ≤
          ‖beta * (2 * M)‖ ^ 5 := by
    have hb :=
      norm_integral_le_of_norm_le_const (μ := haar)
        (Filter.Eventually.of_forall
          (fun X => p4Q2PX2_originalTwoSlabKernel_quinticRemainder_le
            H beta hsmall X A B))
    simpa using hb
  have hb :=
    norm_integral_le_of_norm_le_const (μ := haar)
      (Filter.Eventually.of_forall hInner)
  simpa using hb

end GenuineOriginalWilsonQuarticKernel
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX2_realExp_quarticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX2_originalOneSlabKernel_quinticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX2_originalTwoSlabKernel_quinticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX2_originalOneSlabHaar_quinticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX2_originalTwoSlabDoubleHaar_quinticRemainder_le
