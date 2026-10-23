import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonCubicWardVanishingV5_PM
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# P4-Q2-PN — true Wilson one- and two-slab quadratic Taylor remainder

PM establishes the exact cancellation of the cubic obstruction in the
FORMAL three-spatial-boundary minor. To transfer that to the LITERAL
Wilson Haar-integrated kernel requires a uniform order-three remainder.

This file proves finite-volume estimates directly for the UNCHANGED
complete physical SU(2) Wilson kernels

  K_beta(X,B) = exp (-beta * S(X,B))
  K_beta(A,B) K_beta(X,A) = exp (-beta * [S(X,A)+S(A,B)]).

The intermediate boundary carries the FULL spatial plaquette action;
both spatial halfweights and both temporal crossings remain intact.
The second expression is bounded by twice the ORIGINAL one-slab
action budget, yielding an explicit uniform cubic remainder for
the authentic double spatial Haar integral without new posterior,
spectral measure, rank assumption, sorry or admit.

The integrated quadratic-polynomial coefficients are not yet
identified with PK's first/second Haar moments in this file.
A literal O(beta^4) determinant estimate needs that coefficient
identification and PM's Ward cancellation, and remains OPEN here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PN_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PN_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PN_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PN_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PN_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- A scalar cubic remainder from mathlib's finite exponential-series
bound (range 3), valid on the two-sided real unit interval. -/
theorem p4Q2PN_realExp_quadraticRemainder_le (x : ℝ) (hx : ‖x‖ ≤ 1) :
    ‖Real.exp x - (1 + x + x ^ 2 / 2)‖ ≤ ‖x‖ ^ 3 := by
  have h := Real.exp_bound (x := x) (n := 3)
    (by simpa only [Real.norm_eq_abs] using hx) (by norm_num)
  have hSeries :
      (∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ)) =
        1 + x + x ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
    <;> ring
  rw [hSeries] at h
  norm_num at h
  have hpow : 0 ≤ |x| ^ 3 := pow_nonneg (abs_nonneg x) _
  have hsmall : |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 := by
    nlinarith
  simpa only [Real.norm_eq_abs] using hsmall

section OriginalFiniteVolumeWilson
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

/-- Exact degree-two polynomial of the ACTUAL complete one-slab action. -/
noncomputable def p4Q2PN_originalOneSlabQuadraticTaylor
    (beta : ℝ) (X B : Cfg) : ℝ :=
  1 - beta * S X B + (beta * S X B) ^ 2 / 2

/-- Exact degree-two polynomial of the ACTUAL complete two-slab action.
The full internal W(A) is retained via PK's already verified Q. -/
noncomputable def p4Q2PN_originalTwoSlabQuadraticTaylor
    (beta : ℝ) (X A B : Cfg) : ℝ :=
  1 - beta * Q X A B + (beta * Q X A B) ^ 2 / 2

/-- The original two-slab physical action is at most twice the authentic
one-slab action budget, uniformly over ALL SU(2) spatial boundaries. -/
theorem p4Q2PN_originalTwoSlabAction_le_twoBudget (X A B : Cfg) :
    Q X A B ≤ 2 * M := by
  have h₁ : S X A ≤ M :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H 2 (by decide) X A
  have h₂ : S A B ≤ M :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H 2 (by decide) A B
  unfold p4Q2PK_originalTwoSlabAction
  linarith

/-- Cubic norm remainder of the actual original one-slab Wilson kernel,
uniform in both SU(2) spatial boundaries, for a two-sided small beta. -/
theorem p4Q2PN_originalOneSlabKernel_cubicRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1) (X B : Cfg) :
    ‖K beta X B - p4Q2PN_originalOneSlabQuadraticTaylor H beta X B‖ ≤
      ‖beta * M‖ ^ 3 := by
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
        simp only [norm_neg, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg hSnonneg]
      _ ≤ ‖beta‖ * M :=
        mul_le_mul_of_nonneg_left hSle (norm_nonneg _)
      _ = ‖beta * M‖ := by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hM]
  have hExp :=
    p4Q2PN_realExp_quadraticRemainder_le
      (-beta * S X B)
      (le_trans (by simpa only [neg_mul] using hNorm) hsmall)
  have hPolynomial :
      1 - beta * S X B + (beta * S X B) ^ 2 / 2 =
        1 + (-beta * S X B) + (-beta * S X B) ^ 2 / 2 := by
    ring
  change ‖K beta X B -
    (1 - beta * S X B + (beta * S X B) ^ 2 / 2)‖ ≤ _
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    hPolynomial]
  have hPow : ‖-beta * S X B‖ ^ 3 ≤ ‖beta * M‖ ^ 3 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hNorm 3
    simpa only [neg_mul] using h
  exact hExp.trans hPow

/-- Cubic norm remainder for TWO literal full interacting Wilson slabs.
There is NO modified transfer, independent posterior or action truncation. -/
theorem p4Q2PN_originalTwoSlabKernel_cubicRemainder_le
    (beta : ℝ) (hsmall : ‖beta * (2 * M)‖ ≤ 1)
    (X A B : Cfg) :
    ‖K beta A B * K beta X A -
      p4Q2PN_originalTwoSlabQuadraticTaylor H beta X A B‖ ≤
        ‖beta * (2 * M)‖ ^ 3 := by
  have hM : 0 ≤ M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hQnonneg : 0 ≤ Q X A B :=
    p4Q2PK_originalTwoSlabAction_nonneg H X A B
  have hQle : Q X A B ≤ 2 * M :=
    p4Q2PN_originalTwoSlabAction_le_twoBudget H X A B
  have hNorm : ‖-(beta * Q X A B)‖ ≤ ‖beta * (2 * M)‖ := by
    calc
      ‖-(beta * Q X A B)‖ = ‖beta‖ * Q X A B := by
        simp only [norm_neg, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg hQnonneg]
      _ ≤ ‖beta‖ * (2 * M) :=
        mul_le_mul_of_nonneg_left hQle (norm_nonneg _)
      _ = ‖beta * (2 * M)‖ := by
        simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM]
  have hExp :=
    p4Q2PN_realExp_quadraticRemainder_le
      (-(beta * Q X A B)) (le_trans hNorm hsmall)
  have hPolynomial :
      1 - beta * Q X A B + (beta * Q X A B) ^ 2 / 2 =
        1 + (-(beta * Q X A B)) + (-(beta * Q X A B)) ^ 2 / 2 := by
    ring
  change ‖K beta A B * K beta X A -
    (1 - beta * Q X A B + (beta * Q X A B) ^ 2 / 2)‖ ≤ _
  rw [p4Q2PK_originalTwoSlabKernel_product_eq_exp H beta X A B,
    hPolynomial]
  exact hExp.trans (pow_le_pow_left₀ (norm_nonneg _) hNorm 3)

/-- A true, unmodified double-Haar remainder integral for the original
two-slab Wilson kernel and its ORIGINAL quadratic action jet. -/
noncomputable def p4Q2PN_originalLiteralTwoSlabDoubleHaarRemainder
    (beta : ℝ) (B : Cfg) : ℝ :=
  ∫ A : Cfg, ∫ X : Cfg,
    (K beta A B * K beta X A -
      p4Q2PN_originalTwoSlabQuadraticTaylor H beta X A B) ∂haar ∂haar

/-- The genuine TWO-FOLD original spatial Haar integral inherits the
uniform cubic remainder: no partial posterior is substituted. The
bound applies simultaneously to all actual right-boundary SU(2) fields. -/
theorem p4Q2PN_originalLiteralTwoSlabDoubleHaarRemainder_le
    (beta : ℝ) (hsmall : ‖beta * (2 * M)‖ ≤ 1)
    (B : Cfg) :
    ‖p4Q2PN_originalLiteralTwoSlabDoubleHaarRemainder H beta B‖ ≤
      ‖beta * (2 * M)‖ ^ 3 := by
  have hInner (A : Cfg) :
      ‖∫ X : Cfg, K beta A B * K beta X A -
        p4Q2PN_originalTwoSlabQuadraticTaylor H beta X A B ∂haar‖ ≤
          ‖beta * (2 * M)‖ ^ 3 := by
    have hb :=
      norm_integral_le_of_norm_le_const (μ := haar)
        (Filter.Eventually.of_forall
          (fun X => p4Q2PN_originalTwoSlabKernel_cubicRemainder_le
            H beta hsmall X A B))
    simpa using hb
  unfold p4Q2PN_originalLiteralTwoSlabDoubleHaarRemainder
  have hb :=
    norm_integral_le_of_norm_le_const (μ := haar)
      (Filter.Eventually.of_forall hInner)
  simpa using hb

/-- The same cubic bound for the actual original ONE-FOLD Haar row.
It is a genuine analytic strengthening of JF's first-order quadratic
estimate, now through the entire quadratic Wilson action jet. -/
theorem p4Q2PN_originalLiteralOneSlabHaarRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1) (B : Cfg) :
    ‖∫ X : Cfg, K beta X B -
        p4Q2PN_originalOneSlabQuadraticTaylor H beta X B ∂haar‖ ≤
      ‖beta * M‖ ^ 3 := by
  have hb :=
    norm_integral_le_of_norm_le_const (μ := haar)
      (Filter.Eventually.of_forall
        (fun X => p4Q2PN_originalOneSlabKernel_cubicRemainder_le
          H beta hsmall X B))
  simpa using hb

end OriginalFiniteVolumeWilson
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PN_realExp_quadraticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PN_originalTwoSlabAction_le_twoBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PN_originalOneSlabKernel_cubicRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PN_originalTwoSlabKernel_cubicRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PN_originalLiteralTwoSlabDoubleHaarRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PN_originalLiteralOneSlabHaarRemainder_le
