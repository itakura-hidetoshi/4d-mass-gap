import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSixthFifthMomentJetV5_PZ1
import Mathlib.Tactic

/-!
# P4-Q2-PZ2 — literal original Wilson quintic Taylor / sixth remainder

For the UNCHANGED original SU(2) one-slab S(X,B) and genuinely
interacting two-slab Q(X,A,B)=S(X,A)+S(A,B), prove Mathlib-based
sixth-order pointwise exponential Taylor remainder estimates for
the degree-five polynomial (including the genuine 1/5! coefficient),
with the NEGATIVE fifth power
required by e^(-beta*S).

Integrate against the original normalized spatial Haar reference,
one and two times. The full spatial Wilson action in the intermediate
slice remains in Q, with no independent/posterior factorization.

This is an analytic bound for the actual kernel POLYNOMIALS; the
separate identification of their integrals with PZ1's fifth-moment
jet and the seventh-order literal minor stability are not claimed.

No sorry/admit, new axiom, Dobrushin model or spectral surrogate.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Uniform real quintic exponential remainder, deduced from Mathlib
Real.exp_bound rather than introduced as an analytic assumption. -/
theorem p4Q2PZ2_realExp_quinticRemainder_le
    (x : ℝ) (hx : ‖x‖ ≤ 1) :
    ‖Real.exp x -
      (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 +
        x ^ 5 / 120)‖ ≤ ‖x‖ ^ 6 := by
  have h := Real.exp_bound (x := x) (n := 6)
    (by simpa only [Real.norm_eq_abs] using hx) (by norm_num)
  have hSeries :
      (∑ m ∈ Finset.range 6, x ^ m / (m.factorial : ℝ)) =
        1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 +
          x ^ 5 / 120 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hSeries] at h
  norm_num at h
  have hpow : 0 ≤ |x| ^ 6 := pow_nonneg (abs_nonneg x) _
  have hb :
      |Real.exp x -
        (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 +
          x ^ 5 / 120)| ≤ |x| ^ 6 := by
    nlinarith
  simpa only [Real.norm_eq_abs] using hb

section OriginalQuinticWilsonKernel
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

/-- Genuine original one-slab Wilson exponential fifth Taylor polynomial. -/
noncomputable def p4Q2PZ2_originalOneSlabQuinticTaylor
    (beta : ℝ) (X B : Cfg) : ℝ :=
  p4Q2PX2_originalOneSlabQuarticTaylor H beta X B -
    (beta * S X B) ^ 5 / 120

/-- Genuine original fully interacting two-slab exponential fifth polynomial. -/
noncomputable def p4Q2PZ2_originalTwoSlabQuinticTaylor
    (beta : ℝ) (X A B : Cfg) : ℝ :=
  p4Q2PX2_originalTwoSlabQuarticTaylor H beta X A B -
    (beta * Q X A B) ^ 5 / 120

/-- The ACTUAL one-slab Wilson kernel is sixth-order close to its
quintic original-action Taylor polynomial. -/
theorem p4Q2PZ2_originalOneSlabKernel_sixthRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1)
    (X B : Cfg) :
    ‖K beta X B -
      p4Q2PZ2_originalOneSlabQuinticTaylor H beta X B‖ ≤
      ‖beta * M‖ ^ 6 := by
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
  have hExp := p4Q2PZ2_realExp_quinticRemainder_le
    (-(beta * S X B)) (le_trans hNorm hsmall)
  have hPolynomial :
      p4Q2PZ2_originalOneSlabQuinticTaylor H beta X B =
        1 + (-(beta * S X B)) + (-(beta * S X B)) ^ 2 / 2 +
          (-(beta * S X B)) ^ 3 / 6 +
          (-(beta * S X B)) ^ 4 / 24 +
          (-(beta * S X B)) ^ 5 / 120 := by
    unfold p4Q2PZ2_originalOneSlabQuinticTaylor
      p4Q2PX2_originalOneSlabQuarticTaylor
      p4Q2PP_originalOneSlabCubicTaylor
    ring
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    hPolynomial]
  have hSign : -beta * S X B = -(beta * S X B) := by ring
  rw [hSign]
  exact hExp.trans (pow_le_pow_left₀ (norm_nonneg _) hNorm 6)

/-- Same sixth-order bound for the literal TWO original Wilson slabs:
Q is the true interacting action with all intermediate spatial terms. -/
theorem p4Q2PZ2_originalTwoSlabKernel_sixthRemainder_le
    (beta : ℝ) (hsmall : ‖beta * (2 * M)‖ ≤ 1)
    (X A B : Cfg) :
    ‖K beta A B * K beta X A -
      p4Q2PZ2_originalTwoSlabQuinticTaylor H beta X A B‖ ≤
      ‖beta * (2 * M)‖ ^ 6 := by
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
  have hExp := p4Q2PZ2_realExp_quinticRemainder_le
    (-(beta * Q X A B)) (le_trans hNorm hsmall)
  have hPolynomial :
      p4Q2PZ2_originalTwoSlabQuinticTaylor H beta X A B =
        1 + (-(beta * Q X A B)) + (-(beta * Q X A B)) ^ 2 / 2 +
          (-(beta * Q X A B)) ^ 3 / 6 +
          (-(beta * Q X A B)) ^ 4 / 24 +
          (-(beta * Q X A B)) ^ 5 / 120 := by
    unfold p4Q2PZ2_originalTwoSlabQuinticTaylor
      p4Q2PX2_originalTwoSlabQuarticTaylor
      p4Q2PP_originalTwoSlabCubicTaylor
    ring
  rw [p4Q2PK_originalTwoSlabKernel_product_eq_exp H beta X A B,
    hPolynomial]
  exact hExp.trans (pow_le_pow_left₀ (norm_nonneg _) hNorm 6)

/-- Exact one-slab normalized spatial Haar integral inherits the genuine
sixth remainder of the ORIGINAL Wilson kernel. -/
theorem p4Q2PZ2_originalOneSlabHaar_sixthRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1) (B : Cfg) :
    ‖∫ X : Cfg,
      K beta X B - p4Q2PZ2_originalOneSlabQuinticTaylor H beta X B
        ∂haar‖ ≤ ‖beta * M‖ ^ 6 := by
  have hb :=
    norm_integral_le_of_norm_le_const (μ := haar)
      (Filter.Eventually.of_forall
        (fun X => p4Q2PZ2_originalOneSlabKernel_sixthRemainder_le
          H beta hsmall X B))
  simpa using hb

/-- Double ORIGINAL spatial Haar, with unchanged two-slab interactions,
inherits sixth-order remainder without replacing either posterior. -/
theorem p4Q2PZ2_originalTwoSlabDoubleHaar_sixthRemainder_le
    (beta : ℝ) (hsmall : ‖beta * (2 * M)‖ ≤ 1) (B : Cfg) :
    ‖∫ A : Cfg, ∫ X : Cfg,
      K beta A B * K beta X A -
        p4Q2PZ2_originalTwoSlabQuinticTaylor H beta X A B
          ∂haar ∂haar‖ ≤ ‖beta * (2 * M)‖ ^ 6 := by
  have hInner (A : Cfg) :
      ‖∫ X : Cfg,
        K beta A B * K beta X A -
          p4Q2PZ2_originalTwoSlabQuinticTaylor H beta X A B
            ∂haar‖ ≤ ‖beta * (2 * M)‖ ^ 6 := by
    have hb :=
      norm_integral_le_of_norm_le_const (μ := haar)
        (Filter.Eventually.of_forall
          (fun X => p4Q2PZ2_originalTwoSlabKernel_sixthRemainder_le
            H beta hsmall X A B))
    simpa using hb
  have hb :=
    norm_integral_le_of_norm_le_const (μ := haar)
      (Filter.Eventually.of_forall hInner)
  simpa using hb

end OriginalQuinticWilsonKernel
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ2_realExp_quinticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ2_originalOneSlabKernel_sixthRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ2_originalTwoSlabKernel_sixthRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ2_originalOneSlabHaar_sixthRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ2_originalTwoSlabDoubleHaar_sixthRemainder_le
