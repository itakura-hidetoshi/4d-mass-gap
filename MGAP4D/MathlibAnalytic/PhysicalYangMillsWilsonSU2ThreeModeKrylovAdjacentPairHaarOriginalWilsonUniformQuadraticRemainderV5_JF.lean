import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonHaarZeroDerivativeL2ProfileV5_JE
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-!
# P4-Q2-JF: uniform quadratic Taylor remainder of the TRUE original Wilson Haar row

JE established the ACTUAL beta-zero pointwise derivative profile
  D_H(B) = -W_H(B)/2 - κ_H
and proved its genuine normalized spatial Haar-L² representative is not
constant. Now prove the genuinely UNIFORM physical finite-volume Taylor
remainder with an explicit finite action budget M_H:

  ‖ F_beta(B) - 1 - beta D_H(B) ‖ ≤ (beta M_H)^2

simultaneously for every real physical spatial right boundary B,
whenever ‖beta M_H‖≤1. This works on both sides of beta=0 and does
not require a false interacting conditional-Haar substitution.

The proof applies mathlib's actual Real exponential Taylor bound to
the original positive finite SU(2) one-slab Wilson action, integrates
the bounded remainder over the true normalized LEFT spatial Haar, and
promotes the bound to the sup-norm in C(Cfg,ℝ). This is the precise
uniform quantitative bridge required to establish strong C(Cfg) and
hence Haar-L² differentiability of the original kernel row.

The theorem does not by itself establish original interacting GI
second-context detection, uniformity in lattice H, H1-C3, or the
continuum 4D Yang–Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JF_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JF_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JF_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JF_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JF_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section TrueWilsonUniformTaylor

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
local notation "F" =>
  p4Q2IV_originalWilsonUnitHaarKernelSection H
local notation "D" =>
  p4Q2JE_originalWilsonHaarZeroDerivativeProfile H

/-- Taylor's genuine second-order estimate for ONE actual two-boundary
SU(2) Wilson kernel. Its finite-volume uniform majorant depends
only on the ORIGINAL one-slab Wilson action budget. -/
theorem p4Q2JF_originalWilsonOneSlabKernel_quadraticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1) (A B : Cfg) :
    ‖K beta A B - 1 + beta * S A B‖ ≤ (beta * M) ^ 2 := by
  have hM : 0 ≤ M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hSnonneg : 0 ≤ S A B :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by decide) A B
  have hSle : S A B ≤ M :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H 2 (by decide) A B
  have hNorm :
      ‖-beta * S A B‖ ≤ ‖beta * M‖ := by
    calc
      ‖-beta * S A B‖ = ‖beta‖ * S A B := by
        simp only [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hSnonneg]
      _ ≤ ‖beta‖ * M :=
        mul_le_mul_of_nonneg_left hSle (norm_nonneg _)
      _ = ‖beta * M‖ := by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hM]
  have hExp :=
    Real.norm_exp_sub_one_sub_id_le (le_trans hNorm hsmall)
  have hKernel :
      K beta A B - 1 + beta * S A B =
        Real.exp (-beta * S A B) - 1 - (-beta * S A B) := by
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    ring
  rw [hKernel]
  calc
    ‖Real.exp (-beta * S A B) - 1 - (-beta * S A B)‖ ≤
        ‖-beta * S A B‖ ^ 2 := hExp
    _ ≤ ‖beta * M‖ ^ 2 := by gcongr
    _ = (beta * M) ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]

/-- The true derivative profile is exactly MINUS the Haar mean of the
complete original one-slab Wilson action at every genuine right B.
IX is used ONLY to remove the right-boundary dependence of the Haar
crossing mean, not to replace any interacting posterior. -/
theorem p4Q2JF_originalWilsonZeroDerivativeProfile_eq_neg_actionHaarMean
    (B : Cfg) :
    D B = -(∫ A : Cfg, S A B ∂haar) := by
  rw [p4Q2IW_originalWilsonOneSlabHaarAction_mean_split H B,
    p4Q2IX_originalCrossingAction_HaarMean_eq_identity H B]
  change
    -(1 / 2 : ℝ) *
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 B -
      ((1 / 2 : ℝ) *
        (∫ A : Cfg,
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A ∂haar) +
        (∫ A : Cfg, periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A (fun _ => 1) ∂haar)) =
      -((1 / 2 : ℝ) *
        (∫ A : Cfg,
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A ∂haar) +
        (∫ A : Cfg, periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A (fun _ => 1) ∂haar) +
        (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 B)
  ring

/-- Genuine full spatial LEFT normalized SU(2) Haar integration preserves
the uniform quadratic Taylor bound, simultaneously for every actual
right SU(2) spatial boundary. -/
theorem p4Q2JF_originalWilsonHaarRow_quadraticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1) (B : Cfg) :
    ‖F beta B - 1 - beta * D B‖ ≤ (beta * M) ^ 2 := by
  let Q : Cfg → ℝ := fun A => K beta A B - 1 + beta * S A B
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hKcont : Continuous (fun A : Cfg => K beta A B) := by
    have h := (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp hPair
    simpa only [Function.comp_def] using h
  have hScont : Continuous (fun A : Cfg => S A B) := by
    have h := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
    simpa only [Function.comp_def] using h
  have hKint : Integrable (fun A : Cfg => K beta A B) haar :=
    hKcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSint : Integrable (fun A : Cfg => S A B) haar :=
    hScont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQIntegral :
      (∫ A : Cfg, Q A ∂haar) =
        F beta B - 1 + beta * (∫ A : Cfg, S A B ∂haar) := by
    change (∫ A : Cfg, (K beta A B - 1) + beta * S A B ∂haar) =
      (∫ A : Cfg, K beta A B ∂haar) -
        1 + beta * (∫ A : Cfg, S A B ∂haar)
    have hSub :
        (∫ A : Cfg, K beta A B - (1 : ℝ) ∂haar) =
          (∫ A : Cfg, K beta A B ∂haar) -
            (∫ _A : Cfg, (1 : ℝ) ∂haar) := by
      simpa only [Pi.sub_apply] using
        (integral_sub hKint (integrable_const (1 : ℝ)))
    have hAdd :
        (∫ A : Cfg, (K beta A B - 1) + beta * S A B ∂haar) =
          (∫ A : Cfg, K beta A B - 1 ∂haar) +
            (∫ A : Cfg, beta * S A B ∂haar) := by
      simpa only [Pi.add_apply] using
        (integral_add (hKint.sub (integrable_const _)) (hSint.const_mul beta))
    rw [hAdd, hSub, integral_const_mul]
    simp
  have hQpoint (A : Cfg) : ‖Q A‖ ≤ (beta * M) ^ 2 :=
    p4Q2JF_originalWilsonOneSlabKernel_quadraticRemainder_le
      H beta hsmall A B
  have hQint :
      ‖∫ A : Cfg, Q A ∂haar‖ ≤ (beta * M) ^ 2 := by
    have hb := norm_integral_le_of_norm_le_const
      (μ := haar) (Filter.Eventually.of_forall hQpoint)
    simpa using hb
  have hProfile :=
    p4Q2JF_originalWilsonZeroDerivativeProfile_eq_neg_actionHaarMean H B
  calc
    ‖F beta B - 1 - beta * D B‖ =
        ‖F beta B - 1 + beta * (∫ A : Cfg, S A B ∂haar)‖ := by
          rw [hProfile]
          simp only [mul_neg, sub_neg_eq_add]
    _ = ‖∫ A : Cfg, Q A ∂haar‖ := by rw [hQIntegral]
    _ ≤ (beta * M) ^ 2 := hQint

/-- The true Wilson right-boundary Haar row as a continuous map. -/
noncomputable def p4Q2JF_originalWilsonHaarRowContinuous (beta : ℝ) :
    C(Cfg, ℝ) :=
  ⟨F beta, p4Q2IV_originalWilsonUnitHaarKernelSection_continuous H beta⟩

/-- The same quadratic Taylor remainder is UNIFORM in the entire
finite-dimensional compact physical right SU(2) link configuration,
in the actual continuous-function SUP NORM. This stronger bound
is the precise analytic bridge to L²-valued differentiability. -/
theorem p4Q2JF_originalWilsonHaarRow_supNormQuadraticRemainder_le
    (beta : ℝ) (hsmall : ‖beta * M‖ ≤ 1) :
    ‖p4Q2JF_originalWilsonHaarRowContinuous H beta -
        (1 : C(Cfg, ℝ)) - beta • D‖ ≤ (beta * M) ^ 2 := by
  apply (ContinuousMap.norm_le _ (sq_nonneg _)).2
  intro B
  have h := p4Q2JF_originalWilsonHaarRow_quadraticRemainder_le
    H beta hsmall B
  simpa only [p4Q2JF_originalWilsonHaarRowContinuous,
    ContinuousMap.sub_apply, ContinuousMap.one_apply,
    ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul] using h

end TrueWilsonUniformTaylor
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JF_originalWilsonOneSlabKernel_quadraticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JF_originalWilsonZeroDerivativeProfile_eq_neg_actionHaarMean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JF_originalWilsonHaarRow_quadraticRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JF_originalWilsonHaarRow_supNormQuadraticRemainder_le
