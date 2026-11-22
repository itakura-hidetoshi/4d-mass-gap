import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUniformFirstModeMagnitudeV5_PZ37AOG
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOH — genuine Wilson kernel, local relative Taylor remainder

This additive leaf stays on the original finite-volume Wilson one-slab kernel
and the original Haar-preserving primary-link center twist.

The first comparison factors the *actual* kernel through the action difference
of the two right-boundary configurations.  The action difference is bounded
by eight, independent of the number of links.  For 0 <= beta <= 1/8 the
pinned mathlib exponential Taylor bound therefore gives a relative
quadratic error 64*beta^2 times the original flipped kernel.

This is a pointwise signed relative remainder, not a conditional Haar row
moment or a statement about the normalized physical top eigenvector.
The fixed-left-boundary first-character moment, eigenvector gluing, and
uniform amplitude normalization remain unproved in this leaf.
-/

namespace MGAP4D.MathlibAnalytic

open scoped ENNReal Topology InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The full ORIGINAL Wilson action difference under the genuine primary
right-boundary center twist.  It is a difference, not a new action. -/
noncomputable def p4Q2PZ37AOH_originalRightCenterTwistActionGap
    (H : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B -
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A
    (p4Q2PZ37ANV_singleLinkCenterTwist H
      (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B)

/-- Local action oscillation stays bounded independently of finite volume. -/
theorem p4Q2PZ37AOH_originalRightCenterTwistActionGap_abs_le_eight
    (H : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B| ≤ 8 := by
  unfold p4Q2PZ37AOH_originalRightCenterTwistActionGap
  rw [abs_sub_comm]
  exact p4Q2PZ37AOC_originalSlabAction_rightCenterTwist_sub_abs_le_eight
    H (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) A B

/-- The genuine kernel factors through the relative action difference,
without any volume-dependent global-action bound. -/
theorem p4Q2PZ37AOH_originalKernel_rightCenterTwist_factorization
    (H : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
        (p4Q2PZ37ANV_singleLinkCenterTwist H
          (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B) *
      Real.exp (-beta * p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    ← Real.exp_add]
  congr 1
  unfold p4Q2PZ37AOH_originalRightCenterTwistActionGap
  ring

/-- Exponential convexity gives the sign of the local linear remainder. -/
theorem p4Q2PZ37AOH_real_exp_relativeLinearRemainder_nonneg
    (beta delta : ℝ) :
    0 ≤ Real.exp (-beta * delta) - 1 + beta * delta := by
  have h := Real.add_one_le_exp (-beta * delta)
  linarith only [h]

/-- The pinned mathlib quadratic remainder is dimension-free whenever
the local action oscillation is at most eight and 8*beta <= 1. -/
theorem p4Q2PZ37AOH_real_exp_relativeLinearRemainder_abs_le
    (beta delta : ℝ) (hbeta : 0 ≤ beta)
    (hsmall : 8 * beta ≤ 1) (hdelta : |delta| ≤ 8) :
    |Real.exp (-beta * delta) - 1 + beta * delta| ≤ 64 * beta^2 := by
  have hprod : beta * |delta| ≤ 1 := by
    calc
      _ ≤ beta * 8 := mul_le_mul_of_nonneg_left hdelta hbeta
      _ ≤ 1 := by nlinarith only [hsmall]
  have hnorm : ‖-beta * delta‖ = beta * |delta| := by
    simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hbeta]
  have hnormsmall : ‖-beta * delta‖ ≤ 1 := by
    rw [hnorm]
    exact hprod
  have hTaylor := Real.norm_exp_sub_one_sub_id_le hnormsmall
  have hmul : beta * |delta| ≤ beta * 8 :=
    mul_le_mul_of_nonneg_left hdelta hbeta
  have hleft : 0 ≤ beta * 8 - beta * |delta| := sub_nonneg.mpr hmul
  have hright : 0 ≤ beta * 8 + beta * |delta| :=
    add_nonneg (by positivity) (mul_nonneg hbeta (abs_nonneg delta))
  have hsq : (beta * |delta|)^2 ≤ (beta * 8)^2 := by
    have hp := mul_nonneg hleft hright
    nlinarith only [hp]
  have hform : Real.exp (-beta * delta) - 1 + beta * delta =
      Real.exp (-beta * delta) - 1 - (-beta * delta) := by ring
  calc
    |Real.exp (-beta * delta) - 1 + beta * delta| =
        ‖Real.exp (-beta * delta) - 1 - (-beta * delta)‖ := by
          rw [Real.norm_eq_abs, hform]
    _ ≤ ‖-beta * delta‖^2 := hTaylor
    _ = (beta * |delta|)^2 := by rw [hnorm]
    _ ≤ (beta * 8)^2 := hsq
    _ = 64 * beta^2 := by ring

/-- For every finite H and arbitrary beta, the actual kernel's relative
first-order remainder is nonnegative. -/
theorem p4Q2PZ37AOH_originalKernel_rightCenterTwist_relativeRemainder_nonneg
    (H : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
        (p4Q2PZ37ANV_singleLinkCenterTwist H
          (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B) +
      beta * p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
          (p4Q2PZ37ANV_singleLinkCenterTwist H
            (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B) := by
  let k := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
  let kt := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
    (p4Q2PZ37ANV_singleLinkCenterTwist H
      (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B)
  let delta := p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B
  have hfactor : k = kt * Real.exp (-beta * delta) := by
    dsimp [k, kt, delta]
    exact p4Q2PZ37AOH_originalKernel_rightCenterTwist_factorization H beta A B
  have hkt : 0 ≤ kt := by
    dsimp [kt]
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    exact Real.exp_nonneg _
  have hscalar := p4Q2PZ37AOH_real_exp_relativeLinearRemainder_nonneg beta delta
  change 0 ≤ k - kt + beta * delta * kt
  rw [hfactor]
  have hshape : kt * Real.exp (-beta * delta) - kt + beta * delta * kt =
      kt * (Real.exp (-beta * delta) - 1 + beta * delta) := by ring
  rw [hshape]
  exact mul_nonneg hkt hscalar

/-- Original Wilson-kernel *pointwise* relative quadratic remainder, with
the constant 64 independent of finite volume or the global action budget.
The right side uses the original flipped kernel, not an invented measure. -/
theorem p4Q2PZ37AOH_originalKernel_rightCenterTwist_relativeRemainder_abs_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 8 * beta ≤ 1)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
        (p4Q2PZ37ANV_singleLinkCenterTwist H
          (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B) +
      beta * p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
          (p4Q2PZ37ANV_singleLinkCenterTwist H
            (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B)| ≤
      64 * beta^2 *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
          (p4Q2PZ37ANV_singleLinkCenterTwist H
            (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B) := by
  let k := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
  let kt := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
    (p4Q2PZ37ANV_singleLinkCenterTwist H
      (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B)
  let delta := p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B
  have hfactor : k = kt * Real.exp (-beta * delta) := by
    dsimp [k, kt, delta]
    exact p4Q2PZ37AOH_originalKernel_rightCenterTwist_factorization H beta A B
  have hkt : 0 ≤ kt := by
    dsimp [kt]
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    exact Real.exp_nonneg _
  have hdelta : |delta| ≤ 8 :=
    p4Q2PZ37AOH_originalRightCenterTwistActionGap_abs_le_eight H A B
  have hscalar :=
    p4Q2PZ37AOH_real_exp_relativeLinearRemainder_abs_le beta delta hbeta hsmall hdelta
  change |k - kt + beta * delta * kt| ≤ 64 * beta^2 * kt
  rw [hfactor]
  have hshape : kt * Real.exp (-beta * delta) - kt + beta * delta * kt =
      kt * (Real.exp (-beta * delta) - 1 + beta * delta) := by ring
  calc
    |kt * Real.exp (-beta * delta) - kt + beta * delta * kt| =
        kt * |Real.exp (-beta * delta) - 1 + beta * delta| := by
          rw [hshape, abs_mul, abs_of_nonneg hkt]
    _ ≤ kt * (64 * beta^2) := mul_le_mul_of_nonneg_left hscalar hkt
    _ = 64 * beta^2 * kt := by ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOH_originalRightCenterTwistActionGap_abs_le_eight
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOH_originalKernel_rightCenterTwist_factorization
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOH_real_exp_relativeLinearRemainder_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOH_real_exp_relativeLinearRemainder_abs_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOH_originalKernel_rightCenterTwist_relativeRemainder_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOH_originalKernel_rightCenterTwist_relativeRemainder_abs_le
