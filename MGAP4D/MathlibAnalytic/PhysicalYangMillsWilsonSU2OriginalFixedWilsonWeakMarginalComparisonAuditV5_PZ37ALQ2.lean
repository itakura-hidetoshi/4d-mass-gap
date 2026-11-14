import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedWilsonSharpMarginalVarianceBridgeV5_PZ37ALQ
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonMarginalCondExpComparisonAudit
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALQ2: weak physical variance comparison and exact-data obstruction

The *exact* WilsonMarginalCondExpComparisonData used in ALQ implies much
more than a variance inequality: the canonical audit shows that for EVERY
color c and x, A(x-P_c x)=0. If physical feature analysis A is injective,
ALL P_c must be identity. Then a nonzero excited vector obstructs ANY
positive frame constant. None of these extra conditions is silently
dismissed; injectivity is explicitly a hypothesis, not an assertion.

This second append-only leaf isolates the strictly WEAKER model-facing
hypothesis that avoids over-constraining the physical Wilson marginal:
  eta ||A_H||² E_color,H(x)
    <= ||A_H||² ||x||² - ||A_H x||²
on the actual physical K_H, with eta >= 0. Together with a separate
frame estimate kappa ||x||² <= E_color,H(x), it implies the SHARP
  ||R_H|| <= 1-eta*kappa, gap_H >= eta*kappa
provided 0 <= eta*kappa <= 1. There is no factor-1/2 loss.

The weak comparison can be sought by genuine Wilson kernel estimates
without asserting the strong, possibly obstructed exact marginal data.
This is a conditional lemma: NO explicit local P_H, eta>0, uniform
kappa>0, or all-H weak comparison witness has yet been constructed.
Physical Wilson P, A, full-top K, beta0, Haar and AJA are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000

namespace GroundStatePosteriorJoint

/-- Only a positive WEAK quadratic comparison is needed to transfer a
local residual frame into actual feature-analysis energy. No exact
marginal lift, intertwining, or coarse projection is needed here. -/
theorem p4Q2PZ37ALQ2_genericWeakComparisonFrameToEnergy
    {E F C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    [Fintype C]
    (localP : C → E →L[ℝ] E)
    (A : E →L[ℝ] F)
    (κ η : ℝ) (hη0 : 0 ≤ η)
    (x : E)
    (hframe : κ * ‖x‖ ^ 2 ≤ boundedColorNormalizedResidualEnergy localP x)
    (hComparison :
      η * ‖A‖ ^ 2 * boundedColorNormalizedResidualEnergy localP x ≤
        ‖A‖ ^ 2 * ‖x‖ ^ 2 - ‖A x‖ ^ 2) :
    ‖A x‖ ^ 2 ≤ (1 - η * κ) * ‖A‖ ^ 2 * ‖x‖ ^ 2 := by
  have hFactor : 0 ≤ η * ‖A‖ ^ 2 :=
    mul_nonneg hη0 (sq_nonneg _)
  have hScaled :=
    mul_le_mul_of_nonneg_left hframe hFactor
  have hDeficit :
      (η * ‖A‖ ^ 2) * (κ * ‖x‖ ^ 2) ≤
        ‖A‖ ^ 2 * ‖x‖ ^ 2 - ‖A x‖ ^ 2 :=
    hScaled.trans hComparison
  calc
    ‖A x‖ ^ 2 ≤
        ‖A‖ ^ 2 * ‖x‖ ^ 2 -
          (η * ‖A‖ ^ 2) * (κ * ‖x‖ ^ 2) := by
            linarith
    _ = (1 - η * κ) * ‖A‖ ^ 2 * ‖x‖ ^ 2 := by ring

variable (H : ℕ)

local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "P" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "A" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le

/-- Unmodified physical Wilson weak comparison plus frame, with independent
loss eta, bounds the SAME original positive feature energy. -/
theorem p4Q2PZ37ALQ2_originalFixedWeakFrameToEnergy
    {C : Type*} [Fintype C]
    (localP : C → G →L[ℝ] G)
    (κ η : ℝ) (hη0 : 0 ≤ η)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy localP (x : G))
    (hComparison : ∀ x : K,
      η * ‖A‖ ^ 2 * boundedColorNormalizedResidualEnergy localP (x : G) ≤
        ‖A‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖A (x : G)‖ ^ 2)
    (x : K) :
    ‖A (x : G)‖ ^ 2 ≤
      (1 - η * κ) * ‖A‖ ^ 2 * ‖(x : G)‖ ^ 2 := by
  exact p4Q2PZ37ALQ2_genericWeakComparisonFrameToEnergy
    localP A κ η hη0 (x : G) (hframe x) (hComparison x)

/-- Sharp H-wise physical top-orthogonal norm bound from only the
WEAKER, direct Wilson feature-variance comparison, not exact D. -/
theorem p4Q2PZ37ALQ2_originalFixedNorm_le_of_weakComparison
    {C : Type*} [Fintype C]
    (localP : C → G →L[ℝ] G)
    (κ η : ℝ) (hκ0 : 0 ≤ κ) (hη0 : 0 ≤ η)
    (hηκ1 : η * κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy localP (x : G))
    (hComparison : ∀ x : K,
      η * ‖A‖ ^ 2 * boundedColorNormalizedResidualEnergy localP (x : G) ≤
        ‖A‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖A (x : G)‖ ^ 2) :
    ‖R‖ ≤ 1 - η * κ := by
  apply (p4Q2PZ37ALP_originalFixedNorm_le_iff_featureEnergy
    H (1 - η * κ) (by linarith)).mpr
  intro x
  have hEnergy :=
    p4Q2PZ37ALQ2_originalFixedWeakFrameToEnergy
      H localP κ η hη0 hframe hComparison x
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_eq_analysis_sq
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le]
  exact hEnergy

/-- Lossless linear bridge: kappa*eta instead of the previous (kappa*eta)/2.
This remains conditional on a model-side weak comparison at the true beta0. -/
theorem p4Q2PZ37ALQ2_originalFixedGap_ge_of_weakComparison
    {C : Type*} [Fintype C]
    (localP : C → G →L[ℝ] G)
    (κ η : ℝ) (hκ0 : 0 ≤ κ) (hη0 : 0 ≤ η)
    (hηκ1 : η * κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy localP (x : G))
    (hComparison : ∀ x : K,
      η * ‖A‖ ^ 2 * boundedColorNormalizedResidualEnergy localP (x : G) ≤
        ‖A‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖A (x : G)‖ ^ 2) :
    η * κ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le := by
  have hNorm :=
    p4Q2PZ37ALQ2_originalFixedNorm_le_of_weakComparison
      H localP κ η hκ0 hη0 hηκ1 hframe hComparison
  change η * κ ≤ 1 - ‖R‖
  linarith

/-- One fixed color count and a common positive eta*kappa yield a
volume-independent original physical gap IF the genuine frame and
weak Wilson feature-variance comparison can be supplied uniformly. -/
theorem p4Q2PZ37ALQ2_allH_gap_ge_of_weakComparison
    {C : Type*} [Fintype C]
    (localP : ∀ H : ℕ,
      C →
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (κ η : ℝ) (hκ0 : 0 ≤ κ) (hη0 : 0 ≤ η)
    (hηκ1 : η * κ ≤ 1)
    (hframe : ∀ (H : ℕ)
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le),
      κ * ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy (localP H)
          (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2))
    (hComparison : ∀ (H : ℕ)
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le),
      η *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le‖ ^ 2 *
        boundedColorNormalizedResidualEnergy (localP H)
          (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le‖ ^ 2 *
        ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖ ^ 2 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
          (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖ ^ 2) :
    ∀ H : ℕ,
      η * κ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le := by
  intro H
  exact p4Q2PZ37ALQ2_originalFixedGap_ge_of_weakComparison
    H (localP H) κ η hκ0 hη0 hηκ1 (hframe H) (hComparison H)

/-- The model's OLD exact marginal data forces the physical analysis map to
annihilate every local residual. This is a concrete separate obstruction
to constructing the exact D, rather than an assumed consequence of the
weaker comparison used above. -/
theorem p4Q2PZ37ALQ2_exactMarginalForcesPhysicalResidualKernel
    {C : Type*} [Fintype C]
    (localP : C → G →L[ℝ] G)
    (D : WilsonMarginalCondExpComparisonData localP A)
    (c : C) (x : G) :
    A (x - localP c x) = 0 := by
  exact D.analysis_residual_eq_zero localP A c x

/-- Under the explicit additional hypothesis that the ACTUAL physical A
is injective, exact D forces every color map to be the identity. The
injectivity hypothesis is NOT claimed as a proved Wilson fact. -/
theorem p4Q2PZ37ALQ2_exactMarginalForcesColorIdentity_of_injective
    {C : Type*} [Fintype C]
    (localP : C → G →L[ℝ] G)
    (D : WilsonMarginalCondExpComparisonData localP A)
    (hInjective : Function.Injective A)
    (c : C) (x : G) :
    localP c x = x := by
  have hKernel :=
    p4Q2PZ37ALQ2_exactMarginalForcesPhysicalResidualKernel
      H localP D c x
  have h0 : A (x - localP c x) = A (0 : G) := by
    simpa using hKernel
  have hEq : x - localP c x = 0 := hInjective h0
  exact (sub_eq_zero.mp hEq).symm

/-- Consequently, if the actual excited sector contains ANY nonzero vector,
injectivity of A plus exact D obstructs a positive color-frame constant.
This makes the exact-D route's potential incompatibility visible. -/
theorem p4Q2PZ37ALQ2_exactMarginalAndInjectivityObstructFrame
    {C : Type*} [Fintype C]
    (localP : C → G →L[ℝ] G)
    (D : WilsonMarginalCondExpComparisonData localP A)
    (hInjective : Function.Injective A)
    (κ : ℝ) (hκ : 0 < κ)
    (x : K) (hx : (x : G) ≠ 0) :
    ¬ ∀ y : K,
      κ * ‖(y : G)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy localP (y : G) := by
  have hfixed : (x : G) ∈ boundedColorCommonFixedSpace localP := by
    intro c
    exact p4Q2PZ37ALQ2_exactMarginalForcesColorIdentity_of_injective
      H localP D hInjective c (x : G)
  exact p4Q2PZ37ALQ_originalFixedCommonFixedObstructsPositiveFrame
    H localP κ hκ x hx hfixed

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ2_genericWeakComparisonFrameToEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ2_originalFixedWeakFrameToEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ2_originalFixedNorm_le_of_weakComparison
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ2_originalFixedGap_ge_of_weakComparison
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ2_allH_gap_ge_of_weakComparison
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ2_exactMarginalForcesPhysicalResidualKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ2_exactMarginalForcesColorIdentity_of_injective
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALQ2_exactMarginalAndInjectivityObstructFrame
