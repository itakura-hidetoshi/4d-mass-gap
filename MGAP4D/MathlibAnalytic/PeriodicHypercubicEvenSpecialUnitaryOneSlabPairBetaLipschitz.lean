import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabKernelBetaLipschitz
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2Transfer
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelOperatorContinuity
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
# Beta Lipschitz control of the exact pair one-slab Wilson transfer

The literal ordered-pair kernel is the product of two one-slab kernels.
Using the exact one-slab beta-Lipschitz estimate from PR #5109 together with
the pointwise [0,1] kernel bound gives

  ||K2_gamma(p) - K2_beta(p)||
    <= 2 * globalActionBudget(H) * ||gamma - beta||.

Because the pair-Haar product law is a probability measure, the same constant
bounds the product-L² norm of the pair-kernel difference.  The square
Hilbert--Schmidt kernel-operator map is 1-Lipschitz, so the raw ambient pair
transfer satisfies the identical operator-norm estimate.

No normalization scalar is treated here; that is isolated for the next step.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance pairBetaLipschitzTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairBetaLipschitzCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairBetaLipschitzSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairBetaLipschitzMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairBetaLipschitzBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance pairBetaLipschitzSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pairBetaLipschitzPairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- Pointwise beta-Lipschitz estimate for the literal ordered-pair one-slab
Wilson kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma)
    (p :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
        H N gamma p -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
        H N beta p‖ ≤
      (2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) *
        ‖gamma - beta‖ := by
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let d := ‖gamma - beta‖
  let aγ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N gamma p.1.1 p.2.1
  let bγ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N gamma p.1.2 p.2.2
  let aβ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta p.1.1 p.2.1
  let bβ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta p.1.2 p.2.2
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hd : 0 ≤ d := norm_nonneg _
  have haDiff : ‖aγ - aβ‖ ≤ C * d := by
    simpa [aγ, aβ, C, d] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_norm_sub_le
        H N hN beta gamma hbeta hgamma p.1.1 p.2.1
  have hbDiff : ‖bγ - bβ‖ ≤ C * d := by
    simpa [bγ, bβ, C, d] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_norm_sub_le
        H N hN beta gamma hbeta hgamma p.1.2 p.2.2
  have haβ : ‖aβ‖ ≤ 1 := by
    simpa [aβ, Real.norm_eq_abs] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta p.1.1 p.2.1
  have hbγ : ‖bγ‖ ≤ 1 := by
    simpa [bγ, Real.norm_eq_abs] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN gamma hgamma p.1.2 p.2.2
  have hdecomp :
      aγ * bγ - aβ * bβ =
        (aγ - aβ) * bγ + aβ * (bγ - bβ) := by
    ring
  change ‖aγ * bγ - aβ * bβ‖ ≤ (2 * C) * d
  rw [hdecomp]
  calc
    ‖(aγ - aβ) * bγ + aβ * (bγ - bβ)‖ ≤
        ‖aγ - aβ‖ * ‖bγ‖ + ‖aβ‖ * ‖bγ - bβ‖ := by
      rw [norm_mul, norm_mul]
      exact norm_add_le _ _
    _ ≤ (C * d) * 1 + 1 * (C * d) := by
      apply add_le_add
      · exact mul_le_mul haDiff hbγ (norm_nonneg _) (mul_nonneg hC hd)
      · exact mul_le_mul haβ hbDiff (norm_nonneg _) zero_le_one
    _ = (2 * C) * d := by ring

/-- The ordered-pair kernel product-L² vector is Lipschitz in beta with the
same explicit constant because the underlying four-boundary Haar law is a
probability measure. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          H N hN beta hbeta‖ ≤
      (2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) *
        ‖gamma - beta‖ := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let μ₂ := μ.prod μ
  let M :=
    (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) *
      ‖gamma - beta‖
  letI : IsProbabilityMeasure μ₂ := by
    dsimp [μ₂, μ]
    infer_instance
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hConst :
      MemLp
        (fun _ :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
          M)
        2 μ₂ :=
    memLp_const M
  have hGamma :
      (fun p =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          H N hN gamma hgamma p) =ᵐ[μ₂]
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N gamma := by
    simpa [μ₂, μ] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn
        H N hN gamma hgamma
  have hBeta :
      (fun p =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          H N hN beta hbeta p) =ᵐ[μ₂]
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta := by
    simpa [μ₂, μ] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn
        H N hN beta hbeta
  have hle :
      ∀ᵐ p ∂μ₂,
        ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
              H N hN gamma hgamma -
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
              H N hN beta hbeta) p‖ ≤
          ‖hConst.toLp
              (fun _ :
                (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
                  (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
                M) p‖ := by
    filter_upwards [hGamma, hBeta, hConst.coeFn_toLp] with p hpGamma hpBeta hpConst
    change
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
            H N hN gamma hgamma p -
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
            H N hN beta hbeta p‖ ≤ _
    rw [hpGamma, hpBeta, hpConst]
    simpa [M, Real.norm_eq_abs, abs_of_nonneg hM] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_norm_sub_le
        H N hN beta gamma hbeta hgamma p
  calc
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          H N hN beta hbeta‖ ≤
      ‖hConst.toLp
          (fun _ :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
              (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
            M)‖ :=
      Lp.norm_le_norm_of_ae_le hle
    _ = M := by
      rw [MemLp.toLp_const]
      have hConstNorm :=
        Lp.norm_const'
          (μ := μ₂)
          (p := (2 : ENNReal))
          (c := M)
          (by norm_num)
          (by norm_num)
      simpa [Real.norm_eq_abs, abs_of_nonneg hM] using hConstNorm
    _ =
      (2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) *
        ‖gamma - beta‖ := rfl

/-- The raw ambient ordered-pair one-step transfer is beta-Lipschitz in
operator norm with the explicit pair action-budget constant. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta‖ ≤
      (2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) *
        ‖gamma - beta‖ := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
  exact
    (realL2HilbertSchmidtKernelOperator_sub_norm_le
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
        H N hN gamma hgamma)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
        H N hN beta hbeta)).trans
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_norm_sub_le
        H N hN beta gamma hbeta hgamma)

end

end MathlibAnalytic
end MGAP4D
