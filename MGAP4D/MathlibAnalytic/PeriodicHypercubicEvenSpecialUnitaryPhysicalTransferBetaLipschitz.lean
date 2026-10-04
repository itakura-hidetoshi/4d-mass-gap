import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabKernelBetaLipschitz
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryGaussLawTransfer
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelOperatorContinuity
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
# Beta Lipschitz control of the physical one-slab Wilson transfer

PR #5109 gives the pointwise exact one-slab Wilson-kernel estimate

  ||K_gamma(A,B) - K_beta(A,B)||
    <= globalActionBudget(H) ||gamma-beta||.

Because the two-boundary Haar law is a probability measure, the same constant
controls the product-L² kernel vector.  The square Hilbert--Schmidt
kernel-to-operator map from PR #5110 is 1-Lipschitz, and restricting to the
Gauss-law fixed physical subspace cannot increase the operator norm.

Hence the actual physical one-slab transfer and its operator norm are both
Lipschitz in beta with the same explicit finite-volume coefficient.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance physicalBetaLipschitzTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalBetaLipschitzCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalBetaLipschitzSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalBetaLipschitzMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalBetaLipschitzBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalBetaLipschitzSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The literal one-slab kernel product-L² vector inherits exactly the
pointwise beta-Lipschitz constant. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      ‖gamma - beta‖
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H)
      (norm_nonneg (gamma - beta))
  have hConst :
      MemLp
        (fun _ :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          M)
        2 μ :=
    memLp_const M
  have hGamma :
      (fun p =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN gamma hgamma p) =ᵐ[μ]
        (fun p =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N gamma p.1 p.2) := by
    simpa [μ] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
        H N hN gamma hgamma
  have hBeta :
      (fun p =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta p) =ᵐ[μ]
        (fun p =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2) := by
    simpa [μ] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
        H N hN beta hbeta
  have hSub :=
    Lp.coeFn_sub
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN gamma hgamma)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta)
  have hle :
      ∀ᵐ p ∂μ,
        ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
              H N hN gamma hgamma -
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
              H N hN beta hbeta) p‖ ≤
          ‖hConst.toLp
              (fun _ :
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
                M) p‖ := by
    filter_upwards [hSub, hGamma, hBeta, hConst.coeFn_toLp] with
      p hpSub hpGamma hpBeta hpConst
    have hpSub' :
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
              H N hN gamma hgamma -
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
              H N hN beta hbeta) p =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
              H N hN gamma hgamma p -
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
              H N hN beta hbeta p := by
      simpa only [Pi.sub_apply] using hpSub
    rw [hpSub', hpGamma, hpBeta, hpConst]
    have hpoint :
        ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N gamma p.1 p.2 -
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta p.1 p.2‖ ≤ M := by
      simpa [M] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_norm_sub_le
          H N hN beta gamma hbeta hgamma p.1 p.2
    calc
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N gamma p.1 p.2 -
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2‖ ≤ M := hpoint
      _ = ‖M‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hM]
  calc
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta‖ ≤
      ‖hConst.toLp
          (fun _ :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            M)‖ :=
      Lp.norm_le_norm_of_ae_le hle
    _ = M := by
      rw [MemLp.toLp_const]
      have hConstNorm :=
        Lp.norm_const'
          (μ := μ)
          (p := (2 : ENNReal))
          (c := M)
          (by norm_num)
          (by norm_num)
      simpa [Real.norm_eq_abs, abs_of_nonneg hM] using hConstNorm
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := rfl

/-- The ambient one-slab Haar-L² transfer is beta-Lipschitz in operator norm. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_norm_sub_le_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
  exact
    (realL2HilbertSchmidtKernelOperator_sub_norm_le
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN gamma hgamma)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta)).trans
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_norm_sub_le
        H N hN beta gamma hbeta hgamma)

/-- Restricting the ambient beta perturbation to the Gauss-law physical sector
does not enlarge its operator norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  let A :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN gamma hgamma
  let B :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN beta hbeta
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      ‖gamma - beta‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H)
      (norm_nonneg (gamma - beta))
  have hAB : ‖A - B‖ ≤ M := by
    change
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta‖ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          ‖gamma - beta‖
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_norm_sub_le_beta
        H N hN beta gamma hbeta hgamma
  refine ContinuousLinearMap.opNorm_le_bound
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN gamma hgamma -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
    hM ?_
  intro f
  calc
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta) f‖ =
      ‖A (f :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) -
        B (f :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ := by
      rfl
    _ =
      ‖(A - B)
        (f :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ := by
      rfl
    _ ≤
      ‖A - B‖ *
        ‖(f :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ :=
      (A - B).le_opNorm _
    _ ≤
      M *
        ‖(f :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ :=
      mul_le_mul_of_nonneg_right hAB (norm_nonneg _)
    _ = M * ‖f‖ := by rfl

/-- The physical transfer norm itself has the same beta-Lipschitz modulus. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_norm_sub_le_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    ‖‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN gamma hgamma‖ -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  calc
    ‖‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN gamma hgamma‖ -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ := by
      simpa [Real.norm_eq_abs] using
        abs_norm_sub_norm_le
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN gamma hgamma)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta)
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
        H N hN beta gamma hbeta hgamma

end

end MathlibAnalytic
end MGAP4D
