import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceExponentialDecay
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

local instance periodicHypercubicEvenSpecialUnitaryPhysicalFeatureRatio_completeSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance periodicHypercubicEvenSpecialUnitaryPhysicalExcitationFeatureRatio_completeSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta).isClosed_orthogonal.completeSpace_coe

/-- The actual Moore--Aronszajn feature-analysis operator restricted to the
orthogonal complement of the full normalized-transfer top eigenspace.  This is
the literal Wilson feature seen by finite-volume excitations. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →L[ℝ]
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
      H N hN beta hbeta).comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta).subtypeL

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
        H N hN beta hbeta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  rfl

/-- Exact excitation-sector feature factorization of the normalized physical
one-slab transfer.  It identifies the already-constructed top-eigenspace
orthogonal restriction with the normalized Gram operator of the literal
Wilson feature restricted to that sector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_eq_inv_norm_smul_adjoint_comp_feature
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ •
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
            H N hN beta hbeta)†.comp
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
            H N hN beta hbeta)) := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta
  let A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
      H N hN beta hbeta
  let AK :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
      H N hN beta hbeta
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  change
    inner ℝ (S (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
      inner ℝ
        ((‖T‖⁻¹ • ((AK†).comp AK)) f) g
  change
    ‖T‖⁻¹ *
        inner ℝ
          (T (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
          (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
      ‖T‖⁻¹ * inner ℝ ((AK†) (AK f)) g
  congr 1
  calc
    inner ℝ
        (T (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
      inner ℝ
        (A (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
        (A (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) := by
      simpa [T, A] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_analysis
          H N hN beta hbeta
          (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
          (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    _ = inner ℝ ((AK†) (AK f)) g := by
      change inner ℝ (AK f) (AK g) = inner ℝ ((AK†) (AK f)) g
      exact (AK.adjoint_inner_left g (AK f)).symm

/-- The excitation transfer norm is exactly the normalized squared norm of the
restricted literal Wilson feature-analysis operator. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_eq_inv_mul_feature_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2 := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let AK :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
      H N hN beta hbeta
  have hT : 0 < ‖T‖ := by
    simpa [T] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_eq_inv_norm_smul_adjoint_comp_feature]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  rfl

/-- The full physical feature-analysis norm is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_norm_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
      H N hN beta hbeta‖ := by
  have hT :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_eq_analysis_sq] at hT
  nlinarith [norm_nonneg
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
      H N hN beta hbeta)]

/-- Exact relative singular-value formula.  The finite-volume excitation
contraction is the squared norm ratio between the actual Wilson feature on the
full Gauss-law sector and the same feature restricted to the full top-eigenspace
orthogonal sector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_eq_feature_ratio
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2 /
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_eq_inv_mul_feature_sq]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_eq_analysis_sq]
  rw [inv_mul_eq_div]

/-- The actual finite-volume top-eigenspace transfer gap is exactly one minus
the literal Wilson excitation/full feature norm ratio. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap_eq_one_sub_feature_ratio
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta =
      1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
            H N hN beta hbeta‖ ^ 2 /
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
            H N hN beta hbeta‖ ^ 2 := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_eq_feature_ratio]

/-- The literal Wilson excitation/full feature ratio is strictly below one in
every finite volume.  Uniform continuum control is therefore reduced to making
this strict inequality quantitative with a scale-independent margin. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureRatio_lt_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2 /
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2 < 1 := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_eq_feature_ratio]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta

/-- Audit-visible exact reduction of the finite-volume excitation gap to the
relative norm of the literal Wilson Moore--Aronszajn feature. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationFeatureRatioPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  fullFeatureNormPositive :
    0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
      H N hN beta hbeta‖
  transferFactorization :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ •
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
            H N hN beta hbeta)†.comp
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
            H N hN beta hbeta))
  normRatio :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2 /
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2
  featureRatioStrict :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2 /
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2 < 1

/-- Construct the exact excitation-feature ratio package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationFeatureRatioPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationFeatureRatioPackage
      H N hN beta hbeta :=
  { fullFeatureNormPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_norm_pos
        H N hN beta hbeta
    transferFactorization :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_eq_inv_norm_smul_adjoint_comp_feature
        H N hN beta hbeta
    normRatio :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_eq_feature_ratio
        H N hN beta hbeta
    featureRatioStrict :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalFeatureRatio_lt_one
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
