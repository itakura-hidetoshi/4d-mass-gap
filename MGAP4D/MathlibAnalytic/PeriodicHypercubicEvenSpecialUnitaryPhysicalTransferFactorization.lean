import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryGaussLawTransfer
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance periodicHypercubicEvenSpecialUnitaryPhysicalL2_completeSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- The canonical Moore--Aronszajn feature analysis operator restricted to the
actual finite-volume Gauss-law Hilbert space. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
      H N hN beta hbeta).comp
    (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).subtypeL

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
        H N hN beta hbeta
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  rfl

/-- Matrix coefficients of the physical transfer are the Gram inner products
of the restricted canonical feature-analysis operator. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_analysis
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta f) g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta g) := by
  let A :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
      H N hN beta hbeta
  change
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta
          (f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
        (g : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) = _
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_eq_adjoint_comp_analysis]
  change
    inner ℝ ((A†) (A f))
        (g : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      inner ℝ (A f) (A g)
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- Exact physical Gram factorization:

`T_phys = A_phys† A_phys`.

This is an equality of bounded operators on the closed Gauss-law Hilbert
space, not merely the restriction of an ambient quadratic-form identity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_eq_adjoint_comp_analysis
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta)†.comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta) := by
  let A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
      H N hN beta hbeta
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_analysis]
  change inner ℝ (A f) (A g) = inner ℝ ((A†) (A f)) g
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- The physical transfer quadratic form is exactly the squared norm of the
physical feature-analysis vector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_quadratic_eq_analysis_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta f) f =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta f‖ ^ 2 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_analysis]
  exact real_inner_self_eq_norm_sq _

/-- The physical one-slab transfer norm is exactly the square of the norm of
the restricted feature-analysis operator.  This is the intrinsic finite-volume
normalization scale on the Gauss-law Hilbert sector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_eq_analysis_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
        H N hN beta hbeta‖ ^ 2 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_eq_adjoint_comp_analysis]
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  ring

/-- Restriction to the Gauss-law Hilbert sector cannot increase the ambient
one-slab transfer norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_le_ambient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta)
    (norm_nonneg _)
  intro f
  change
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
        (f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta‖ *
        ‖(f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))‖
  exact ContinuousLinearMap.le_opNorm
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN beta hbeta) _

/-- Audit-visible exact physical factorization package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFactorizationPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  operatorEq :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta)†.comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta)
  quadraticIdentity :
    ∀ f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta f) f =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
            H N hN beta hbeta f‖ ^ 2
  normIdentity :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
        H N hN beta hbeta‖ ^ 2
  normLeAmbient :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta‖

/-- Construct the complete physical one-slab factorization receipt. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFactorizationPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFactorizationPackage
      H N hN beta hbeta :=
  { operatorEq :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_eq_adjoint_comp_analysis
        H N hN beta hbeta
    quadraticIdentity :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_quadratic_eq_analysis_norm_sq
        H N hN beta hbeta
    normIdentity :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_eq_analysis_sq
        H N hN beta hbeta
    normLeAmbient :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_le_ambient
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D