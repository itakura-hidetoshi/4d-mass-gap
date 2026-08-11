import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialCyclicFourLegFockPullback
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct InnerProduct InnerProductSpace

noncomputable section

private theorem cyclicFourEdgeHilbertTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

/-- The scalar multiplying the defining matrix feature in the normalized
`SU(2)` relative-trace RKHS feature. -/
noncomputable def specialUnitaryTwoNormalizedTraceFeatureScale : ℝ :=
  Real.sqrt (1 / (2 : ℝ))

private theorem specialUnitaryTwoNormalizedTraceFeatureScale_pos :
    0 < specialUnitaryTwoNormalizedTraceFeatureScale := by
  unfold specialUnitaryTwoNormalizedTraceFeatureScale
  positivity

private theorem specialUnitaryTwoNormalizedTraceFeatureScale_ne_zero :
    specialUnitaryTwoNormalizedTraceFeatureScale ≠ 0 :=
  ne_of_gt specialUnitaryTwoNormalizedTraceFeatureScale_pos

/-- Explicit normalized degree-one `SU(2)` matrix feature. -/
noncomputable def specialUnitaryTwoNormalizedTraceFeatureVector
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoNormalizedTraceFeatureScale •
    specialUnitaryMatrixRealFeature 2 g

/-- The explicit vector is the degree-one RKHS feature already used by the
normalized relative-trace kernel. -/
theorem specialUnitaryTwoNormalizedTraceFeatureVector_eq_kernelFeature
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoNormalizedTraceFeatureVector g =
      (specialUnitaryNormalizedTraceRelativeKernelFeature
        2 cyclicFourEdgeHilbertTwoRankPositive).feature g := by
  rfl

/-- Two-edge Hilbert tensor carrier.  Because the matrix feature is finite
dimensional, Mathlib's algebraic inner-product tensor is already complete; no
second completion is needed. -/
abbrev SpecialUnitaryTwoNormalizedTracePairTensorSpace :=
  SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
    SpecialUnitaryMatrixRealFeatureSpace 2

/-- Pair-of-pairs finite-dimensional Hilbert tensor carrier for the four
companion edges, in cyclic pair order `(2,3)|(0,1)`. -/
abbrev SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace :=
  SpecialUnitaryTwoNormalizedTracePairTensorSpace ⊗[ℝ]
    SpecialUnitaryTwoNormalizedTracePairTensorSpace

/-- Matrix multiplication linearized on the canonical finite-dimensional
Hilbert tensor product. -/
noncomputable def specialUnitaryTwoRealFeaturePairMulTensorLinearMap :
    SpecialUnitaryTwoNormalizedTracePairTensorSpace →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  TensorProduct.lift (realFeatureMatrixMulLinearMap 2)

/-- Finite-dimensionality makes tensor-linearized multiplication bounded. -/
noncomputable def specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap :
    SpecialUnitaryTwoNormalizedTracePairTensorSpace →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  LinearMap.toContinuousLinearMap
    specialUnitaryTwoRealFeaturePairMulTensorLinearMap

@[simp] theorem specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap_tmul
    (v w : SpecialUnitaryMatrixRealFeatureSpace 2) :
    specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap
        (v ⊗ₜ[ℝ] w) =
      realFeatureMatrixMulLinearMap 2 v w := by
  change specialUnitaryTwoRealFeaturePairMulTensorLinearMap (v ⊗ₜ[ℝ] w) = _
  simp [specialUnitaryTwoRealFeaturePairMulTensorLinearMap]

/-- The cyclic backward pair `(2,3)`. -/
noncomputable def specialUnitaryTwoBackwardPairTensorContraction :
    SpecialUnitaryTwoNormalizedTracePairTensorSpace →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap.comp
    (TensorProduct.mapL
      (orientedRealFeatureLinearMap 2 .backward).toContinuousLinearMap
      (orientedRealFeatureLinearMap 2 .backward).toContinuousLinearMap)

/-- The cyclic forward pair `(0,1)`. -/
noncomputable def specialUnitaryTwoForwardPairTensorContraction :
    SpecialUnitaryTwoNormalizedTracePairTensorSpace →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap.comp
    (TensorProduct.mapL
      (orientedRealFeatureLinearMap 2 .forward).toContinuousLinearMap
      (orientedRealFeatureLinearMap 2 .forward).toContinuousLinearMap)

/-- Contract `(2,3)` and `(0,1)` separately and multiply the pair products in
cyclic order. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeCompletedContractionRaw :
    SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap.comp
    (TensorProduct.mapL
      specialUnitaryTwoBackwardPairTensorContraction
      specialUnitaryTwoForwardPairTensorContraction)

/-- Pure four-edge normalized feature tensor in cyclic pair order `(2,3)|(0,1)`. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace :=
  (specialUnitaryTwoNormalizedTraceFeatureVector (x 2) ⊗ₜ[ℝ]
      specialUnitaryTwoNormalizedTraceFeatureVector (x 3)) ⊗ₜ[ℝ]
    (specialUnitaryTwoNormalizedTraceFeatureVector (x 0) ⊗ₜ[ℝ]
      specialUnitaryTwoNormalizedTraceFeatureVector (x 1))

/-- Before the final normalization correction, the four-edge contraction carries
four copies of the degree-one normalization scale. -/
theorem specialUnitaryTwoCyclicFourEdgeCompletedContractionRaw_featureTensor
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoCyclicFourEdgeCompletedContractionRaw
        (specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor x) =
      specialUnitaryTwoNormalizedTraceFeatureScale ^ 4 •
        specialUnitaryMatrixRealFeature 2 (haarFinFourCyclicPlaquetteWord x) := by
  simp [specialUnitaryTwoCyclicFourEdgeCompletedContractionRaw,
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor,
    specialUnitaryTwoBackwardPairTensorContraction,
    specialUnitaryTwoForwardPairTensorContraction,
    specialUnitaryTwoNormalizedTraceFeatureVector,
    specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap_tmul,
    realFeatureMatrixMulLinearMap_apply,
    haarFinFourCyclicPlaquetteWord,
    haarCyclicPlaquetteWord,
    mul_assoc, pow_succ]

/-- Correction factor converting the four normalized input scales to the one
normalized output scale. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizationCorrection : ℝ :=
  specialUnitaryTwoNormalizedTraceFeatureScale /
    specialUnitaryTwoNormalizedTraceFeatureScale ^ 4

private theorem specialUnitaryTwoCyclicFourEdgeNormalizationCorrection_mul_scale_pow :
    specialUnitaryTwoCyclicFourEdgeNormalizationCorrection *
        specialUnitaryTwoNormalizedTraceFeatureScale ^ 4 =
      specialUnitaryTwoNormalizedTraceFeatureScale := by
  unfold specialUnitaryTwoCyclicFourEdgeNormalizationCorrection
  field_simp [specialUnitaryTwoNormalizedTraceFeatureScale_ne_zero]

/-- The normalized cyclic four-edge finite-dimensional Hilbert contraction. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction :
    SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoCyclicFourEdgeNormalizationCorrection •
    specialUnitaryTwoCyclicFourEdgeCompletedContractionRaw

/-- The normalized four-edge contraction sends the four edgewise normalized
features exactly to the normalized feature of the cyclic composite holonomy. -/
theorem specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction_featureTensor
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction
        (specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor x) =
      specialUnitaryTwoNormalizedTraceFeatureVector
        (haarFinFourCyclicPlaquetteWord x) := by
  rw [specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction,
    ContinuousLinearMap.smul_apply,
    specialUnitaryTwoCyclicFourEdgeCompletedContractionRaw_featureTensor]
  rw [smul_smul,
    specialUnitaryTwoCyclicFourEdgeNormalizationCorrection_mul_scale_pow]
  rfl

/-- Hilbert-adjoint pullback of a degree-one cyclic normalized-trace dual vector
to the exact four-edge tensor carrier. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTraceDualPullback
    (q : SpecialUnitaryMatrixRealFeatureSpace 2) :
    SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace :=
  specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction.adjoint q

/-- Exact degree-one pullback identity against every four-edge pure feature
tensor. -/
theorem specialUnitaryTwoCyclicFourEdgeNormalizedTraceDualPullback_inner_featureTensor
    (q : SpecialUnitaryMatrixRealFeatureSpace 2)
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    inner ℝ
        (specialUnitaryTwoCyclicFourEdgeNormalizedTraceDualPullback q)
        (specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor x) =
      inner ℝ q
        (specialUnitaryTwoNormalizedTraceFeatureVector
          (haarFinFourCyclicPlaquetteWord x)) := by
  rw [specialUnitaryTwoCyclicFourEdgeNormalizedTraceDualPullback,
    ContinuousLinearMap.adjoint_inner_left,
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction_featureTensor]

end

end MathlibAnalytic
end MGAP4D
