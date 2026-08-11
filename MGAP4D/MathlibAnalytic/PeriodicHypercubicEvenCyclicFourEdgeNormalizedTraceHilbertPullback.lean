import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialCyclicFourLegFockPullback
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.TensorProduct

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct InnerProduct InnerProductSpace

noncomputable section

local instance cyclicFourEdgeHilbertMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

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

private theorem specialUnitaryTwoNormalizedTraceFeatureScale_inv_mul_sq :
    specialUnitaryTwoNormalizedTraceFeatureScale⁻¹ *
        (specialUnitaryTwoNormalizedTraceFeatureScale *
          specialUnitaryTwoNormalizedTraceFeatureScale) =
      specialUnitaryTwoNormalizedTraceFeatureScale := by
  field_simp [specialUnitaryTwoNormalizedTraceFeatureScale_ne_zero]

private theorem specialUnitaryTwoNormalizedTraceFeatureScale_mul_mul_inv :
    specialUnitaryTwoNormalizedTraceFeatureScale *
        (specialUnitaryTwoNormalizedTraceFeatureScale *
          specialUnitaryTwoNormalizedTraceFeatureScale⁻¹) =
      specialUnitaryTwoNormalizedTraceFeatureScale := by
  field_simp [specialUnitaryTwoNormalizedTraceFeatureScale_ne_zero]

/-- Explicit normalized degree-one `SU(2)` matrix feature. -/
noncomputable def specialUnitaryTwoNormalizedTraceFeatureVector
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoNormalizedTraceFeatureScale •
    specialUnitaryMatrixRealFeature 2 g

/-- The explicit vector is definitionally the degree-one RKHS feature already
used by the normalized relative-trace kernel. -/
theorem specialUnitaryTwoNormalizedTraceFeatureVector_eq_kernelFeature
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoNormalizedTraceFeatureVector g =
      (specialUnitaryNormalizedTraceRelativeKernelFeature
        2 cyclicFourEdgeHilbertTwoRankPositive).feature g := by
  rfl

/-- Canonical finite-dimensional Hilbert tensor for one ordered edge pair. -/
abbrev SpecialUnitaryTwoNormalizedTracePairTensorSpace :=
  SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
    SpecialUnitaryMatrixRealFeatureSpace 2

/-- Canonical pair-of-pairs finite-dimensional Hilbert tensor in cyclic order
`(2,3)|(0,1)`.  We deliberately keep this as Mathlib's algebraic tensor with
its canonical inner product and use `LinearMap.adjoint`; no extra completion
instance is introduced, avoiding any duplicate tensor-product topology. -/
abbrev SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace :=
  SpecialUnitaryTwoNormalizedTracePairTensorSpace ⊗[ℝ]
    SpecialUnitaryTwoNormalizedTracePairTensorSpace

/-- Normalized backward-pair multiplication.  The inverse feature scale removes
one of the two input normalizations, so two normalized edge features map to one
normalized product feature. -/
noncomputable def specialUnitaryTwoBackwardPairNormalizedBilinearMap :
    SpecialUnitaryMatrixRealFeatureSpace 2 →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 →ₗ[ℝ]
        SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoNormalizedTraceFeatureScale⁻¹ •
    ((realFeatureMatrixMulLinearMap 2).compl₁₂
      (orientedRealFeatureLinearMap 2 .backward)
      (orientedRealFeatureLinearMap 2 .backward))

/-- Normalized forward-pair multiplication. -/
noncomputable def specialUnitaryTwoForwardPairNormalizedBilinearMap :
    SpecialUnitaryMatrixRealFeatureSpace 2 →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 →ₗ[ℝ]
        SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoNormalizedTraceFeatureScale⁻¹ •
    ((realFeatureMatrixMulLinearMap 2).compl₁₂
      (orientedRealFeatureLinearMap 2 .forward)
      (orientedRealFeatureLinearMap 2 .forward))

/-- Linearized normalized backward-pair contraction. -/
noncomputable def specialUnitaryTwoBackwardPairTensorLinearMap :
    SpecialUnitaryTwoNormalizedTracePairTensorSpace →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  TensorProduct.lift specialUnitaryTwoBackwardPairNormalizedBilinearMap

/-- Linearized normalized forward-pair contraction. -/
noncomputable def specialUnitaryTwoForwardPairTensorLinearMap :
    SpecialUnitaryTwoNormalizedTracePairTensorSpace →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  TensorProduct.lift specialUnitaryTwoForwardPairNormalizedBilinearMap

@[simp] theorem specialUnitaryTwoBackwardPairTensorLinearMap_feature_tmul
    (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoBackwardPairTensorLinearMap
        (specialUnitaryTwoNormalizedTraceFeatureVector g ⊗ₜ[ℝ]
          specialUnitaryTwoNormalizedTraceFeatureVector h) =
      specialUnitaryTwoNormalizedTraceFeatureVector (g⁻¹ * h⁻¹) := by
  simp [specialUnitaryTwoBackwardPairTensorLinearMap,
    specialUnitaryTwoBackwardPairNormalizedBilinearMap,
    specialUnitaryTwoNormalizedTraceFeatureVector,
    smul_smul,
    specialUnitaryTwoNormalizedTraceFeatureScale_mul_mul_inv,
    realFeatureMatrixMulLinearMap_apply]

@[simp] theorem specialUnitaryTwoForwardPairTensorLinearMap_feature_tmul
    (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoForwardPairTensorLinearMap
        (specialUnitaryTwoNormalizedTraceFeatureVector g ⊗ₜ[ℝ]
          specialUnitaryTwoNormalizedTraceFeatureVector h) =
      specialUnitaryTwoNormalizedTraceFeatureVector (g * h) := by
  simp [specialUnitaryTwoForwardPairTensorLinearMap,
    specialUnitaryTwoForwardPairNormalizedBilinearMap,
    specialUnitaryTwoNormalizedTraceFeatureVector,
    smul_smul,
    specialUnitaryTwoNormalizedTraceFeatureScale_mul_mul_inv,
    realFeatureMatrixMulLinearMap_apply]

/-- Normalized multiplication of the two already-contracted pair features. -/
noncomputable def specialUnitaryTwoOuterNormalizedBilinearMap :
    SpecialUnitaryMatrixRealFeatureSpace 2 →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 →ₗ[ℝ]
        SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoNormalizedTraceFeatureScale⁻¹ •
    realFeatureMatrixMulLinearMap 2

/-- Algebraic four-edge contraction on the canonical finite-dimensional Hilbert
tensor. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTraceLinearMap :
    SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  TensorProduct.lift
    ((specialUnitaryTwoOuterNormalizedBilinearMap).compl₁₂
      specialUnitaryTwoBackwardPairTensorLinearMap
      specialUnitaryTwoForwardPairTensorLinearMap)

/-- The finite-dimensional Hilbert contraction, kept as a linear map so that
Mathlib's finite-dimensional `LinearMap.adjoint` supplies the canonical dual
pullback without introducing a second tensor-product topology. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction :
    SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoCyclicFourEdgeNormalizedTraceLinearMap

/-- Pure four-edge normalized feature tensor in cyclic pair order `(2,3)|(0,1)`. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace :=
  (specialUnitaryTwoNormalizedTraceFeatureVector (x 2) ⊗ₜ[ℝ]
      specialUnitaryTwoNormalizedTraceFeatureVector (x 3)) ⊗ₜ[ℝ]
    (specialUnitaryTwoNormalizedTraceFeatureVector (x 0) ⊗ₜ[ℝ]
      specialUnitaryTwoNormalizedTraceFeatureVector (x 1))

/-- The normalized four-edge contraction sends the four edgewise normalized
features exactly to the normalized feature of the cyclic composite holonomy. -/
theorem specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction_featureTensor
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction
        (specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor x) =
      specialUnitaryTwoNormalizedTraceFeatureVector
        (haarFinFourCyclicPlaquetteWord x) := by
  simp [specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction,
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceLinearMap,
    specialUnitaryTwoOuterNormalizedBilinearMap,
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor,
    specialUnitaryTwoNormalizedTraceFeatureVector,
    smul_smul,
    specialUnitaryTwoNormalizedTraceFeatureScale_mul_mul_inv,
    realFeatureMatrixMulLinearMap_apply,
    haarFinFourCyclicPlaquetteWord_eq,
    mul_assoc]

/-- Hilbert-adjoint pullback of a degree-one cyclic normalized-trace dual vector
to the four-edge tensor carrier.  `LinearMap.adjoint` is the canonical Mathlib
adjoint for finite-dimensional inner-product spaces. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTraceDualPullback
    (q : SpecialUnitaryMatrixRealFeatureSpace 2) :
    SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace :=
  LinearMap.adjoint specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction q

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
    LinearMap.adjoint_inner_left,
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction_featureTensor]

end

end MathlibAnalytic
end MGAP4D
