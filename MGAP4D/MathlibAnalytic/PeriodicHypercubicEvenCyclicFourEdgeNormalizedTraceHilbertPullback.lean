import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialCyclicFourLegFockPullback
import Mathlib.Analysis.InnerProductSpace.Adjoint
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

/-- The explicit vector is definitionally the degree-one RKHS feature already
used by the normalized relative-trace kernel. -/
theorem specialUnitaryTwoNormalizedTraceFeatureVector_eq_kernelFeature
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoNormalizedTraceFeatureVector g =
      (specialUnitaryNormalizedTraceRelativeKernelFeature
        2 cyclicFourEdgeHilbertTwoRankPositive).feature g := by
  rfl

/-- Hilbert tensor of two degree-one normalized matrix features. -/
abbrev SpecialUnitaryTwoNormalizedTracePairTensorSpace :=
  UniformSpace.Completion
    (SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2)

/-- Pair-of-pairs Hilbert tensor carrier for the four companion edges.  The
first pair is the cyclic `(2,3)` pair and the second the `(0,1)` pair. -/
abbrev SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace :=
  UniformSpace.Completion
    (SpecialUnitaryTwoNormalizedTracePairTensorSpace ⊗[ℝ]
      SpecialUnitaryTwoNormalizedTracePairTensorSpace)

/-- Matrix multiplication linearized on the canonical Hilbert tensor product. -/
noncomputable def specialUnitaryTwoRealFeaturePairMulTensorLinearMap :
    (SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2) →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  TensorProduct.lift (realFeatureMatrixMulLinearMap 2)

/-- Finite-dimensionality makes the tensor-linearized multiplication bounded. -/
noncomputable def specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap :
    (SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2) →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  LinearMap.toContinuousLinearMap
    specialUnitaryTwoRealFeaturePairMulTensorLinearMap

@[simp] theorem specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap_tmul
    (v w : SpecialUnitaryMatrixRealFeatureSpace 2) :
    specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap
        (v ⊗ₜ[ℝ] w) =
      realFeatureMatrixMulLinearMap 2 v w := by
  rfl

/-- The cyclic backward pair `(2,3)` on the algebraic Hilbert tensor. -/
noncomputable def specialUnitaryTwoBackwardPairTensorContraction :
    (SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2) →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap.comp
    (TensorProduct.mapL
      (orientedRealFeatureLinearMap 2 .backward).toContinuousLinearMap
      (orientedRealFeatureLinearMap 2 .backward).toContinuousLinearMap)

/-- The cyclic forward pair `(0,1)` on the algebraic Hilbert tensor. -/
noncomputable def specialUnitaryTwoForwardPairTensorContraction :
    (SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2) →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap.comp
    (TensorProduct.mapL
      (orientedRealFeatureLinearMap 2 .forward).toContinuousLinearMap
      (orientedRealFeatureLinearMap 2 .forward).toContinuousLinearMap)

/-- Extend the backward pair contraction to the completed pair Hilbert tensor. -/
noncomputable def specialUnitaryTwoBackwardPairCompletedContraction :
    SpecialUnitaryTwoNormalizedTracePairTensorSpace →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoBackwardPairTensorContraction.extend
    (UniformSpace.Completion.toComplL :
      (SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
        SpecialUnitaryMatrixRealFeatureSpace 2) →L[ℝ]
        SpecialUnitaryTwoNormalizedTracePairTensorSpace)

/-- Extend the forward pair contraction to the completed pair Hilbert tensor. -/
noncomputable def specialUnitaryTwoForwardPairCompletedContraction :
    SpecialUnitaryTwoNormalizedTracePairTensorSpace →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoForwardPairTensorContraction.extend
    (UniformSpace.Completion.toComplL :
      (SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
        SpecialUnitaryMatrixRealFeatureSpace 2) →L[ℝ]
        SpecialUnitaryTwoNormalizedTracePairTensorSpace)

@[simp] theorem specialUnitaryTwoBackwardPairCompletedContraction_coe
    (t : SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2) :
    specialUnitaryTwoBackwardPairCompletedContraction
        (t : SpecialUnitaryTwoNormalizedTracePairTensorSpace) =
      specialUnitaryTwoBackwardPairTensorContraction t := by
  exact ContinuousLinearMap.extend_eq
    specialUnitaryTwoBackwardPairTensorContraction
    (e := (UniformSpace.Completion.toComplL :
      (SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
        SpecialUnitaryMatrixRealFeatureSpace 2) →L[ℝ]
        SpecialUnitaryTwoNormalizedTracePairTensorSpace))
    (by
      simpa only [UniformSpace.Completion.coe_toComplL] using
        (UniformSpace.Completion.denseRange_coe :
          DenseRange fun x :
            SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
              SpecialUnitaryMatrixRealFeatureSpace 2 =>
            (x : SpecialUnitaryTwoNormalizedTracePairTensorSpace)))
    (by
      simpa only [UniformSpace.Completion.coe_toComplL] using
        UniformSpace.Completion.isUniformInducing_coe
          (SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
            SpecialUnitaryMatrixRealFeatureSpace 2))
    t

@[simp] theorem specialUnitaryTwoForwardPairCompletedContraction_coe
    (t : SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2) :
    specialUnitaryTwoForwardPairCompletedContraction
        (t : SpecialUnitaryTwoNormalizedTracePairTensorSpace) =
      specialUnitaryTwoForwardPairTensorContraction t := by
  exact ContinuousLinearMap.extend_eq
    specialUnitaryTwoForwardPairTensorContraction
    (e := (UniformSpace.Completion.toComplL :
      (SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
        SpecialUnitaryMatrixRealFeatureSpace 2) →L[ℝ]
        SpecialUnitaryTwoNormalizedTracePairTensorSpace))
    (by
      simpa only [UniformSpace.Completion.coe_toComplL] using
        (UniformSpace.Completion.denseRange_coe :
          DenseRange fun x :
            SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
              SpecialUnitaryMatrixRealFeatureSpace 2 =>
            (x : SpecialUnitaryTwoNormalizedTracePairTensorSpace)))
    (by
      simpa only [UniformSpace.Completion.coe_toComplL] using
        UniformSpace.Completion.isUniformInducing_coe
          (SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
            SpecialUnitaryMatrixRealFeatureSpace 2))
    t

/-- Algebraic outer contraction: contract `(2,3)` and `(0,1)` separately and
then multiply the two pair products in cyclic order. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeOuterTensorContraction :
    (SpecialUnitaryTwoNormalizedTracePairTensorSpace ⊗[ℝ]
      SpecialUnitaryTwoNormalizedTracePairTensorSpace) →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap.comp
    (TensorProduct.mapL
      specialUnitaryTwoBackwardPairCompletedContraction
      specialUnitaryTwoForwardPairCompletedContraction)

/-- Extend the cyclic four-edge contraction to the completed pair-of-pairs
Hilbert tensor. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeCompletedContractionRaw :
    SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace 2 :=
  specialUnitaryTwoCyclicFourEdgeOuterTensorContraction.extend
    (UniformSpace.Completion.toComplL :
      (SpecialUnitaryTwoNormalizedTracePairTensorSpace ⊗[ℝ]
        SpecialUnitaryTwoNormalizedTracePairTensorSpace) →L[ℝ]
        SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace)

@[simp] theorem specialUnitaryTwoCyclicFourEdgeCompletedContractionRaw_coe
    (t : SpecialUnitaryTwoNormalizedTracePairTensorSpace ⊗[ℝ]
      SpecialUnitaryTwoNormalizedTracePairTensorSpace) :
    specialUnitaryTwoCyclicFourEdgeCompletedContractionRaw
        (t : SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace) =
      specialUnitaryTwoCyclicFourEdgeOuterTensorContraction t := by
  exact ContinuousLinearMap.extend_eq
    specialUnitaryTwoCyclicFourEdgeOuterTensorContraction
    (e := (UniformSpace.Completion.toComplL :
      (SpecialUnitaryTwoNormalizedTracePairTensorSpace ⊗[ℝ]
        SpecialUnitaryTwoNormalizedTracePairTensorSpace) →L[ℝ]
        SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace))
    (by
      simpa only [UniformSpace.Completion.coe_toComplL] using
        (UniformSpace.Completion.denseRange_coe :
          DenseRange fun x :
            SpecialUnitaryTwoNormalizedTracePairTensorSpace ⊗[ℝ]
              SpecialUnitaryTwoNormalizedTracePairTensorSpace =>
            (x : SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace)))
    (by
      simpa only [UniformSpace.Completion.coe_toComplL] using
        UniformSpace.Completion.isUniformInducing_coe
          (SpecialUnitaryTwoNormalizedTracePairTensorSpace ⊗[ℝ]
            SpecialUnitaryTwoNormalizedTracePairTensorSpace))
    t

/-- Pure four-edge normalized feature tensor in cyclic pair order `(2,3)|(0,1)`. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace :=
  (((
      ((specialUnitaryTwoNormalizedTraceFeatureVector (x 2) ⊗ₜ[ℝ]
          specialUnitaryTwoNormalizedTraceFeatureVector (x 3) :
        SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
          SpecialUnitaryMatrixRealFeatureSpace 2) :
        SpecialUnitaryTwoNormalizedTracePairTensorSpace) ⊗ₜ[ℝ]
      ((specialUnitaryTwoNormalizedTraceFeatureVector (x 0) ⊗ₜ[ℝ]
          specialUnitaryTwoNormalizedTraceFeatureVector (x 1) :
        SpecialUnitaryMatrixRealFeatureSpace 2 ⊗[ℝ]
          SpecialUnitaryMatrixRealFeatureSpace 2) :
        SpecialUnitaryTwoNormalizedTracePairTensorSpace) :
      SpecialUnitaryTwoNormalizedTracePairTensorSpace ⊗[ℝ]
        SpecialUnitaryTwoNormalizedTracePairTensorSpace) :
    SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace)

/-- Before the final normalization correction, the four-edge contraction carries
four copies of the degree-one normalization scale. -/
theorem specialUnitaryTwoCyclicFourEdgeCompletedContractionRaw_featureTensor
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoCyclicFourEdgeCompletedContractionRaw
        (specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor x) =
      specialUnitaryTwoNormalizedTraceFeatureScale ^ 4 •
        specialUnitaryMatrixRealFeature 2 (haarFinFourCyclicPlaquetteWord x) := by
  rw [specialUnitaryTwoCyclicFourEdgeCompletedContractionRaw_coe]
  simp [specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor,
    specialUnitaryTwoCyclicFourEdgeOuterTensorContraction,
    specialUnitaryTwoBackwardPairCompletedContraction_coe,
    specialUnitaryTwoForwardPairCompletedContraction_coe,
    specialUnitaryTwoBackwardPairTensorContraction,
    specialUnitaryTwoForwardPairTensorContraction,
    specialUnitaryTwoNormalizedTraceFeatureVector,
    specialUnitaryTwoRealFeaturePairMulTensorContinuousLinearMap_tmul,
    realFeatureMatrixMulLinearMap_apply,
    haarFinFourCyclicPlaquetteWord_eq, mul_assoc, pow_succ]

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

/-- The normalized cyclic four-edge Hilbert contraction. -/
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
to the four-edge tensor carrier. -/
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
