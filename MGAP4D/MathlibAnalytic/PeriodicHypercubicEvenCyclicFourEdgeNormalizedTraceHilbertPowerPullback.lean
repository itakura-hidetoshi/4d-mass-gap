import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeNormalizedTraceHilbertPullback
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureFiniteDimensionalPowerMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct InnerProduct InnerProductSpace

noncomputable section

private theorem cyclicFourEdgeHilbertPowerTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

/-- Reinstall Mathlib's canonical Hilbert tensor structures in this module.
The corresponding instances in the degree-one file were deliberately local. -/
noncomputable local instance cyclicFourEdgePowerPairNormedAddCommGroup :
    NormedAddCommGroup SpecialUnitaryTwoNormalizedTracePairTensorSpace :=
  TensorProduct.instNormedAddCommGroup

noncomputable local instance cyclicFourEdgePowerPairInnerProductSpace :
    InnerProductSpace ℝ SpecialUnitaryTwoNormalizedTracePairTensorSpace :=
  TensorProduct.instInnerProductSpace

noncomputable local instance cyclicFourEdgePowerFourTensorNormedAddCommGroup :
    NormedAddCommGroup SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace :=
  TensorProduct.instNormedAddCommGroup

noncomputable local instance cyclicFourEdgePowerFourTensorInnerProductSpace :
    InnerProductSpace ℝ SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace :=
  TensorProduct.instInnerProductSpace

noncomputable local instance cyclicFourEdgePowerPairFiniteDimensional :
    FiniteDimensional ℝ SpecialUnitaryTwoNormalizedTracePairTensorSpace := by
  infer_instance

noncomputable local instance cyclicFourEdgePowerFourTensorFiniteDimensional :
    FiniteDimensional ℝ SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace := by
  infer_instance

noncomputable local instance cyclicFourEdgePowerFourTensorCompleteSpace :
    CompleteSpace SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace :=
  FiniteDimensional.complete ℝ _

/-- The target degree-one normalized relative-trace Hilbert feature. -/
noncomputable def specialUnitaryTwoNormalizedTraceHilbertKernelFeature :
    RealHilbertKernelFeature
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (specialUnitaryNormalizedTraceRelativeKernel 2) :=
  specialUnitaryNormalizedTraceRelativeKernelFeature
    2 cyclicFourEdgeHilbertPowerTwoRankPositive

/-- The normalized relative-trace kernel is the inner product of the explicit
normalized matrix feature vectors used by the degree-one four-edge contraction. -/
theorem specialUnitaryTwoNormalizedTraceRelativeKernel_eq_inner_featureVector
    (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryNormalizedTraceRelativeKernel 2 g h =
      inner ℝ
        (specialUnitaryTwoNormalizedTraceFeatureVector g)
        (specialUnitaryTwoNormalizedTraceFeatureVector h) := by
  rw [specialUnitaryTwoNormalizedTraceFeatureVector_eq_kernelFeature,
    specialUnitaryTwoNormalizedTraceFeatureVector_eq_kernelFeature]
  exact specialUnitaryTwoNormalizedTraceHilbertKernelFeature.kernel_eq_inner g h

/-- Product kernel of the four independent normalized temporal-edge features,
kept in the validated cyclic pair order `(2,3)|(0,1)`.

This is intentionally not the normalized relative-trace kernel of the cyclic
composite holonomy.  It is the genuine four-edge tensor kernel required by the
edgewise Wilson Taylor expansion. -/
def specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel
    (x y : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  (specialUnitaryNormalizedTraceRelativeKernel 2 (x 2) (y 2) *
      specialUnitaryNormalizedTraceRelativeKernel 2 (x 3) (y 3)) *
    (specialUnitaryNormalizedTraceRelativeKernel 2 (x 0) (y 0) *
      specialUnitaryNormalizedTraceRelativeKernel 2 (x 1) (y 1))

/-- Hilbert realization of the genuine four-edge product kernel.  Its feature
is exactly the degree-one pure four-edge tensor already validated in #1662. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature :
    RealHilbertKernelFeature
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel where
  FeatureHilbert := SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace
  feature := specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor
  kernel_eq_inner x y := by
    simp only [specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseKernel,
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor,
      TensorProduct.inner_tmul]
    rw [specialUnitaryTwoNormalizedTraceRelativeKernel_eq_inner_featureVector,
      specialUnitaryTwoNormalizedTraceRelativeKernel_eq_inner_featureVector,
      specialUnitaryTwoNormalizedTraceRelativeKernel_eq_inner_featureVector,
      specialUnitaryTwoNormalizedTraceRelativeKernel_eq_inner_featureVector]

/-- Degree-one map between the genuine four-edge Hilbert feature and the cyclic
normalized relative-trace feature. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTraceDegreeOneLinearMap :
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.FeatureHilbert →ₗ[ℝ]
      specialUnitaryTwoNormalizedTraceHilbertKernelFeature.FeatureHilbert := by
  change SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace →ₗ[ℝ]
    SpecialUnitaryMatrixRealFeatureSpace 2
  exact specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction

/-- The degree-one map sends the genuine four-edge pure feature to the target
feature of the cyclic holonomy. -/
theorem specialUnitaryTwoCyclicFourEdgeNormalizedTraceDegreeOneLinearMap_feature
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceDegreeOneLinearMap
        (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.feature x) =
      specialUnitaryTwoNormalizedTraceHilbertKernelFeature.feature
        (haarFinFourCyclicPlaquetteWord x) := by
  change specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction
      (specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor x) =
    (specialUnitaryNormalizedTraceRelativeKernelFeature
      2 cyclicFourEdgeHilbertPowerTwoRankPositive).feature
      (haarFinFourCyclicPlaquetteWord x)
  rw [specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction_featureTensor]
  exact specialUnitaryTwoNormalizedTraceFeatureVector_eq_kernelFeature _

/-- Arbitrary-degree cyclic contraction obtained from the generic
finite-dimensional Hilbert power-map construction. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerLinearMap
    (n : ℕ) :
    (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).FeatureHilbert →ₗ[ℝ]
      (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert :=
  RealHilbertKernelFeature.powLinearMap
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature
    specialUnitaryTwoNormalizedTraceHilbertKernelFeature
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceDegreeOneLinearMap n

/-- Hilbert-adjoint pullback of an arbitrary degree-`n` cyclic dual vector to
the genuine four-edge degree-`n` carrier. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback
    (n : ℕ)
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert) :
    (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).FeatureHilbert := by
  letI : FiniteDimensional ℝ
      ((specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).FeatureHilbert) :=
    RealHilbertKernelFeature.pow_finiteDimensional
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature n
  letI : FiniteDimensional ℝ
      ((specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert) :=
    RealHilbertKernelFeature.pow_finiteDimensional
      specialUnitaryTwoNormalizedTraceHilbertKernelFeature n
  exact LinearMap.adjoint
    (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerLinearMap n) q

/-- Exact adjoint identity for the arbitrary-degree four-edge pullback. -/
theorem specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner
    (n : ℕ)
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert)
    (v : (specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).FeatureHilbert) :
    inner ℝ
        (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q) v =
      inner ℝ q
        (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerLinearMap n v) := by
  letI : FiniteDimensional ℝ
      ((specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature.pow n).FeatureHilbert) :=
    RealHilbertKernelFeature.pow_finiteDimensional
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceEdgewiseFeature n
  letI : FiniteDimensional ℝ
      ((specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert) :=
    RealHilbertKernelFeature.pow_finiteDimensional
      specialUnitaryTwoNormalizedTraceHilbertKernelFeature n
  rw [specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback,
    LinearMap.adjoint_inner_left]

end

end MathlibAnalytic
end MGAP4D
