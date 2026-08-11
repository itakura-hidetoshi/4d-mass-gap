import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeNormalizedTraceHilbertPullback
import Mathlib.Topology.Algebra.LinearMapCompletion

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct InnerProduct InnerProductSpace

noncomputable section

private theorem cyclicFourEdgeHilbertPowerTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

/-- The degree-one cyclic four-edge source kernel is defined by the canonical
Hilbert inner product of the four normalized edge features.  Keeping the kernel
at the feature level makes the subsequent power recursion use exactly the same
completed tensor bracketing as `RealHilbertKernelFeature.pow`. -/
def specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureKernel
    (x y : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  inner ℝ
    (specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor x)
    (specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor y)

/-- The four-edge degree-one source as a genuine Hilbert-kernel feature.  Its
carrier is the already validated degree-one four-edge Hilbert tensor. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature :
    RealHilbertKernelFeature
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureKernel where
  FeatureHilbert := SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace
  feature := specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor
  kernel_eq_inner := by
    intro x y
    rfl

/-- The one-edge normalized relative-trace Hilbert feature used as the target
of the cyclic four-edge contraction. -/
noncomputable def specialUnitaryTwoNormalizedTraceKernelFeature :
    RealHilbertKernelFeature
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (specialUnitaryNormalizedTraceRelativeKernel 2) :=
  specialUnitaryNormalizedTraceRelativeKernelFeature
    2 cyclicFourEdgeHilbertPowerTwoRankPositive

/-- Continuous form of the validated degree-one cyclic four-edge contraction.
Finite dimensionality of the algebraic Hilbert tensor makes the linear map
continuous without adding a new topology. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTraceContractionCLM :
    (specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.FeatureHilbert) →L[ℝ]
      specialUnitaryTwoNormalizedTraceKernelFeature.FeatureHilbert := by
  change SpecialUnitaryTwoNormalizedTraceFourEdgeHilbertTensorSpace →L[ℝ]
    SpecialUnitaryMatrixRealFeatureSpace 2
  exact specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction.toContinuousLinearMap

/-- The continuous degree-one contraction sends the four-edge source feature to
exactly the normalized relative-trace feature of the cyclic holonomy. -/
theorem specialUnitaryTwoCyclicFourEdgeNormalizedTraceContractionCLM_feature
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoCyclicFourEdgeNormalizedTraceContractionCLM
        (specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.feature x) =
      specialUnitaryTwoNormalizedTraceKernelFeature.feature
        (haarFinFourCyclicPlaquetteWord x) := by
  change specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction
      (specialUnitaryTwoCyclicFourEdgeNormalizedTraceFeatureTensor x) =
    (specialUnitaryNormalizedTraceRelativeKernelFeature
      2 cyclicFourEdgeHilbertPowerTwoRankPositive).feature
      (haarFinFourCyclicPlaquetteWord x)
  rw [specialUnitaryTwoCyclicFourEdgeNormalizedTraceContraction_featureTensor]
  exact specialUnitaryTwoNormalizedTraceFeatureVector_eq_kernelFeature
    (haarFinFourCyclicPlaquetteWord x)

/-- Recursive Hilbert lift of the degree-one cyclic four-edge contraction to
all tensor powers.

At degree zero this is the identity on `ℝ`.  At a successor degree, Mathlib's
`TensorProduct.mapL` applies the degree-one contraction to the new tensor leg
and the already constructed map to the preceding degree; `completion` then
extends that bounded tensor map to the exact completed carrier used by
`RealHilbertKernelFeature.pow`. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerContraction :
    ∀ n : ℕ,
      (specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.pow n).FeatureHilbert →L[ℝ]
        (specialUnitaryTwoNormalizedTraceKernelFeature.pow n).FeatureHilbert
  | 0 => ContinuousLinearMap.id ℝ ℝ
  | n + 1 => by
      change UniformSpace.Completion
          (specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.FeatureHilbert ⊗[ℝ]
            (specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.pow n).FeatureHilbert) →L[ℝ]
        UniformSpace.Completion
          (specialUnitaryTwoNormalizedTraceKernelFeature.FeatureHilbert ⊗[ℝ]
            (specialUnitaryTwoNormalizedTraceKernelFeature.pow n).FeatureHilbert)
      exact
        (TensorProduct.mapL
          specialUnitaryTwoCyclicFourEdgeNormalizedTraceContractionCLM
          (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerContraction n)).completion

/-- Every degree-`n` pure four-edge feature is transported to the degree-`n`
normalized relative-trace feature of the cyclic holonomy.  This is the exact
power-level compatibility needed before inserting the four temporal companion
edges into the Wilson Taylor expansion. -/
theorem specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerContraction_feature
    (n : ℕ)
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerContraction n
        ((specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.pow n).feature x) =
      (specialUnitaryTwoNormalizedTraceKernelFeature.pow n).feature
        (haarFinFourCyclicPlaquetteWord x) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (TensorProduct.mapL
          specialUnitaryTwoCyclicFourEdgeNormalizedTraceContractionCLM
          (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerContraction n)).completion
          (((specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.feature x ⊗ₜ[ℝ]
            (specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.pow n).feature x) :
              specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.FeatureHilbert ⊗[ℝ]
                (specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.pow n).FeatureHilbert) :
            UniformSpace.Completion
              (specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.FeatureHilbert ⊗[ℝ]
                (specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.pow n).FeatureHilbert)) =
          (((specialUnitaryTwoNormalizedTraceKernelFeature.feature
              (haarFinFourCyclicPlaquetteWord x) ⊗ₜ[ℝ]
            (specialUnitaryTwoNormalizedTraceKernelFeature.pow n).feature
              (haarFinFourCyclicPlaquetteWord x)) :
              specialUnitaryTwoNormalizedTraceKernelFeature.FeatureHilbert ⊗[ℝ]
                (specialUnitaryTwoNormalizedTraceKernelFeature.pow n).FeatureHilbert) :
            UniformSpace.Completion
              (specialUnitaryTwoNormalizedTraceKernelFeature.FeatureHilbert ⊗[ℝ]
                (specialUnitaryTwoNormalizedTraceKernelFeature.pow n).FeatureHilbert))
      rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul,
        specialUnitaryTwoCyclicFourEdgeNormalizedTraceContractionCLM_feature, ih]

/-- Hilbert-adjoint pullback of an arbitrary degree-`n` normalized cyclic dual
vector to the four-edge degree-`n` Fock carrier. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback
    (n : ℕ)
    (q : (specialUnitaryTwoNormalizedTraceKernelFeature.pow n).FeatureHilbert) :
    (specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.pow n).FeatureHilbert :=
  ContinuousLinearMap.adjoint
    (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerContraction n) q

/-- Exact degree-`n` adjoint identity against every pure four-edge feature. -/
theorem specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_feature
    (n : ℕ)
    (q : (specialUnitaryTwoNormalizedTraceKernelFeature.pow n).FeatureHilbert)
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    inner ℝ
        (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
        ((specialUnitaryTwoCyclicFourEdgeNormalizedTraceKernelFeature.pow n).feature x) =
      inner ℝ q
        ((specialUnitaryTwoNormalizedTraceKernelFeature.pow n).feature
          (haarFinFourCyclicPlaquetteWord x)) := by
  rw [specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback,
    ContinuousLinearMap.adjoint_inner_left,
    specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerContraction_feature]

end

end MathlibAnalytic
end MGAP4D
