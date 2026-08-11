import MGAP4D.MathlibAnalytic.FiniteDimensionalRealHilbertCompletion
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureProduct
import Mathlib.RingTheory.TensorProduct.Finite

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct

noncomputable section

/-- Reindexing a Hilbert-kernel feature along an equality of scalar kernels does
not change finite-dimensionality of its feature carrier.  This small transport
lemma isolates the dependent cast introduced by the `simpa` in
`RealHilbertKernelFeature.pow`. -/
theorem RealHilbertKernelFeature.castFeatureHilbert_finiteDimensional
    {X : Type}
    {kernel₁ kernel₂ : X → X → ℝ}
    (h : kernel₁ = kernel₂)
    (C : RealHilbertKernelFeature X kernel₁)
    [FiniteDimensional ℝ C.FeatureHilbert] :
    FiniteDimensional ℝ
      ((h ▸ C : RealHilbertKernelFeature X kernel₂).FeatureHilbert) := by
  subst h
  infer_instance

/-- If the degree-one carrier of a real Hilbert-kernel feature is finite
dimensional, then every recursively completed tensor-power carrier produced by
`RealHilbertKernelFeature.pow` is finite dimensional.

The successor step is exactly the implementation of `pow`: finite-dimensional
base carrier tensor finite-dimensional preceding power carrier, followed by
the finite-dimensional Hilbert-completion bridge.  The final kernel reindexing
is discharged by `castFeatureHilbert_finiteDimensional`. -/
theorem RealHilbertKernelFeature.pow_finiteDimensional
    {X : Type}
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    [FiniteDimensional ℝ C.FeatureHilbert]
    (n : ℕ) :
    FiniteDimensional ℝ
      ((RealHilbertKernelFeature.pow C n).FeatureHilbert) := by
  induction n with
  | zero =>
      change FiniteDimensional ℝ ℝ
      infer_instance
  | succ n ih =>
      letI : FiniteDimensional ℝ
          ((RealHilbertKernelFeature.pow C n).FeatureHilbert) := ih
      letI : FiniteDimensional ℝ
          (C.FeatureHilbert ⊗[ℝ]
            (RealHilbertKernelFeature.pow C n).FeatureHilbert) := by
        infer_instance
      let D :=
        RealHilbertKernelFeature.mul C
          (RealHilbertKernelFeature.pow C n)
      letI : FiniteDimensional ℝ D.FeatureHilbert := by
        change FiniteDimensional ℝ
          (UniformSpace.Completion
            (C.FeatureHilbert ⊗[ℝ]
              (RealHilbertKernelFeature.pow C n).FeatureHilbert))
        exact finiteDimensional_realHilbert_completion
          (C.FeatureHilbert ⊗[ℝ]
            (RealHilbertKernelFeature.pow C n).FeatureHilbert)
      have hKernel :
          (fun x y => kernel x y * kernel x y ^ n) =
            (fun x y => kernel x y ^ (n + 1)) := by
        funext x y
        rw [pow_succ]
      have hCast :
          FiniteDimensional ℝ
            ((hKernel ▸ D :
              RealHilbertKernelFeature X
                (fun x y => kernel x y ^ (n + 1))).FeatureHilbert) :=
        RealHilbertKernelFeature.castFeatureHilbert_finiteDimensional
          hKernel D
      simpa [D, RealHilbertKernelFeature.pow, pow_succ, mul_comm] using hCast

end

end MathlibAnalytic
end MGAP4D
