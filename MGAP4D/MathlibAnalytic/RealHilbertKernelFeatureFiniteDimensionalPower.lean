import MGAP4D.MathlibAnalytic.FiniteDimensionalRealHilbertCompletion
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureProduct
import Mathlib.RingTheory.TensorProduct.Finite

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct

noncomputable section

/-- If the degree-one carrier of a real Hilbert-kernel feature is finite
dimensional, then every recursively completed tensor-power carrier produced by
`RealHilbertKernelFeature.pow` is finite dimensional.

The successor step is exactly the implementation of `pow`: finite-dimensional
base carrier tensor finite-dimensional preceding power carrier, followed by
the finite-dimensional Hilbert-completion bridge. -/
noncomputable def RealHilbertKernelFeature.powFiniteDimensional
    {X : Type}
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    [FiniteDimensional ℝ C.FeatureHilbert] :
    ∀ n : ℕ,
      FiniteDimensional ℝ
        ((RealHilbertKernelFeature.pow C n).FeatureHilbert)
  | 0 => by
      change FiniteDimensional ℝ ℝ
      infer_instance
  | n + 1 => by
      letI : FiniteDimensional ℝ
          ((RealHilbertKernelFeature.pow C n).FeatureHilbert) :=
        RealHilbertKernelFeature.powFiniteDimensional C n
      letI : FiniteDimensional ℝ
          (C.FeatureHilbert ⊗[ℝ]
            (RealHilbertKernelFeature.pow C n).FeatureHilbert) := by
        infer_instance
      simpa [RealHilbertKernelFeature.pow, RealHilbertKernelFeature.mul,
        pow_succ, mul_comm] using
        finiteDimensional_realHilbert_completion
          (C.FeatureHilbert ⊗[ℝ]
            (RealHilbertKernelFeature.pow C n).FeatureHilbert)

end

end MathlibAnalytic
end MGAP4D
