import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureProduct
import Mathlib.Topology.ContinuousMap.Compact

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct InnerProductSpace

noncomputable section

/-- A fixed Hilbert-space dual probe turns a continuous feature map into a
continuous scalar matrix coefficient.  No basis or finite-dimensional
coordinate choice is used. -/
theorem RealHilbertKernelFeature.continuous_dualProbe
    {X : Type}
    [TopologicalSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (hC : Continuous C.feature)
    (q : C.FeatureHilbert) :
    Continuous (fun x => inner ℝ q (C.feature x)) := by
  exact continuous_const.inner hC

/-- On a compact source, every continuous Hilbert-feature matrix coefficient
is canonically a bounded continuous real observable. -/
noncomputable def RealHilbertKernelFeature.dualProbeBoundedContinuous
    {X : Type}
    [TopologicalSpace X]
    [CompactSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (hC : Continuous C.feature)
    (q : C.FeatureHilbert) :
    BoundedContinuousFunction X ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => inner ℝ q (C.feature x), C.continuous_dualProbe hC q⟩

@[simp]
theorem RealHilbertKernelFeature.dualProbeBoundedContinuous_apply
    {X : Type}
    [TopologicalSpace X]
    [CompactSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (hC : Continuous C.feature)
    (q : C.FeatureHilbert)
    (x : X) :
    C.dualProbeBoundedContinuous hC q x = inner ℝ q (C.feature x) := by
  rfl

/-- The scalar observable obtained from the dual probe is exactly the scalar
factor appearing when the feature itself is weighted before pairing. -/
theorem RealHilbertKernelFeature.inner_smul_feature_eq_mul_dualProbeBoundedContinuous
    {X : Type}
    [TopologicalSpace X]
    [CompactSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (hC : Continuous C.feature)
    (q : C.FeatureHilbert)
    (a : ℝ)
    (x : X) :
    inner ℝ q (a • C.feature x) =
      a * C.dualProbeBoundedContinuous hC q x := by
  rw [real_inner_smul_right]
  rfl

end

end MathlibAnalytic
end MGAP4D
