import Mathlib.Topology.ContinuousMap.Compact

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On a compact domain, the canonical passage from a real continuous function
to its bounded-continuous representative is a real algebra homomorphism.

Mathlib already supplies the underlying linear isometry
`ContinuousMap.linearIsometryBoundedOfCompact`; this wrapper records the
pointwise multiplicative structure that is needed when an actual finite Wilson
cylinder algebra is transported before entering the merely-linear OS pullback
layer. -/
noncomputable def continuousMapAlgHomBoundedOfCompact
    (X : Type*) [TopologicalSpace X] [CompactSpace X] :
    C(X, ℝ) →ₐ[ℝ] BoundedContinuousFunction X ℝ where
  toFun := ContinuousMap.linearIsometryBoundedOfCompact X ℝ ℝ
  map_zero' := by
    ext x
    rfl
  map_one' := by
    ext x
    rfl
  map_add' := by
    intro f g
    ext x
    rfl
  map_mul' := by
    intro f g
    ext x
    rfl
  commutes' := by
    intro r
    ext x
    rfl

@[simp] theorem continuousMapAlgHomBoundedOfCompact_apply
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    (f : C(X, ℝ)) (x : X) :
    continuousMapAlgHomBoundedOfCompact X f x = f x :=
  rfl

@[simp] theorem continuousMapAlgHomBoundedOfCompact_toLinearMap
    (X : Type*) [TopologicalSpace X] [CompactSpace X] :
    (continuousMapAlgHomBoundedOfCompact X).toLinearMap =
      (ContinuousMap.linearIsometryBoundedOfCompact X ℝ ℝ).toLinearMap :=
  rfl

end

end MathlibAnalytic
end MGAP4D
