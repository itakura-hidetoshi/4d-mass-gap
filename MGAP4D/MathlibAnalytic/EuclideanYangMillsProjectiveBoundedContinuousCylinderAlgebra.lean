import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveBoundedContinuousCylinder

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsProjectiveCylinderFamily

variable (F : EuclideanYangMillsProjectiveCylinderFamily)
variable [∀ x, TopologicalSpace (F.fieldValue x)]

/-- Finite-coordinate bounded-continuous cylinder lift as a real algebra
homomorphism.

Multiplication is handled before any OS or positive-half pullback is applied:
the projective cylinder observable is literally obtained by precomposition with
the canonical finite restriction map.  Thus later physical realization layers
can transport the actual cylinder algebra without assuming multiplicativity of
a merely linear positive-half pullback. -/
noncomputable def boundedContinuousCylinderLiftAlgHom
    (J : Finset EuclideanFourSpace) :
    BoundedContinuousFunction (∀ x : J, F.fieldValue x) ℝ →ₐ[ℝ]
      BoundedContinuousFunction F.Configuration ℝ where
  toFun := F.boundedContinuousCylinderLift J
  map_zero' := F.boundedContinuousCylinderLift_zero J
  map_one' := F.boundedContinuousCylinderLift_one J
  map_add' := F.boundedContinuousCylinderLift_add J
  map_mul' := F.boundedContinuousCylinderLift_mul J
  commutes' := by
    intro r
    ext A
    rfl

@[simp] theorem boundedContinuousCylinderLiftAlgHom_apply
    (J : Finset EuclideanFourSpace)
    (f : BoundedContinuousFunction (∀ x : J, F.fieldValue x) ℝ) :
    F.boundedContinuousCylinderLiftAlgHom J f =
      F.boundedContinuousCylinderLift J f :=
  rfl

@[simp] theorem boundedContinuousCylinderLiftAlgHom_eval
    (J : Finset EuclideanFourSpace)
    (f : BoundedContinuousFunction (∀ x : J, F.fieldValue x) ℝ)
    (A : F.Configuration) :
    F.boundedContinuousCylinderLiftAlgHom J f A = f (J.restrict A) :=
  rfl

end EuclideanYangMillsProjectiveCylinderFamily

end

end MathlibAnalytic
end MGAP4D
