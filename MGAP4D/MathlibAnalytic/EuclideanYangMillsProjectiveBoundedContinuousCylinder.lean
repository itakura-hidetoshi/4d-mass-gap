import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveContinuumMeasure
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Bounded.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsProjectiveCylinderFamily

variable (F : EuclideanYangMillsProjectiveCylinderFamily)
variable [∀ x, TopologicalSpace (F.fieldValue x)]

/-- Lift a bounded continuous finite-coordinate cylinder observable to the full
projective continuum configuration by precomposition with the canonical finite
restriction map.

This is a purely topological construction.  It uses the actual projective
continuum carrier `F.Configuration = ∀ x, F.fieldValue x` and Mathlib's
continuity of finite restriction; no density, extension, surjectivity, measure,
or OS hypothesis is required. -/
noncomputable def boundedContinuousCylinderLift
    (J : Finset EuclideanFourSpace)
    (f : BoundedContinuousFunction (∀ x : J, F.fieldValue x) ℝ) :
    BoundedContinuousFunction F.Configuration ℝ :=
  f.compContinuous ⟨J.restrict, Finset.continuous_restrict J⟩

@[simp] theorem boundedContinuousCylinderLift_apply
    (J : Finset EuclideanFourSpace)
    (f : BoundedContinuousFunction (∀ x : J, F.fieldValue x) ℝ)
    (A : F.Configuration) :
    F.boundedContinuousCylinderLift J f A = f (J.restrict A) :=
  rfl

@[simp] theorem boundedContinuousCylinderLift_zero
    (J : Finset EuclideanFourSpace) :
    F.boundedContinuousCylinderLift J
        (0 : BoundedContinuousFunction (∀ x : J, F.fieldValue x) ℝ) = 0 := by
  ext A
  rfl

@[simp] theorem boundedContinuousCylinderLift_one
    (J : Finset EuclideanFourSpace) :
    F.boundedContinuousCylinderLift J
        (1 : BoundedContinuousFunction (∀ x : J, F.fieldValue x) ℝ) = 1 := by
  ext A
  rfl

@[simp] theorem boundedContinuousCylinderLift_add
    (J : Finset EuclideanFourSpace)
    (f g : BoundedContinuousFunction (∀ x : J, F.fieldValue x) ℝ) :
    F.boundedContinuousCylinderLift J (f + g) =
      F.boundedContinuousCylinderLift J f +
        F.boundedContinuousCylinderLift J g := by
  ext A
  rfl

@[simp] theorem boundedContinuousCylinderLift_smul
    (J : Finset EuclideanFourSpace)
    (r : ℝ)
    (f : BoundedContinuousFunction (∀ x : J, F.fieldValue x) ℝ) :
    F.boundedContinuousCylinderLift J (r • f) =
      r • F.boundedContinuousCylinderLift J f := by
  ext A
  rfl

@[simp] theorem boundedContinuousCylinderLift_mul
    (J : Finset EuclideanFourSpace)
    (f g : BoundedContinuousFunction (∀ x : J, F.fieldValue x) ℝ) :
    F.boundedContinuousCylinderLift J (f * g) =
      F.boundedContinuousCylinderLift J f *
        F.boundedContinuousCylinderLift J g := by
  ext A
  rfl

/-- The finite-coordinate cylinder lift is real-linear.  This is the form used
by later positive-time range and approximation arguments. -/
noncomputable def boundedContinuousCylinderLiftLinearMap
    (J : Finset EuclideanFourSpace) :
    BoundedContinuousFunction (∀ x : J, F.fieldValue x) ℝ →ₗ[ℝ]
      BoundedContinuousFunction F.Configuration ℝ where
  toFun := F.boundedContinuousCylinderLift J
  map_add' := F.boundedContinuousCylinderLift_add J
  map_smul' := F.boundedContinuousCylinderLift_smul J

@[simp] theorem boundedContinuousCylinderLiftLinearMap_apply
    (J : Finset EuclideanFourSpace)
    (f : BoundedContinuousFunction (∀ x : J, F.fieldValue x) ℝ) :
    F.boundedContinuousCylinderLiftLinearMap J f =
      F.boundedContinuousCylinderLift J f :=
  rfl

end EuclideanYangMillsProjectiveCylinderFamily

end

end MathlibAnalytic
end MGAP4D
