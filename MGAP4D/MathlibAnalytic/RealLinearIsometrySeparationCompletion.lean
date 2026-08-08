import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.Analysis.Normed.Group.HomCompletion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.LinearIsometry

namespace MGAP4D
namespace MathlibAnalytic

open UniformSpace

noncomputable section

variable {E F : Type*}
  [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A real linear isometry out of a seminormed space vanishes on every
zero-seminorm vector.  This is the exact compatibility needed to descend
through Mathlib's `SeparationQuotient`. -/
theorem realLinearIsometry_eq_zero_of_norm_eq_zero
    (f : E →ₗᵢ[ℝ] F) (x : E) (hx : ‖x‖ = 0) :
    f x = 0 := by
  apply norm_eq_zero.mp
  rw [f.norm_map, hx]

/-- A real linear isometry from a seminormed space descends canonically to the
Hausdorff separation quotient.

The quotient introduces no new analytic assumption: well-definedness follows
from exact norm preservation, hence zero-seminorm differences map to zero. -/
noncomputable def realLinearIsometrySeparationQuotient
    (f : E →ₗᵢ[ℝ] F) :
    SeparationQuotient E →ₗᵢ[ℝ] F where
  toLinearMap :=
    { toFun := SeparationQuotient.lift f
        (SeparationQuotient.apply_eq_apply_of_inseparable
          f.toLinearMap
          (fun x hx => realLinearIsometry_eq_zero_of_norm_eq_zero f x hx))
      map_add' := by
        intro x y
        obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
        obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk y
        exact f.map_add x y
      map_smul' := by
        intro r x
        obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
        exact f.map_smul r x }
  norm_map' := by
    intro x
    obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
    simpa using f.norm_map x

@[simp] theorem realLinearIsometrySeparationQuotient_mk
    (f : E →ₗᵢ[ℝ] F) (x : E) :
    realLinearIsometrySeparationQuotient f (SeparationQuotient.mk x) = f x :=
  rfl

variable [CompleteSpace F]

/-- Extend a real linear isometry from a normed space to its uniform
completion, directly into a complete target.

Mathlib supplies the additive extension.  Real homogeneity and norm
preservation are then extended from the dense original carrier by completion
induction and continuity. -/
noncomputable def realLinearIsometryCompletionExtension
    (f : E →ₗᵢ[ℝ] F) :
    Completion E →ₗᵢ[ℝ] F := by
  let fAdd : E →+ F := f.toLinearMap.toAddMonoidHom
  let fExt : Completion E →+ F := fAdd.extension f.continuous
  have hfExt : Continuous fExt :=
    fAdd.continuous_extension f.continuous
  have hfExt_coe (x : E) :
      fExt (x : Completion E) = f x := by
    exact AddMonoidHom.extension_coe fAdd f.continuous x
  let fLin : Completion E →ₗ[ℝ] F :=
    { toFun := fExt
      map_add' := fExt.map_add
      map_smul' := by
        intro r x
        induction x using Completion.induction_on with
        | hp =>
            exact isClosed_eq
              (hfExt.comp (continuous_const_smul r))
              (hfExt.const_smul r)
        | ih x =>
            rw [← Completion.coe_smul, hfExt_coe]
            simpa using f.map_smul r x }
  exact
    { toLinearMap := fLin
      norm_map' := by
        intro x
        induction x using Completion.induction_on with
        | hp =>
            exact isClosed_eq
              (continuous_norm.comp hfExt)
              continuous_norm
        | ih x =>
            change ‖fExt (x : Completion E)‖ = ‖(x : Completion E)‖
            rw [hfExt_coe, Completion.norm_coe]
            exact f.norm_map x }

@[simp] theorem realLinearIsometryCompletionExtension_coe
    (f : E →ₗᵢ[ℝ] F) (x : E) :
    realLinearIsometryCompletionExtension f (x : Completion E) = f x := by
  change
    (f.toLinearMap.toAddMonoidHom.extension f.continuous)
        (x : Completion E) = f x
  exact AddMonoidHom.extension_coe _ f.continuous x

/-- Combined canonical lift: first remove the seminorm-zero directions, then
complete.  This is the generic Mathlib mechanism needed by the physical OS
boundary realization. -/
noncomputable def realLinearIsometrySeparationCompletion
    (f : E →ₗᵢ[ℝ] F) :
    Completion (SeparationQuotient E) →ₗᵢ[ℝ] F :=
  realLinearIsometryCompletionExtension
    (realLinearIsometrySeparationQuotient f)

@[simp] theorem realLinearIsometrySeparationCompletion_coe_mk
    (f : E →ₗᵢ[ℝ] F) (x : E) :
    realLinearIsometrySeparationCompletion f
        ((SeparationQuotient.mk x : SeparationQuotient E) :
          Completion (SeparationQuotient E)) =
      f x := by
  rw [realLinearIsometrySeparationCompletion,
    realLinearIsometryCompletionExtension_coe,
    realLinearIsometrySeparationQuotient_mk]

end

end MathlibAnalytic
end MGAP4D