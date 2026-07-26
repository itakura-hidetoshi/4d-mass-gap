import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set

universe u v

namespace ContinuousLinearMap

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous real-linear map whose image lies in one submodule and which
preserves every vector norm. -/
structure IsometricSubmoduleRangeData
    (f : E →L[ℝ] F)
    (S : Submodule ℝ F) where
  map_mem : ∀ x, f x ∈ S
  norm_map : ∀ x, ‖f x‖ = ‖x‖

namespace IsometricSubmoduleRangeData

variable {f : E →L[ℝ] F} {S : Submodule ℝ F}

/-- Restrict an isometric continuous linear map to the submodule containing its
range. -/
noncomputable def toSubmodule
    (D : IsometricSubmoduleRangeData f S) : E →L[ℝ] S :=
  f.codRestrict S D.map_mem

@[simp] theorem coe_toSubmodule
    (D : IsometricSubmoduleRangeData f S)
    (x : E) :
    (D.toSubmodule x : F) = f x :=
  rfl

/-- Codomain restriction to the containing submodule preserves the original
isometry. -/
theorem norm_toSubmodule
    (D : IsometricSubmoduleRangeData f S)
    (x : E) :
    ‖D.toSubmodule x‖ = ‖x‖ := by
  simpa only [Submodule.norm_coe, D.coe_toSubmodule] using D.norm_map x

/-- The norm-preserving map bundled as a linear isometry. -/
noncomputable def toLinearIsometry
    (D : IsometricSubmoduleRangeData f S) : E →ₗᵢ[ℝ] S where
  toLinearMap := D.toSubmodule.toLinearMap
  norm_map' := D.norm_toSubmodule

end IsometricSubmoduleRangeData

/-- A norm-preserving continuous real-linear map preserves the real inner
product. -/
theorem inner_map_map_of_norm_map
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    (f : E →L[ℝ] F)
    (hNorm : ∀ x, ‖f x‖ = ‖x‖)
    (x y : E) :
    inner ℝ (f x) (f y) = inner ℝ x y := by
  let e : E →ₗᵢ[ℝ] F :=
    { toLinearMap := f.toLinearMap
      norm_map' := hNorm }
  exact e.inner_map_map x y

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
