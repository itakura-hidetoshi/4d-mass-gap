import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalOperatorNormIsometry
import Mathlib.Analysis.Normed.Operator.LinearIsometry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Diagonal complexification preserves addition of bounded real-linear endomorphisms. -/
@[simp]
theorem diagonalComplexification_add (S T : H →L[ℝ] H) :
    diagonalComplexification (S + T) =
      diagonalComplexification S + diagonalComplexification T := by
  apply ContinuousLinearMap.ext
  intro z
  apply Prod.ext <;> rfl

/-- Diagonal complexification preserves real scalar multiplication on operator spaces. -/
@[simp]
theorem diagonalComplexification_smul_real (r : ℝ) (T : H →L[ℝ] H) :
    diagonalComplexification (r • T) = r • diagonalComplexification T := by
  rw [← Complex.coe_smul r (diagonalComplexification T)]
  apply ContinuousLinearMap.ext
  intro z
  rw [smul_apply]
  apply Prod.ext <;>
    simp [complex_smul_re, complex_smul_im]

/-- Diagonal complexification, bundled as a real-linear isometric embedding between operator
spaces. -/
noncomputable def diagonalComplexificationLinearIsometry :
    (H →L[ℝ] H) →ₗᵢ[ℝ]
      (StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) where
  toLinearMap :=
    { toFun := diagonalComplexification
      map_add' := diagonalComplexification_add
      map_smul' := diagonalComplexification_smul_real }
  norm_map' := norm_diagonalComplexification

@[simp]
theorem diagonalComplexificationLinearIsometry_apply (T : H →L[ℝ] H) :
    diagonalComplexificationLinearIsometry T = diagonalComplexification T :=
  rfl

/-- The bundled operator complexification is an isometry. -/
theorem diagonalComplexification_isometry :
    Isometry (diagonalComplexification (H := H)) :=
  diagonalComplexificationLinearIsometry.isometry

@[simp]
theorem diagonalComplexification_zero :
    diagonalComplexification (0 : H →L[ℝ] H) = 0 := by
  change diagonalComplexificationLinearIsometry (H := H) 0 = 0
  exact diagonalComplexificationLinearIsometry.map_zero

@[simp]
theorem diagonalComplexification_neg (T : H →L[ℝ] H) :
    diagonalComplexification (-T) = -diagonalComplexification T := by
  change diagonalComplexificationLinearIsometry (H := H) (-T) =
    -diagonalComplexificationLinearIsometry T
  exact diagonalComplexificationLinearIsometry.map_neg T

@[simp]
theorem diagonalComplexification_sub (S T : H →L[ℝ] H) :
    diagonalComplexification (S - T) =
      diagonalComplexification S - diagonalComplexification T := by
  change diagonalComplexificationLinearIsometry (H := H) (S - T) =
    diagonalComplexificationLinearIsometry S - diagonalComplexificationLinearIsometry T
  exact diagonalComplexificationLinearIsometry.map_sub S T

/-- Diagonal complexification preserves the multiplicative identity. -/
@[simp]
theorem diagonalComplexification_one :
    diagonalComplexification (1 : H →L[ℝ] H) =
      (1 : StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) := by
  change diagonalComplexification (ContinuousLinearMap.id ℝ H) =
    ContinuousLinearMap.id ℂ (StandardRealHilbertComplexification H)
  exact diagonalComplexification_id

/-- Diagonal complexification preserves multiplication, i.e. operator composition. -/
@[simp]
theorem diagonalComplexification_mul (S T : H →L[ℝ] H) :
    diagonalComplexification (S * T) =
      diagonalComplexification S * diagonalComplexification T := by
  change diagonalComplexification (S.comp T) =
    (diagonalComplexification S).comp (diagonalComplexification T)
  exact diagonalComplexification_comp S T

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D