import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry

noncomputable section

namespace MGAP4D
namespace MathlibAnalytic

variable {H B : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B]

/-- The closed Hilbert range of a real linear isometry. -/
abbrev realLinearIsometryRange (J : H →ₗᵢ[ℝ] B) : Submodule ℝ B :=
  LinearMap.range J.toLinearMap

/-- The range of an isometry from a complete space is complete, hence admits
orthogonal projection even when the ambient Hilbert space is not assumed
complete. -/
noncomputable instance realLinearIsometryRangeCompleteSpace
    (J : H →ₗᵢ[ℝ] B) :
    CompleteSpace (realLinearIsometryRange J) := by
  change CompleteSpace ((⊤ : Submodule ℝ H).map J.toLinearMap)
  exact J.completeSpace_map (⊤ : Submodule ℝ H)

/-- Canonical contractive left inverse of a Hilbert-space isometric embedding:
first project orthogonally to its closed range, then use the inverse of the
isometric equivalence onto that range. -/
noncomputable def realLinearIsometryProjectedInverse
    (J : H →ₗᵢ[ℝ] B) :
    B →L[ℝ] H :=
  J.equivRange.symm.toLinearIsometry.toContinuousLinearMap.comp
    (realLinearIsometryRange J).orthogonalProjection

/-- The projected inverse is an exact left inverse on the embedded Hilbert
space. -/
@[simp] theorem realLinearIsometryProjectedInverse_apply_map
    (J : H →ₗᵢ[ℝ] B) (x : H) :
    realLinearIsometryProjectedInverse J (J x) = x := by
  change J.equivRange.symm
      ((realLinearIsometryRange J).orthogonalProjection (J x)) = x
  have hproj :
      (realLinearIsometryRange J).orthogonalProjection (J x) =
        J.equivRange x := by
    simpa [realLinearIsometryRange] using
      (realLinearIsometryRange J).orthogonalProjection_mem_subspace_eq_self
        (J.equivRange x)
  rw [hproj]
  exact J.equivRange.symm_apply_apply x

/-- Orthogonal projection followed by an isometric inverse is contractive. -/
theorem realLinearIsometryProjectedInverse_norm_le
    (J : H →ₗᵢ[ℝ] B) (y : B) :
    ‖realLinearIsometryProjectedInverse J y‖ ≤ ‖y‖ := by
  change ‖J.equivRange.symm
      ((realLinearIsometryRange J).orthogonalProjection y)‖ ≤ ‖y‖
  rw [J.equivRange.symm.norm_map]
  exact (realLinearIsometryRange J).norm_orthogonalProjection_apply_le y

/-- The projected inverse has operator norm at most one. -/
theorem realLinearIsometryProjectedInverse_opNorm_le
    (J : H →ₗᵢ[ℝ] B) :
    ‖realLinearIsometryProjectedInverse J‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound
    (realLinearIsometryProjectedInverse J) zero_le_one ?_
  intro y
  simpa using realLinearIsometryProjectedInverse_norm_le J y

/-- Extend an operator on an isometrically embedded Hilbert space to the whole
ambient Hilbert space by zero on the orthogonal complement of the range.

Concretely this is `J ∘ T ∘ J⁻¹ ∘ P_range`.  No surjectivity of `J` is
required. -/
noncomputable def realLinearIsometryProjectedCompression
    (J : H →ₗᵢ[ℝ] B)
    (T : H →L[ℝ] H) :
    B →L[ℝ] B :=
  J.toContinuousLinearMap.comp
    (T.comp (realLinearIsometryProjectedInverse J))

/-- Projected compression agrees exactly with conjugation on the embedded
Hilbert space. -/
@[simp] theorem realLinearIsometryProjectedCompression_apply_map
    (J : H →ₗᵢ[ℝ] B)
    (T : H →L[ℝ] H)
    (x : H) :
    realLinearIsometryProjectedCompression J T (J x) = J (T x) := by
  simp [realLinearIsometryProjectedCompression]

/-- Pointwise norm control for projected compression. -/
theorem realLinearIsometryProjectedCompression_norm_le
    (J : H →ₗᵢ[ℝ] B)
    (T : H →L[ℝ] H)
    (y : B) :
    ‖realLinearIsometryProjectedCompression J T y‖ ≤ ‖T‖ * ‖y‖ := by
  change ‖J (T (realLinearIsometryProjectedInverse J y))‖ ≤ ‖T‖ * ‖y‖
  rw [J.norm_map]
  calc
    ‖T (realLinearIsometryProjectedInverse J y)‖ ≤
        ‖T‖ * ‖realLinearIsometryProjectedInverse J y‖ :=
      T.le_opNorm _
    _ ≤ ‖T‖ * ‖y‖ := by
      exact mul_le_mul_of_nonneg_left
        (realLinearIsometryProjectedInverse_norm_le J y) (norm_nonneg T)

/-- Compression through an isometric Hilbert realization does not increase
operator norm. -/
theorem realLinearIsometryProjectedCompression_opNorm_le
    (J : H →ₗᵢ[ℝ] B)
    (T : H →L[ℝ] H) :
    ‖realLinearIsometryProjectedCompression J T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound
    (realLinearIsometryProjectedCompression J T) (norm_nonneg T) ?_
  intro y
  exact realLinearIsometryProjectedCompression_norm_le J T y

end MathlibAnalytic
end MGAP4D

end
