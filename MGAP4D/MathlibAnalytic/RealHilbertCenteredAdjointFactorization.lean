import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProduct

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A real Hilbert-space linear isometry, viewed as a continuous linear map,
has operator norm at most one. -/
theorem realHilbertLinearIsometry_opNorm_le_one
    (A : F →ₗᵢ[ℝ] E) :
    ‖A.toContinuousLinearMap‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  simpa using le_of_eq (A.norm_map x)

/-- The canonical synthesis associated with a Hilbert-space analysis is its
adjoint. -/
noncomputable def realHilbertAdjointSynthesis
    (A : F →ₗᵢ[ℝ] E) : E →L[ℝ] F :=
  (A.toContinuousLinearMap)†

/-- The canonical adjoint synthesis of a linear isometric analysis is
contractive. -/
theorem realHilbertAdjointSynthesis_opNorm_le_one
    (A : F →ₗᵢ[ℝ] E) :
    ‖realHilbertAdjointSynthesis A‖ ≤ 1 := by
  calc
    ‖realHilbertAdjointSynthesis A‖ = ‖A.toContinuousLinearMap‖ := by
      exact LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint
        A.toContinuousLinearMap
    _ ≤ 1 := realHilbertLinearIsometry_opNorm_le_one A

@[simp] theorem realHilbertAdjointSynthesis_apply
    (A : F →ₗᵢ[ℝ] E)
    (x : E) :
    realHilbertAdjointSynthesis A x =
      (A.toContinuousLinearMap)† x :=
  rfl

end

end MathlibAnalytic
end MGAP4D