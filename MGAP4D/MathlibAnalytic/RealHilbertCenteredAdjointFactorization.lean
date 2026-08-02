import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProduct

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The inclusion of a real Hilbert subspace has operator norm at most one. -/
theorem realHilbert_subtypeL_opNorm_le_one
    (U : Submodule ℝ E) :
    ‖U.subtypeL‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  simp

/-- Orthogonal projection onto a real Hilbert subspace has operator norm at
most one. -/
theorem realHilbert_orthogonalProjectionOnto_opNorm_le_one
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] :
    ‖U.orthogonalProjectionOnto‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  simpa [Submodule.orthogonalProjectionOnto] using
    U.norm_projection_orthogonal_le x

/-- Lift an operator on a closed real Hilbert subspace to the ambient space by
orthogonally projecting into the subspace, applying the operator, and then
including the result. -/
noncomputable def realHilbertCenteredLift
    (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (T : U →L[ℝ] U) : E →L[ℝ] E :=
  U.subtypeL.comp (T.comp U.orthogonalProjectionOnto)

/-- A norm bound on a centered operator survives its canonical ambient-space
lift. -/
theorem realHilbertCenteredLift_opNorm_le
    (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (T : U →L[ℝ] U)
    (r : ℝ)
    (hr : 0 ≤ r)
    (hT : ‖T‖ ≤ r) :
    ‖realHilbertCenteredLift U T‖ ≤ r := by
  unfold realHilbertCenteredLift
  calc
    ‖U.subtypeL.comp (T.comp U.orthogonalProjectionOnto)‖ ≤
        ‖U.subtypeL‖ * ‖T.comp U.orthogonalProjectionOnto‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖U.subtypeL‖ * (‖T‖ * ‖U.orthogonalProjectionOnto‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le T U.orthogonalProjectionOnto)
        (norm_nonneg _)
    _ ≤ 1 * (r * 1) := by
      exact mul_le_mul
        (realHilbert_subtypeL_opNorm_le_one U)
        (mul_le_mul hT
          (realHilbert_orthogonalProjectionOnto_opNorm_le_one U)
          (norm_nonneg _) hr)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        zero_le_one
    _ = r := by ring

/-- Include a linear isometric boundary analysis map into the ambient Gibbs
Hilbert space. -/
noncomputable def realHilbertAnalysisAmbient
    (U : Submodule ℝ E)
    (A : F →ₗᵢ[ℝ] U) : F →L[ℝ] E :=
  U.subtypeL.comp A.toContinuousLinearMap

/-- The ambient realization of a linear isometric analysis map is
contractive. -/
theorem realHilbertAnalysisAmbient_opNorm_le_one
    (U : Submodule ℝ E)
    (A : F →ₗᵢ[ℝ] U) :
    ‖realHilbertAnalysisAmbient U A‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  simp [realHilbertAnalysisAmbient]

/-- The canonical synthesis associated with a centered analysis is the
adjoint of the analysis after orthogonal projection to the centered sector. -/
noncomputable def realHilbertAdjointSynthesis
    (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (A : F →ₗᵢ[ℝ] U) : E →L[ℝ] F :=
  (A.toContinuousLinearMap†).comp U.orthogonalProjectionOnto

/-- The canonical adjoint synthesis of a linear isometric analysis is
contractive. -/
theorem realHilbertAdjointSynthesis_opNorm_le_one
    (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (A : F →ₗᵢ[ℝ] U) :
    ‖realHilbertAdjointSynthesis U A‖ ≤ 1 := by
  unfold realHilbertAdjointSynthesis
  calc
    ‖(A.toContinuousLinearMap†).comp U.orthogonalProjectionOnto‖ ≤
        ‖A.toContinuousLinearMap†‖ * ‖U.orthogonalProjectionOnto‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖A.toContinuousLinearMap‖ * ‖U.orthogonalProjectionOnto‖ := by
      rw [LinearIsometryEquiv.norm_map]
    _ ≤ 1 * 1 := mul_le_mul
      (by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
        intro x
        simp)
      (realHilbert_orthogonalProjectionOnto_opNorm_le_one U)
      (norm_nonneg _)
      zero_le_one
    _ = 1 := by ring

/-- On a vector already lying in the centered subspace, the canonical
synthesis is exactly the adjoint of the analysis. -/
@[simp] theorem realHilbertAdjointSynthesis_apply_subtype
    (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (A : F →ₗᵢ[ℝ] U)
    (x : U) :
    realHilbertAdjointSynthesis U A (x : E) =
      A.toContinuousLinearMap† x := by
  simp [realHilbertAdjointSynthesis]

end

end MathlibAnalytic
end MGAP4D