import MGAP4D.MathlibAnalytic.RealTensorComplexificationContinuousSymmetricContraction
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace RealTensorComplexification

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The continuous complex contraction wrapper of a symmetric real contraction is
symmetric in Mathlib's bundled `LinearMap.IsSymmetric` sense. -/
theorem isSymmetric_ofContinuousLinearMapContraction
    (T : H →L[ℝ] H)
    (hcontraction : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hsymmetric : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y)) :
    (ofContinuousLinearMapContraction T hcontraction).IsSymmetric := by
  intro x y
  exact inner_ofContinuousLinearMapContraction_left_eq_right
    T hcontraction hsymmetric x y

section Complete

variable [CompleteSpace H]

/-- The Hilbert-space adjoint of the continuous complexification is the operator
itself. -/
theorem adjoint_ofContinuousLinearMapContraction_eq_self
    (T : H →L[ℝ] H)
    (hcontraction : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hsymmetric : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y)) :
    ContinuousLinearMap.adjoint
        (ofContinuousLinearMapContraction T hcontraction) =
      ofContinuousLinearMapContraction T hcontraction :=
  (isSymmetric_ofContinuousLinearMapContraction
    T hcontraction hsymmetric).clm_adjoint_eq

/-- The continuous complexification of a symmetric real contraction is
self-adjoint in Mathlib's standard star-algebra sense. -/
theorem isSelfAdjoint_ofContinuousLinearMapContraction
    (T : H →L[ℝ] H)
    (hcontraction : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hsymmetric : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y)) :
    IsSelfAdjoint (ofContinuousLinearMapContraction T hcontraction) :=
  (isSymmetric_ofContinuousLinearMapContraction
    T hcontraction hsymmetric).isSelfAdjoint

end Complete

end RealTensorComplexification

end

end MathlibAnalytic
end MGAP4D
