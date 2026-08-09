import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

noncomputable section

open Function
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/- Generic completion of a second norm-preserving realization from a dense
isometric core.

If the same seminormed real-linear core `E` is represented densely and
isometrically in `H`, and is also represented isometrically in a complete
normed space `K`, the second representation extends uniquely to an isometric
linear map `H → K`.

No Yang--Mills or spectral structure occurs in this layer. -/
namespace DenseIsometricCoreRepresentationCompletion

universe u v w

variable
    {E : Type u} {H : Type v} {K : Type w}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]

/-- Extend the second core representation along the dense first
representation. -/
noncomputable def completedRepresentation
    (e : E →ₗ[ℝ] H)
    (b : E →ₗ[ℝ] K) : H →L[ℝ] K :=
  b.extendOfNorm e

/-- Exact norm preservation on both core realizations supplies the unit norm
bound consumed by `LinearMap.extendOfNorm`. -/
theorem coreRepresentation_norm_le
    (e : E →ₗ[ℝ] H)
    (he : ∀ x : E, ‖e x‖ = ‖x‖)
    (b : E →ₗ[ℝ] K)
    (hb : ∀ x : E, ‖b x‖ = ‖x‖)
    (x : E) :
    ‖b x‖ ≤ 1 * ‖e x‖ := by
  rw [hb x, he x]
  simp

/-- The completed representation agrees exactly with the second realization
on the represented dense core. -/
@[simp] theorem completedRepresentation_on_core
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (he : ∀ x : E, ‖e x‖ = ‖x‖)
    (b : E →ₗ[ℝ] K)
    (hb : ∀ x : E, ‖b x‖ = ‖x‖)
    (x : E) :
    completedRepresentation e b (e x) = b x := by
  exact LinearMap.extendOfNorm_eq
    hDense ⟨1, coreRepresentation_norm_le e he b hb⟩ x

/-- The completed second realization remains exactly isometric on the whole
ambient space.  Density is used only here: equality of norms holds on the
represented core and extends over its closure by continuity. -/
@[simp] theorem completedRepresentation_norm
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (he : ∀ x : E, ‖e x‖ = ‖x‖)
    (b : E →ₗ[ℝ] K)
    (hb : ∀ x : E, ‖b x‖ = ‖x‖)
    (y : H) :
    ‖completedRepresentation e b y‖ = ‖y‖ := by
  refine hDense.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) y
  intro z hz
  rcases hz with ⟨x, rfl⟩
  rw [completedRepresentation_on_core e hDense he b hb x, hb x, he x]

/-- The theorem-generated completion as a real linear isometry. -/
noncomputable def completedLinearIsometry
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (he : ∀ x : E, ‖e x‖ = ‖x‖)
    (b : E →ₗ[ℝ] K)
    (hb : ∀ x : E, ‖b x‖ = ‖x‖) :
    H →ₗᵢ[ℝ] K where
  toLinearMap := (completedRepresentation e b).toLinearMap
  norm_map' := completedRepresentation_norm e hDense he b hb

/-- The linear-isometry wrapper still agrees with the original second core
representation. -/
@[simp] theorem completedLinearIsometry_on_core
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (he : ∀ x : E, ‖e x‖ = ‖x‖)
    (b : E →ₗ[ℝ] K)
    (hb : ∀ x : E, ‖b x‖ = ‖x‖)
    (x : E) :
    completedLinearIsometry e hDense he b hb (e x) = b x := by
  exact completedRepresentation_on_core e hDense he b hb x

/-- In real inner-product spaces the completed representation also preserves
inner products, generated from norm preservation by polarization. -/
@[simp] theorem completedLinearIsometry_inner
    [InnerProductSpace ℝ H]
    [InnerProductSpace ℝ K]
    (e : E →ₗ[ℝ] H)
    (hDense : DenseRange e)
    (he : ∀ x : E, ‖e x‖ = ‖x‖)
    (b : E →ₗ[ℝ] K)
    (hb : ∀ x : E, ‖b x‖ = ‖x‖)
    (x y : H) :
    inner ℝ
        (completedLinearIsometry e hDense he b hb x)
        (completedLinearIsometry e hDense he b hb y) =
      inner ℝ x y := by
  exact LinearIsometry.inner_map_map
    (completedLinearIsometry e hDense he b hb) x y

end DenseIsometricCoreRepresentationCompletion

end MathlibAnalytic
end MGAP4D

end
