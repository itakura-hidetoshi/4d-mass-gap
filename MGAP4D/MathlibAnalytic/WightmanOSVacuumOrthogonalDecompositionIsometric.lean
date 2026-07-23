import MGAP4D.MathlibAnalytic.WightmanOSPVMVacuumOrthogonality
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The canonical orthogonal-complement decomposition of a real Hilbert space is
an isometric linear equivalence when the product is equipped with its `L²` norm. -/
def realHilbertOrthogonalDecompositionLinearIsometryEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Submodule ℝ H) [K.HasOrthogonalProjection] :
    H ≃ₗᵢ[ℝ] WithLp 2 (K × Kᗮ) :=
  K.orthogonalDecomposition

/-- The existing decomposition equivalence preserves the Hilbert norm exactly. -/
theorem real_hilbert_orthogonal_decomposition_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Submodule ℝ H) [K.HasOrthogonalProjection] (x : H) :
    ‖realHilbertOrthogonalDecompositionLinearIsometryEquiv K x‖ = ‖x‖ := by
  exact LinearIsometryEquiv.norm_map
    (realHilbertOrthogonalDecompositionLinearIsometryEquiv K) x

/-- The inverse of the decomposition equivalence also preserves the `L²` product norm. -/
theorem real_hilbert_orthogonal_decomposition_symm_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (y : WithLp 2 (K × Kᗮ)) :
    ‖(realHilbertOrthogonalDecompositionLinearIsometryEquiv K).symm y‖ = ‖y‖ := by
  exact LinearIsometryEquiv.norm_map
    (realHilbertOrthogonalDecompositionLinearIsometryEquiv K).symm y

/-- The underlying linear equivalence of the isometric decomposition is the
underlying linear equivalence of Mathlib's canonical orthogonal decomposition. -/
theorem real_hilbert_orthogonal_decomposition_toLinearEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Submodule ℝ H) [K.HasOrthogonalProjection] :
    (realHilbertOrthogonalDecompositionLinearIsometryEquiv K).toLinearEquiv =
      K.orthogonalDecomposition.toLinearEquiv := by
  rfl

/-- The explicit Wightman OS Hilbert space decomposes isometrically into the
vacuum-orthogonal sector and its orthogonal complement. -/
def explicitWightmanOSVacuumOrthogonalDecompositionLinearIsometryEquiv
    (M : ExplicitWightmanOSReconstructedModel) :
    M.H ≃ₗᵢ[ℝ] WithLp 2 (M.vacuumOrthogonal × M.vacuumOrthogonalᗮ) :=
  realHilbertOrthogonalDecompositionLinearIsometryEquiv M.vacuumOrthogonal

/-- The actual Wightman OS vacuum-orthogonal decomposition preserves norm exactly. -/
theorem explicit_wightman_os_vacuum_orthogonal_decomposition_norm
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    ‖explicitWightmanOSVacuumOrthogonalDecompositionLinearIsometryEquiv M ψ‖ = ‖ψ‖ := by
  exact real_hilbert_orthogonal_decomposition_norm M.vacuumOrthogonal ψ

/-- The inverse actual decomposition preserves the `L²` product norm exactly. -/
theorem explicit_wightman_os_vacuum_orthogonal_decomposition_symm_norm
    (M : ExplicitWightmanOSReconstructedModel)
    (y : WithLp 2 (M.vacuumOrthogonal × M.vacuumOrthogonalᗮ)) :
    ‖(explicitWightmanOSVacuumOrthogonalDecompositionLinearIsometryEquiv M).symm y‖ = ‖y‖ := by
  exact real_hilbert_orthogonal_decomposition_symm_norm M.vacuumOrthogonal y

/-- Structured receipt that the generic and actual decomposition equivalences are
isometric in both directions. -/
structure WightmanOSVacuumOrthogonalDecompositionIsometricReceipt : Prop where
  generic_norm :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      (K : Submodule ℝ H) [K.HasOrthogonalProjection] (x : H),
      ‖realHilbertOrthogonalDecompositionLinearIsometryEquiv K x‖ = ‖x‖
  generic_symm_norm :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      (K : Submodule ℝ H) [K.HasOrthogonalProjection]
      (y : WithLp 2 (K × Kᗮ)),
      ‖(realHilbertOrthogonalDecompositionLinearIsometryEquiv K).symm y‖ = ‖y‖
  actual_norm :
    ∀ (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H),
      ‖explicitWightmanOSVacuumOrthogonalDecompositionLinearIsometryEquiv M ψ‖ = ‖ψ‖
  actual_symm_norm :
    ∀ (M : ExplicitWightmanOSReconstructedModel)
      (y : WithLp 2 (M.vacuumOrthogonal × M.vacuumOrthogonalᗮ)),
      ‖(explicitWightmanOSVacuumOrthogonalDecompositionLinearIsometryEquiv M).symm y‖ = ‖y‖
  claim_boundary : True

/-- The isometric decomposition receipt is inhabited. -/
theorem wightmanOSVacuumOrthogonalDecompositionIsometricReceipt_proved :
    WightmanOSVacuumOrthogonalDecompositionIsometricReceipt := by
  exact
    { generic_norm := real_hilbert_orthogonal_decomposition_norm
      generic_symm_norm := real_hilbert_orthogonal_decomposition_symm_norm
      actual_norm := explicit_wightman_os_vacuum_orthogonal_decomposition_norm
      actual_symm_norm := explicit_wightman_os_vacuum_orthogonal_decomposition_symm_norm
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
