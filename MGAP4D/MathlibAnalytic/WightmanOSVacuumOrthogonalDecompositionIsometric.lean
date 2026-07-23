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

/-- The underlying linear equivalence is exactly the standard complementary-subspace
product decomposition followed by the `L²` product transport. -/
theorem real_hilbert_orthogonal_decomposition_toLinearEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Submodule ℝ H) [K.HasOrthogonalProjection] :
    (realHilbertOrthogonalDecompositionLinearIsometryEquiv K).toLinearEquiv =
      (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal).symm ≪≫ₗ
        (WithLp.linearEquiv 2 ℝ (K × Kᗮ)).symm := by
  rfl

/-- The decomposition equivalence preserves the Hilbert norm exactly. -/
theorem real_hilbert_orthogonal_decomposition_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Submodule ℝ H) [K.HasOrthogonalProjection] (x : H) :
    ‖realHilbertOrthogonalDecompositionLinearIsometryEquiv K x‖ = ‖x‖ := by
  exact LinearIsometryEquiv.norm_map
    (realHilbertOrthogonalDecompositionLinearIsometryEquiv K) x

/-- The first component is the orthogonal projection onto the selected subspace. -/
theorem real_hilbert_orthogonal_decomposition_fst
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Submodule ℝ H) [K.HasOrthogonalProjection] (x : H) :
    (realHilbertOrthogonalDecompositionLinearIsometryEquiv K x).fst =
      K.orthogonalProjectionOnto x := by
  exact K.fst_orthogonalDecomposition_apply x

/-- The second component is the orthogonal projection onto the orthogonal complement. -/
theorem real_hilbert_orthogonal_decomposition_snd
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Submodule ℝ H) [K.HasOrthogonalProjection] (x : H) :
    (realHilbertOrthogonalDecompositionLinearIsometryEquiv K x).snd =
      Kᗮ.orthogonalProjectionOnto x := by
  exact K.snd_orthogonalDecomposition_apply x

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

/-- The actual decomposition's first coordinate is the vacuum-orthogonal projection. -/
theorem explicit_wightman_os_vacuum_orthogonal_decomposition_fst
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    (explicitWightmanOSVacuumOrthogonalDecompositionLinearIsometryEquiv M ψ).fst =
      M.vacuumOrthogonal.orthogonalProjectionOnto ψ := by
  exact real_hilbert_orthogonal_decomposition_fst M.vacuumOrthogonal ψ

/-- The actual decomposition's second coordinate is the complementary projection. -/
theorem explicit_wightman_os_vacuum_orthogonal_decomposition_snd
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    (explicitWightmanOSVacuumOrthogonalDecompositionLinearIsometryEquiv M ψ).snd =
      M.vacuumOrthogonalᗮ.orthogonalProjectionOnto ψ := by
  exact real_hilbert_orthogonal_decomposition_snd M.vacuumOrthogonal ψ

/-- Structured receipt that the generic and actual decomposition equivalences are
isometric, with their projection coordinates exposed. -/
structure WightmanOSVacuumOrthogonalDecompositionIsometricReceipt : Prop where
  generic_norm :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      (K : Submodule ℝ H) [K.HasOrthogonalProjection] (x : H),
      ‖realHilbertOrthogonalDecompositionLinearIsometryEquiv K x‖ = ‖x‖
  actual_norm :
    ∀ (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H),
      ‖explicitWightmanOSVacuumOrthogonalDecompositionLinearIsometryEquiv M ψ‖ = ‖ψ‖
  claim_boundary : True

/-- The isometric decomposition receipt is inhabited. -/
theorem wightmanOSVacuumOrthogonalDecompositionIsometricReceipt_proved :
    WightmanOSVacuumOrthogonalDecompositionIsometricReceipt := by
  exact
    { generic_norm := real_hilbert_orthogonal_decomposition_norm
      actual_norm := explicit_wightman_os_vacuum_orthogonal_decomposition_norm
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
