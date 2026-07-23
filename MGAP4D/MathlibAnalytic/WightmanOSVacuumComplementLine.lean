import MGAP4D.MathlibAnalytic.WightmanOSVacuumOrthogonalDecompositionIsometric
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- In a real Hilbert space, the double orthogonal complement of the line spanned
by a vector is exactly that line.  The proof uses the general closure theorem and
the fact that a singleton span is finite-dimensional, rather than assuming a
new projection-coordinate API. -/
theorem real_hilbert_span_singleton_orthogonal_orthogonal_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) :
    (ℝ ∙ Ω)ᗮᗮ = ℝ ∙ Ω := by
  calc
    (ℝ ∙ Ω)ᗮᗮ = (ℝ ∙ Ω).topologicalClosure :=
      (ℝ ∙ Ω).orthogonal_orthogonal_eq_closure
    _ = ℝ ∙ Ω := (ℝ ∙ Ω).topologicalClosure_eq_self

/-- Replace only the orthogonal-complement summand of the canonical decomposition
along an equality of submodules.  Pattern matching on the equality performs the
required dependent transport of subtype carriers. -/
def realHilbertOrthogonalDecompositionLinearIsometryEquivOfComplementEq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K L : Submodule ℝ H) [K.HasOrthogonalProjection]
    (h : Kᗮ = L) :
    H ≃ₗᵢ[ℝ] WithLp 2 (K × L) := by
  cases h
  exact realHilbertOrthogonalDecompositionLinearIsometryEquiv K

/-- The canonical orthogonal decomposition can therefore be presented with its
second summand as the actual line spanned by the chosen vector. -/
def realHilbertOrthogonalComplementLineDecompositionLinearIsometryEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) :
    H ≃ₗᵢ[ℝ] WithLp 2 (((ℝ ∙ Ω)ᗮ) × (ℝ ∙ Ω)) :=
  realHilbertOrthogonalDecompositionLinearIsometryEquivOfComplementEq
    ((ℝ ∙ Ω)ᗮ) (ℝ ∙ Ω)
    (real_hilbert_span_singleton_orthogonal_orthogonal_eq Ω)

/-- The line-valued orthogonal decomposition preserves the Hilbert norm exactly. -/
theorem real_hilbert_orthogonal_complement_line_decomposition_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω x : H) :
    ‖realHilbertOrthogonalComplementLineDecompositionLinearIsometryEquiv Ω x‖ = ‖x‖ := by
  exact LinearIsometryEquiv.norm_map
    (realHilbertOrthogonalComplementLineDecompositionLinearIsometryEquiv Ω) x

/-- The inverse line-valued decomposition also preserves the `L²` product norm. -/
theorem real_hilbert_orthogonal_complement_line_decomposition_symm_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (y : WithLp 2 (((ℝ ∙ Ω)ᗮ) × (ℝ ∙ Ω))) :
    ‖(realHilbertOrthogonalComplementLineDecompositionLinearIsometryEquiv Ω).symm y‖ = ‖y‖ := by
  exact LinearIsometryEquiv.norm_map
    (realHilbertOrthogonalComplementLineDecompositionLinearIsometryEquiv Ω).symm y

/-- For the reconstructed Wightman OS model, the orthogonal complement of the
vacuum-orthogonal sector is exactly the vacuum line. -/
theorem explicit_wightman_os_vacuumOrthogonal_orthogonal_eq_vacuumLine
    (M : ExplicitWightmanOSReconstructedModel) :
    M.vacuumOrthogonalᗮ = M.vacuumLine := by
  change (ℝ ∙ M.vacuum)ᗮᗮ = ℝ ∙ M.vacuum
  exact real_hilbert_span_singleton_orthogonal_orthogonal_eq M.vacuum

/-- Equivalent span notation for the exact identification of the vacuum
complement. -/
theorem explicit_wightman_os_vacuumOrthogonal_orthogonal_eq_span_vacuum
    (M : ExplicitWightmanOSReconstructedModel) :
    M.vacuumOrthogonalᗮ = ℝ ∙ M.vacuum := by
  simpa [ExplicitWightmanOSReconstructedModel.vacuumLine] using
    explicit_wightman_os_vacuumOrthogonal_orthogonal_eq_vacuumLine M

/-- The actual reconstructed Hilbert space decomposes isometrically into the
vacuum-orthogonal sector and the vacuum line itself. -/
def explicitWightmanOSVacuumOrthogonalVacuumLineDecompositionLinearIsometryEquiv
    (M : ExplicitWightmanOSReconstructedModel) :
    M.H ≃ₗᵢ[ℝ] WithLp 2 (M.vacuumOrthogonal × M.vacuumLine) :=
  realHilbertOrthogonalDecompositionLinearIsometryEquivOfComplementEq
    M.vacuumOrthogonal M.vacuumLine
    (explicit_wightman_os_vacuumOrthogonal_orthogonal_eq_vacuumLine M)

/-- The actual vacuum-line decomposition preserves norm exactly. -/
theorem explicit_wightman_os_vacuum_orthogonal_vacuum_line_decomposition_norm
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    ‖explicitWightmanOSVacuumOrthogonalVacuumLineDecompositionLinearIsometryEquiv M ψ‖ = ‖ψ‖ := by
  exact LinearIsometryEquiv.norm_map
    (explicitWightmanOSVacuumOrthogonalVacuumLineDecompositionLinearIsometryEquiv M) ψ

/-- The inverse actual vacuum-line decomposition preserves the `L²` product norm. -/
theorem explicit_wightman_os_vacuum_orthogonal_vacuum_line_decomposition_symm_norm
    (M : ExplicitWightmanOSReconstructedModel)
    (y : WithLp 2 (M.vacuumOrthogonal × M.vacuumLine)) :
    ‖(explicitWightmanOSVacuumOrthogonalVacuumLineDecompositionLinearIsometryEquiv M).symm y‖ = ‖y‖ := by
  exact LinearIsometryEquiv.norm_map
    (explicitWightmanOSVacuumOrthogonalVacuumLineDecompositionLinearIsometryEquiv M).symm y

/-- Structured receipt for the generic line theorem and its actual Wightman OS
specialization. -/
structure WightmanOSVacuumComplementLineReceipt : Prop where
  generic_complement :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (Ω : H), (ℝ ∙ Ω)ᗮᗮ = ℝ ∙ Ω
  actual_complement :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      M.vacuumOrthogonalᗮ = M.vacuumLine
  generic_norm :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (Ω x : H),
      ‖realHilbertOrthogonalComplementLineDecompositionLinearIsometryEquiv Ω x‖ = ‖x‖
  generic_symm_norm :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (Ω : H) (y : WithLp 2 (((ℝ ∙ Ω)ᗮ) × (ℝ ∙ Ω))),
      ‖(realHilbertOrthogonalComplementLineDecompositionLinearIsometryEquiv Ω).symm y‖ = ‖y‖
  actual_norm :
    ∀ (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H),
      ‖explicitWightmanOSVacuumOrthogonalVacuumLineDecompositionLinearIsometryEquiv M ψ‖ = ‖ψ‖
  actual_symm_norm :
    ∀ (M : ExplicitWightmanOSReconstructedModel)
      (y : WithLp 2 (M.vacuumOrthogonal × M.vacuumLine)),
      ‖(explicitWightmanOSVacuumOrthogonalVacuumLineDecompositionLinearIsometryEquiv M).symm y‖ = ‖y‖
  claim_boundary : True

/-- The vacuum-complement-line receipt is inhabited. -/
theorem wightmanOSVacuumComplementLineReceipt_proved :
    WightmanOSVacuumComplementLineReceipt := by
  exact
    { generic_complement := real_hilbert_span_singleton_orthogonal_orthogonal_eq
      actual_complement := explicit_wightman_os_vacuumOrthogonal_orthogonal_eq_vacuumLine
      generic_norm := real_hilbert_orthogonal_complement_line_decomposition_norm
      generic_symm_norm := real_hilbert_orthogonal_complement_line_decomposition_symm_norm
      actual_norm := explicit_wightman_os_vacuum_orthogonal_vacuum_line_decomposition_norm
      actual_symm_norm :=
        explicit_wightman_os_vacuum_orthogonal_vacuum_line_decomposition_symm_norm
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
