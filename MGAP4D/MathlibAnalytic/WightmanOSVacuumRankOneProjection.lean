import MGAP4D.MathlibAnalytic.WightmanOSVacuumScalarCoordinate
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- For a unit vector, Mathlib's orthogonal projection onto its span is the
expected vacuum-component formula. -/
theorem real_unit_span_starProjection_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) (ψ : H) :
    (ℝ ∙ Ω).starProjection ψ = inner ℝ Ω ψ • Ω := by
  exact Submodule.starProjection_unit_singleton ℝ hΩ ψ

/-- The projection onto a normalized line is exactly Mathlib's rank-one
operator `|Ω⟩⟨Ω|`. -/
theorem real_unit_span_starProjection_eq_rankOne
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    (ℝ ∙ Ω).starProjection = InnerProductSpace.rankOne ℝ Ω Ω := by
  ext ψ
  rw [real_unit_span_starProjection_apply Ω hΩ ψ]
  rfl

/-- The orthogonal-complement projection is the complementary operator
`1 - |Ω⟩⟨Ω|`. -/
theorem real_unit_orthogonal_starProjection_eq_one_sub_rankOne
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    ((ℝ ∙ Ω)ᗮ).starProjection =
      (1 : H →L[ℝ] H) - InnerProductSpace.rankOne ℝ Ω Ω := by
  rw [Submodule.starProjection_orthogonal',
    real_unit_span_starProjection_eq_rankOne Ω hΩ]

/-- Pointwise form of the complementary rank-one projection. -/
theorem real_unit_orthogonal_starProjection_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) (ψ : H) :
    ((ℝ ∙ Ω)ᗮ).starProjection ψ =
      ψ - inner ℝ Ω ψ • Ω := by
  rw [Submodule.starProjection_orthogonal_val,
    real_unit_span_starProjection_apply Ω hΩ ψ]

/-- The vacuum-line projection and its orthogonal complement add to the
identity operator. -/
theorem real_unit_span_add_orthogonal_starProjection_eq_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    (ℝ ∙ Ω).starProjection + ((ℝ ∙ Ω)ᗮ).starProjection =
      (1 : H →L[ℝ] H) := by
  rw [real_unit_span_starProjection_eq_rankOne Ω hΩ,
    real_unit_orthogonal_starProjection_eq_one_sub_rankOne Ω hΩ]
  abel

/-- The rank-one vacuum projection has range exactly the line spanned by the
unit vector. -/
theorem real_unit_rankOne_range
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    (InnerProductSpace.rankOne ℝ Ω Ω).range = ℝ ∙ Ω := by
  rw [← real_unit_span_starProjection_eq_rankOne Ω hΩ,
    Submodule.range_starProjection]

/-- The kernel of the rank-one vacuum projection is exactly the orthogonal
complement of the vacuum line. -/
theorem real_unit_rankOne_ker
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    (InnerProductSpace.rankOne ℝ Ω Ω).ker = (ℝ ∙ Ω)ᗮ := by
  rw [← real_unit_span_starProjection_eq_rankOne Ω hΩ,
    Submodule.ker_starProjection]

/-- In the reconstructed Wightman OS Hilbert space, projection onto the
vacuum line is the rank-one vacuum operator. -/
theorem explicit_wightman_os_vacuumLine_starProjection_eq_rankOne
    (M : ExplicitWightmanOSReconstructedModel) :
    M.vacuumLine.starProjection =
      InnerProductSpace.rankOne ℝ M.vacuum M.vacuum := by
  simpa [ExplicitWightmanOSReconstructedModel.vacuumLine] using
    real_unit_span_starProjection_eq_rankOne M.vacuum M.vacuum_norm

/-- Pointwise vacuum-line projection in the reconstructed Wightman OS model. -/
theorem explicit_wightman_os_vacuumLine_starProjection_apply
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    M.vacuumLine.starProjection ψ =
      inner ℝ M.vacuum ψ • M.vacuum := by
  simpa [ExplicitWightmanOSReconstructedModel.vacuumLine] using
    real_unit_span_starProjection_apply M.vacuum M.vacuum_norm ψ

/-- The actual vacuum-orthogonal projector is `1 - |Ω⟩⟨Ω|`. -/
theorem explicit_wightman_os_vacuumOrthogonal_starProjection_eq_one_sub_rankOne
    (M : ExplicitWightmanOSReconstructedModel) :
    M.vacuumOrthogonal.starProjection =
      (1 : M.H →L[ℝ] M.H) -
        InnerProductSpace.rankOne ℝ M.vacuum M.vacuum := by
  simpa [ExplicitWightmanOSReconstructedModel.vacuumOrthogonal,
    ExplicitWightmanOSReconstructedModel.vacuumLine] using
    real_unit_orthogonal_starProjection_eq_one_sub_rankOne
      M.vacuum M.vacuum_norm

/-- Pointwise formula for the actual vacuum-orthogonal projector. -/
theorem explicit_wightman_os_vacuumOrthogonal_starProjection_apply
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    M.vacuumOrthogonal.starProjection ψ =
      ψ - inner ℝ M.vacuum ψ • M.vacuum := by
  simpa [ExplicitWightmanOSReconstructedModel.vacuumOrthogonal,
    ExplicitWightmanOSReconstructedModel.vacuumLine] using
    real_unit_orthogonal_starProjection_apply
      M.vacuum M.vacuum_norm ψ

/-- The first coordinate of the scalar decomposition is precisely the
vacuum-orthogonal projection. -/
theorem explicit_wightman_os_vacuum_scalar_decomposition_fst_eq_starProjection
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    ((explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv M ψ).fst : M.H) =
      M.vacuumOrthogonal.starProjection ψ := by
  rw [explicit_wightman_os_vacuum_scalar_decomposition_fst,
    explicit_wightman_os_vacuumOrthogonal_starProjection_apply]

/-- The scalar coordinate, multiplied back by the vacuum, is precisely the
vacuum-line projection. -/
theorem explicit_wightman_os_vacuum_scalar_decomposition_snd_smul_eq_starProjection
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    (explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv M ψ).snd •
        M.vacuum =
      M.vacuumLine.starProjection ψ := by
  rw [explicit_wightman_os_vacuum_scalar_decomposition_snd,
    explicit_wightman_os_vacuumLine_starProjection_apply]

/-- The two actual vacuum-sector projections add pointwise to the original
vector. -/
theorem explicit_wightman_os_vacuumLine_add_vacuumOrthogonal_starProjection
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    M.vacuumLine.starProjection ψ +
        M.vacuumOrthogonal.starProjection ψ = ψ := by
  rw [explicit_wightman_os_vacuumLine_starProjection_apply,
    explicit_wightman_os_vacuumOrthogonal_starProjection_apply]
  abel

/-- The actual rank-one vacuum operator has the expected range. -/
theorem explicit_wightman_os_vacuum_rankOne_range
    (M : ExplicitWightmanOSReconstructedModel) :
    (InnerProductSpace.rankOne ℝ M.vacuum M.vacuum).range =
      M.vacuumLine := by
  simpa [ExplicitWightmanOSReconstructedModel.vacuumLine] using
    real_unit_rankOne_range M.vacuum M.vacuum_norm

/-- The actual rank-one vacuum operator has kernel equal to the physical
non-vacuum Hilbert sector. -/
theorem explicit_wightman_os_vacuum_rankOne_ker
    (M : ExplicitWightmanOSReconstructedModel) :
    (InnerProductSpace.rankOne ℝ M.vacuum M.vacuum).ker =
      M.vacuumOrthogonal := by
  simpa [ExplicitWightmanOSReconstructedModel.vacuumOrthogonal,
    ExplicitWightmanOSReconstructedModel.vacuumLine] using
    real_unit_rankOne_ker M.vacuum M.vacuum_norm

/-- Structured receipt for the rank-one realization of the vacuum-sector
projections. -/
structure WightmanOSVacuumRankOneProjectionReceipt : Prop where
  generic_vacuum_operator :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      (Ω : H) (hΩ : ‖Ω‖ = 1),
      (ℝ ∙ Ω).starProjection = InnerProductSpace.rankOne ℝ Ω Ω
  generic_orthogonal_operator :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      (Ω : H) (hΩ : ‖Ω‖ = 1),
      ((ℝ ∙ Ω)ᗮ).starProjection =
        (1 : H →L[ℝ] H) - InnerProductSpace.rankOne ℝ Ω Ω
  generic_range :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      (Ω : H) (hΩ : ‖Ω‖ = 1),
      (InnerProductSpace.rankOne ℝ Ω Ω).range = ℝ ∙ Ω
  generic_ker :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      (Ω : H) (hΩ : ‖Ω‖ = 1),
      (InnerProductSpace.rankOne ℝ Ω Ω).ker = (ℝ ∙ Ω)ᗮ
  actual_vacuum_operator :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      M.vacuumLine.starProjection =
        InnerProductSpace.rankOne ℝ M.vacuum M.vacuum
  actual_orthogonal_operator :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      M.vacuumOrthogonal.starProjection =
        (1 : M.H →L[ℝ] M.H) -
          InnerProductSpace.rankOne ℝ M.vacuum M.vacuum
  actual_coordinate_fst :
    ∀ (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H),
      ((explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv M ψ).fst : M.H) =
        M.vacuumOrthogonal.starProjection ψ
  actual_coordinate_snd :
    ∀ (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H),
      (explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv M ψ).snd •
          M.vacuum =
        M.vacuumLine.starProjection ψ
  actual_range :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      (InnerProductSpace.rankOne ℝ M.vacuum M.vacuum).range =
        M.vacuumLine
  actual_ker :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      (InnerProductSpace.rankOne ℝ M.vacuum M.vacuum).ker =
        M.vacuumOrthogonal
  claim_boundary : True

/-- The vacuum rank-one projection receipt is inhabited. -/
theorem wightmanOSVacuumRankOneProjectionReceipt_proved :
    WightmanOSVacuumRankOneProjectionReceipt := by
  exact
    { generic_vacuum_operator := real_unit_span_starProjection_eq_rankOne
      generic_orthogonal_operator :=
        real_unit_orthogonal_starProjection_eq_one_sub_rankOne
      generic_range := real_unit_rankOne_range
      generic_ker := real_unit_rankOne_ker
      actual_vacuum_operator :=
        explicit_wightman_os_vacuumLine_starProjection_eq_rankOne
      actual_orthogonal_operator :=
        explicit_wightman_os_vacuumOrthogonal_starProjection_eq_one_sub_rankOne
      actual_coordinate_fst :=
        explicit_wightman_os_vacuum_scalar_decomposition_fst_eq_starProjection
      actual_coordinate_snd :=
        explicit_wightman_os_vacuum_scalar_decomposition_snd_smul_eq_starProjection
      actual_range := explicit_wightman_os_vacuum_rankOne_range
      actual_ker := explicit_wightman_os_vacuum_rankOne_ker
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
