import MGAP4D.MathlibAnalytic.WightmanOSVacuumRankOneProjection
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- A normalized rank-one operator is a Mathlib star projection: it is both
self-adjoint and idempotent. -/
theorem real_unit_rankOne_isStarProjection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    IsStarProjection (InnerProductSpace.rankOne ℝ Ω Ω) :=
  InnerProductSpace.isStarProjection_rankOne_self hΩ

/-- The adjoint of the normalized rank-one operator is itself. -/
theorem real_unit_rankOne_adjoint_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    ContinuousLinearMap.adjoint (InnerProductSpace.rankOne ℝ Ω Ω) =
      InnerProductSpace.rankOne ℝ Ω Ω :=
  (real_unit_rankOne_isStarProjection Ω hΩ).isSelfAdjoint.adjoint_eq

/-- The normalized rank-one operator is idempotent. -/
theorem real_unit_rankOne_mul_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    InnerProductSpace.rankOne ℝ Ω Ω *
        InnerProductSpace.rankOne ℝ Ω Ω =
      InnerProductSpace.rankOne ℝ Ω Ω :=
  (real_unit_rankOne_isStarProjection Ω hΩ).isIdempotentElem

/-- The complementary operator `1 - |Ω⟩⟨Ω|` is also a star projection. -/
theorem real_unit_one_sub_rankOne_isStarProjection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    IsStarProjection
      ((1 : H →L[ℝ] H) - InnerProductSpace.rankOne ℝ Ω Ω) :=
  (real_unit_rankOne_isStarProjection Ω hΩ).one_sub

/-- A normalized rank-one projection annihilates its complementary projection
on the right. -/
theorem real_unit_rankOne_mul_one_sub_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    InnerProductSpace.rankOne ℝ Ω Ω *
        ((1 : H →L[ℝ] H) - InnerProductSpace.rankOne ℝ Ω Ω) = 0 :=
  (real_unit_rankOne_isStarProjection Ω hΩ).mul_one_sub_self

/-- A normalized rank-one projection annihilates its complementary projection
on the left. -/
theorem real_unit_one_sub_mul_rankOne_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    ((1 : H →L[ℝ] H) - InnerProductSpace.rankOne ℝ Ω Ω) *
        InnerProductSpace.rankOne ℝ Ω Ω = 0 :=
  (real_unit_rankOne_isStarProjection Ω hΩ).one_sub_mul_self

/-- The line projection followed by the orthogonal-complement projection is
zero. -/
theorem real_unit_span_mul_orthogonal_starProjection_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    (ℝ ∙ Ω).starProjection * ((ℝ ∙ Ω)ᗮ).starProjection = 0 := by
  rw [real_unit_span_starProjection_eq_rankOne Ω hΩ,
    real_unit_orthogonal_starProjection_eq_one_sub_rankOne Ω hΩ]
  exact real_unit_rankOne_mul_one_sub_eq_zero Ω hΩ

/-- The orthogonal-complement projection followed by the line projection is
zero. -/
theorem real_unit_orthogonal_mul_span_starProjection_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    ((ℝ ∙ Ω)ᗮ).starProjection * (ℝ ∙ Ω).starProjection = 0 := by
  rw [real_unit_span_starProjection_eq_rankOne Ω hΩ,
    real_unit_orthogonal_starProjection_eq_one_sub_rankOne Ω hΩ]
  exact real_unit_one_sub_mul_rankOne_eq_zero Ω hΩ

/-- Re-export the reconstructed physical Hilbert-space completeness field as
a typeclass instance, allowing Mathlib's adjoint and star-projection APIs to be
used directly on model-level operators. -/
instance explicitWightmanOSReconstructedHilbertCompleteSpace
    (M : ExplicitWightmanOSReconstructedModel) : CompleteSpace M.H :=
  M.hilbertCompleteSpace

/-- The actual vacuum rank-one operator is a star projection. -/
theorem explicit_wightman_os_vacuum_rankOne_isStarProjection
    (M : ExplicitWightmanOSReconstructedModel) :
    IsStarProjection
      (InnerProductSpace.rankOne ℝ M.vacuum M.vacuum) :=
  real_unit_rankOne_isStarProjection M.vacuum M.vacuum_norm

/-- The actual vacuum rank-one operator is self-adjoint. -/
theorem explicit_wightman_os_vacuum_rankOne_adjoint_eq
    (M : ExplicitWightmanOSReconstructedModel) :
    ContinuousLinearMap.adjoint
        (InnerProductSpace.rankOne ℝ M.vacuum M.vacuum) =
      InnerProductSpace.rankOne ℝ M.vacuum M.vacuum :=
  real_unit_rankOne_adjoint_eq M.vacuum M.vacuum_norm

/-- The actual vacuum rank-one operator is idempotent. -/
theorem explicit_wightman_os_vacuum_rankOne_mul_self
    (M : ExplicitWightmanOSReconstructedModel) :
    InnerProductSpace.rankOne ℝ M.vacuum M.vacuum *
        InnerProductSpace.rankOne ℝ M.vacuum M.vacuum =
      InnerProductSpace.rankOne ℝ M.vacuum M.vacuum :=
  real_unit_rankOne_mul_self M.vacuum M.vacuum_norm

/-- The model-level projection onto the vacuum line is a star projection. -/
theorem explicit_wightman_os_vacuumLine_starProjection_isStarProjection
    (M : ExplicitWightmanOSReconstructedModel) :
    IsStarProjection M.vacuumLine.starProjection := by
  exact isStarProjection_starProjection

/-- The model-level projection onto the vacuum-orthogonal sector is a star
projection. -/
theorem explicit_wightman_os_vacuumOrthogonal_starProjection_isStarProjection
    (M : ExplicitWightmanOSReconstructedModel) :
    IsStarProjection M.vacuumOrthogonal.starProjection := by
  exact isStarProjection_starProjection

/-- The vacuum-line projector is self-adjoint. -/
theorem explicit_wightman_os_vacuumLine_starProjection_adjoint_eq
    (M : ExplicitWightmanOSReconstructedModel) :
    ContinuousLinearMap.adjoint M.vacuumLine.starProjection =
      M.vacuumLine.starProjection :=
  (explicit_wightman_os_vacuumLine_starProjection_isStarProjection M).isSelfAdjoint.adjoint_eq

/-- The vacuum-orthogonal projector is self-adjoint. -/
theorem explicit_wightman_os_vacuumOrthogonal_starProjection_adjoint_eq
    (M : ExplicitWightmanOSReconstructedModel) :
    ContinuousLinearMap.adjoint M.vacuumOrthogonal.starProjection =
      M.vacuumOrthogonal.starProjection :=
  (explicit_wightman_os_vacuumOrthogonal_starProjection_isStarProjection M).isSelfAdjoint.adjoint_eq

/-- The vacuum-line projector is idempotent. -/
theorem explicit_wightman_os_vacuumLine_starProjection_mul_self
    (M : ExplicitWightmanOSReconstructedModel) :
    M.vacuumLine.starProjection * M.vacuumLine.starProjection =
      M.vacuumLine.starProjection :=
  (explicit_wightman_os_vacuumLine_starProjection_isStarProjection M).isIdempotentElem

/-- The vacuum-orthogonal projector is idempotent. -/
theorem explicit_wightman_os_vacuumOrthogonal_starProjection_mul_self
    (M : ExplicitWightmanOSReconstructedModel) :
    M.vacuumOrthogonal.starProjection *
        M.vacuumOrthogonal.starProjection =
      M.vacuumOrthogonal.starProjection :=
  (explicit_wightman_os_vacuumOrthogonal_starProjection_isStarProjection M).isIdempotentElem

/-- The actual vacuum-line projection annihilates the vacuum-orthogonal
projection on the right. -/
theorem explicit_wightman_os_vacuumLine_mul_vacuumOrthogonal_starProjection_eq_zero
    (M : ExplicitWightmanOSReconstructedModel) :
    M.vacuumLine.starProjection *
        M.vacuumOrthogonal.starProjection = 0 := by
  rw [explicit_wightman_os_vacuumLine_starProjection_eq_rankOne M,
    explicit_wightman_os_vacuumOrthogonal_starProjection_eq_one_sub_rankOne M]
  exact real_unit_rankOne_mul_one_sub_eq_zero M.vacuum M.vacuum_norm

/-- The actual vacuum-orthogonal projection annihilates the vacuum-line
projection on the right. -/
theorem explicit_wightman_os_vacuumOrthogonal_mul_vacuumLine_starProjection_eq_zero
    (M : ExplicitWightmanOSReconstructedModel) :
    M.vacuumOrthogonal.starProjection *
        M.vacuumLine.starProjection = 0 := by
  rw [explicit_wightman_os_vacuumLine_starProjection_eq_rankOne M,
    explicit_wightman_os_vacuumOrthogonal_starProjection_eq_one_sub_rankOne M]
  exact real_unit_one_sub_mul_rankOne_eq_zero M.vacuum M.vacuum_norm

/-- Structured receipt for the complementary star-projection realization of
the reconstructed vacuum sectors. -/
structure WightmanOSVacuumStarProjectionStructureReceipt : Prop where
  generic_rankOne_starProjection :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (Ω : H) (hΩ : ‖Ω‖ = 1),
      IsStarProjection (InnerProductSpace.rankOne ℝ Ω Ω)
  generic_rankOne_adjoint :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (Ω : H) (hΩ : ‖Ω‖ = 1),
      ContinuousLinearMap.adjoint (InnerProductSpace.rankOne ℝ Ω Ω) =
        InnerProductSpace.rankOne ℝ Ω Ω
  generic_rankOne_idempotent :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (Ω : H) (hΩ : ‖Ω‖ = 1),
      InnerProductSpace.rankOne ℝ Ω Ω *
          InnerProductSpace.rankOne ℝ Ω Ω =
        InnerProductSpace.rankOne ℝ Ω Ω
  generic_left_zero :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (Ω : H) (hΩ : ‖Ω‖ = 1),
      (ℝ ∙ Ω).starProjection * ((ℝ ∙ Ω)ᗮ).starProjection = 0
  generic_right_zero :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (Ω : H) (hΩ : ‖Ω‖ = 1),
      ((ℝ ∙ Ω)ᗮ).starProjection * (ℝ ∙ Ω).starProjection = 0
  actual_rankOne_starProjection :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      IsStarProjection (InnerProductSpace.rankOne ℝ M.vacuum M.vacuum)
  actual_line_starProjection :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      IsStarProjection M.vacuumLine.starProjection
  actual_orthogonal_starProjection :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      IsStarProjection M.vacuumOrthogonal.starProjection
  actual_line_orthogonal_zero :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      M.vacuumLine.starProjection * M.vacuumOrthogonal.starProjection = 0
  actual_orthogonal_line_zero :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      M.vacuumOrthogonal.starProjection * M.vacuumLine.starProjection = 0
  claim_boundary : True

/-- The vacuum complementary-star-projection receipt is inhabited. -/
theorem wightmanOSVacuumStarProjectionStructureReceipt_proved :
    WightmanOSVacuumStarProjectionStructureReceipt := by
  exact
    { generic_rankOne_starProjection := real_unit_rankOne_isStarProjection
      generic_rankOne_adjoint := real_unit_rankOne_adjoint_eq
      generic_rankOne_idempotent := real_unit_rankOne_mul_self
      generic_left_zero := real_unit_span_mul_orthogonal_starProjection_eq_zero
      generic_right_zero := real_unit_orthogonal_mul_span_starProjection_eq_zero
      actual_rankOne_starProjection :=
        explicit_wightman_os_vacuum_rankOne_isStarProjection
      actual_line_starProjection :=
        explicit_wightman_os_vacuumLine_starProjection_isStarProjection
      actual_orthogonal_starProjection :=
        explicit_wightman_os_vacuumOrthogonal_starProjection_isStarProjection
      actual_line_orthogonal_zero :=
        explicit_wightman_os_vacuumLine_mul_vacuumOrthogonal_starProjection_eq_zero
      actual_orthogonal_line_zero :=
        explicit_wightman_os_vacuumOrthogonal_mul_vacuumLine_starProjection_eq_zero
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
