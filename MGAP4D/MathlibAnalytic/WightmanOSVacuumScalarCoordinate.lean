import MGAP4D.MathlibAnalytic.WightmanOSVacuumComplementLine
import Mathlib.Analysis.Normed.Module.Span

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The inverse of the canonical orthogonal decomposition is addition of the two
subspace components, even after the complement summand is transported along an
explicit equality of submodules. -/
theorem real_hilbert_orthogonal_decomposition_of_complement_eq_symm_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K L : Submodule ℝ H) [K.HasOrthogonalProjection]
    (h : Kᗮ = L) (y : WithLp 2 (K × L)) :
    (realHilbertOrthogonalDecompositionLinearIsometryEquivOfComplementEq
      K L h).symm y = (y.fst : H) + (y.snd : H) := by
  cases h
  simpa [realHilbertOrthogonalDecompositionLinearIsometryEquivOfComplementEq,
    realHilbertOrthogonalDecompositionLinearIsometryEquiv] using
    (Submodule.orthogonalDecomposition_symm_apply K y)

/-- The inverse of the line-valued decomposition is the sum of the orthogonal
component and the line component. -/
theorem real_hilbert_orthogonal_complement_line_decomposition_symm_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (y : WithLp 2 (((ℝ ∙ Ω)ᗮ) × (ℝ ∙ Ω))) :
    (realHilbertOrthogonalComplementLineDecompositionLinearIsometryEquiv Ω).symm y =
      (y.fst : H) + (y.snd : H) := by
  exact real_hilbert_orthogonal_decomposition_of_complement_eq_symm_apply
    ((ℝ ∙ Ω)ᗮ) (ℝ ∙ Ω)
    (real_hilbert_span_singleton_orthogonal_orthogonal_eq Ω) y

/-- A unit vector identifies the line that it spans isometrically with the real
scalar field.  The inverse sends `a` to `a • Ω`. -/
def realUnitSpanScalarLinearIsometryEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    (ℝ ∙ Ω) ≃ₗᵢ[ℝ] ℝ :=
  (LinearIsometryEquiv.toSpanUnitSingleton Ω hΩ).symm

/-- The inverse scalar coordinate map is scalar multiplication by the unit vector. -/
@[simp]
theorem real_unit_span_scalar_symm_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) (a : ℝ) :
    ((realUnitSpanScalarLinearIsometryEquiv Ω hΩ).symm a : H) = a • Ω := by
  rfl

/-- Apply an isometric equivalence to the right summand of an `L²` product. -/
def realUnitSpanScalarWithLpProdCongrLinearIsometryEquiv
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    WithLp 2 (K × (ℝ ∙ Ω)) ≃ₗᵢ[ℝ] WithLp 2 (K × ℝ) :=
  LinearIsometryEquiv.withLpProdCongr (p := 2)
    (LinearIsometryEquiv.refl ℝ K)
    (realUnitSpanScalarLinearIsometryEquiv Ω hΩ)

/-- A real Hilbert space decomposes isometrically into the orthogonal complement
of a normalized vector and one real scalar coordinate. -/
def realUnitOrthogonalScalarDecompositionLinearIsometryEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) :
    H ≃ₗᵢ[ℝ] WithLp 2 (((ℝ ∙ Ω)ᗮ) × ℝ) :=
  (realHilbertOrthogonalComplementLineDecompositionLinearIsometryEquiv Ω).trans
    (realUnitSpanScalarWithLpProdCongrLinearIsometryEquiv Ω hΩ)

/-- The inverse scalar decomposition has the expected explicit formula
`(φ, a) ↦ φ + a • Ω`. -/
theorem real_unit_orthogonal_scalar_decomposition_symm_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) (φ : (ℝ ∙ Ω)ᗮ) (a : ℝ) :
    (realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ).symm
        (WithLp.toLp 2 (φ, a)) =
      (φ : H) + a • Ω := by
  change
    (realHilbertOrthogonalComplementLineDecompositionLinearIsometryEquiv Ω).symm
        ((realUnitSpanScalarWithLpProdCongrLinearIsometryEquiv Ω hΩ).symm
          (WithLp.toLp 2 (φ, a))) =
      (φ : H) + a • Ω
  rw [real_hilbert_orthogonal_complement_line_decomposition_symm_apply]
  change
    (φ : H) +
        ((LinearIsometryEquiv.toSpanUnitSingleton Ω hΩ a : ℝ ∙ Ω) : H) =
      (φ : H) + a • Ω
  rw [LinearIsometryEquiv.toSpanUnitSingleton_apply]

/-- Reconstruct a vector from the two coordinates returned by the scalar
orthogonal decomposition. -/
theorem real_unit_orthogonal_scalar_decomposition_reconstruction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) (ψ : H) :
    ψ =
      ((realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ ψ).fst : H) +
        (realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ ψ).snd • Ω := by
  let E := realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ
  let y := E ψ
  calc
    ψ = E.symm (E ψ) := (E.symm_apply_apply ψ).symm
    _ = E.symm (WithLp.toLp 2 (y.fst, y.snd)) := by rfl
    _ = (y.fst : H) + y.snd • Ω :=
      real_unit_orthogonal_scalar_decomposition_symm_apply Ω hΩ y.fst y.snd

/-- The real scalar coordinate is exactly the vacuum coefficient
`inner ℝ Ω ψ`. -/
theorem real_unit_orthogonal_scalar_decomposition_snd
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) (ψ : H) :
    (realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ ψ).snd =
      inner ℝ Ω ψ := by
  let E := realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ
  let y := E ψ
  have hsum : ψ = (y.fst : H) + y.snd • Ω := by
    simpa [E, y] using
      real_unit_orthogonal_scalar_decomposition_reconstruction Ω hΩ ψ
  have horth : inner ℝ Ω (y.fst : H) = 0 :=
    (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℝ) (u := Ω) (v := (y.fst : H))).mp y.fst.property
  have hself : inner ℝ Ω Ω = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    norm_num
  have hinner : inner ℝ Ω ψ = y.snd := by
    calc
      inner ℝ Ω ψ = inner ℝ Ω ((y.fst : H) + y.snd • Ω) := by rw [hsum]
      _ = inner ℝ Ω (y.fst : H) + inner ℝ Ω (y.snd • Ω) := by
        rw [inner_add_right]
      _ = y.snd := by
        rw [horth, zero_add, inner_smul_right, hself, mul_one]
  exact hinner.symm

/-- The orthogonal coordinate is the vector with its vacuum coefficient removed. -/
theorem real_unit_orthogonal_scalar_decomposition_fst
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) (ψ : H) :
    ((realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ ψ).fst : H) =
      ψ - inner ℝ Ω ψ • Ω := by
  have hsum :=
    real_unit_orthogonal_scalar_decomposition_reconstruction Ω hΩ ψ
  have hfirst :
      ((realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ ψ).fst : H) =
        ψ -
          (realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ ψ).snd • Ω :=
    (eq_sub_iff_add_eq).2 hsum.symm
  rw [real_unit_orthogonal_scalar_decomposition_snd Ω hΩ ψ] at hfirst
  exact hfirst

/-- Pythagoras in the explicit vacuum scalar coordinates. -/
theorem real_unit_orthogonal_scalar_decomposition_norm_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ω : H) (hΩ : ‖Ω‖ = 1) (ψ : H) :
    ‖ψ‖ ^ 2 =
      ‖ψ - inner ℝ Ω ψ • Ω‖ ^ 2 + ‖inner ℝ Ω ψ‖ ^ 2 := by
  let E := realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ
  calc
    ‖ψ‖ ^ 2 = ‖E ψ‖ ^ 2 :=
      congrArg (fun r : ℝ => r ^ 2) (LinearIsometryEquiv.norm_map E ψ).symm
    _ = ‖(E ψ).fst‖ ^ 2 + ‖(E ψ).snd‖ ^ 2 :=
      WithLp.prod_norm_sq_eq_of_L2 (E ψ)
    _ = ‖ψ - inner ℝ Ω ψ • Ω‖ ^ 2 + ‖inner ℝ Ω ψ‖ ^ 2 := by
      change
        ‖((E ψ).fst : H)‖ ^ 2 + ‖(E ψ).snd‖ ^ 2 =
          ‖ψ - inner ℝ Ω ψ • Ω‖ ^ 2 + ‖inner ℝ Ω ψ‖ ^ 2
      rw [real_unit_orthogonal_scalar_decomposition_fst Ω hΩ ψ,
        real_unit_orthogonal_scalar_decomposition_snd Ω hΩ ψ]

/-- The reconstructed Wightman OS Hilbert space decomposes isometrically into
the vacuum-orthogonal sector and one real vacuum coordinate. -/
def explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv
    (M : ExplicitWightmanOSReconstructedModel) :
    M.H ≃ₗᵢ[ℝ] WithLp 2 (M.vacuumOrthogonal × ℝ) := by
  simpa [ExplicitWightmanOSReconstructedModel.vacuumOrthogonal,
    ExplicitWightmanOSReconstructedModel.vacuumLine] using
    realUnitOrthogonalScalarDecompositionLinearIsometryEquiv
      M.vacuum M.vacuum_norm

/-- The actual inverse Wightman OS decomposition is `(φ, a) ↦ φ + a • Ω`. -/
theorem explicit_wightman_os_vacuum_scalar_decomposition_symm_apply
    (M : ExplicitWightmanOSReconstructedModel)
    (φ : M.vacuumOrthogonal) (a : ℝ) :
    (explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv M).symm
        (WithLp.toLp 2 (φ, a)) =
      (φ : M.H) + a • M.vacuum := by
  simpa [explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv,
    ExplicitWightmanOSReconstructedModel.vacuumOrthogonal,
    ExplicitWightmanOSReconstructedModel.vacuumLine] using
    real_unit_orthogonal_scalar_decomposition_symm_apply
      M.vacuum M.vacuum_norm φ a

/-- The actual Wightman OS scalar coordinate is the vacuum inner product. -/
theorem explicit_wightman_os_vacuum_scalar_decomposition_snd
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    (explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv M ψ).snd =
      inner ℝ M.vacuum ψ := by
  simpa [explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv,
    ExplicitWightmanOSReconstructedModel.vacuumOrthogonal,
    ExplicitWightmanOSReconstructedModel.vacuumLine] using
    real_unit_orthogonal_scalar_decomposition_snd
      M.vacuum M.vacuum_norm ψ

/-- The actual Wightman OS orthogonal coordinate subtracts the vacuum component. -/
theorem explicit_wightman_os_vacuum_scalar_decomposition_fst
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    ((explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv M ψ).fst : M.H) =
      ψ - inner ℝ M.vacuum ψ • M.vacuum := by
  simpa [explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv,
    ExplicitWightmanOSReconstructedModel.vacuumOrthogonal,
    ExplicitWightmanOSReconstructedModel.vacuumLine] using
    real_unit_orthogonal_scalar_decomposition_fst
      M.vacuum M.vacuum_norm ψ

/-- The exact Pythagorean norm identity for the actual Wightman OS vacuum coordinate. -/
theorem explicit_wightman_os_vacuum_scalar_decomposition_norm_sq
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    ‖ψ‖ ^ 2 =
      ‖ψ - inner ℝ M.vacuum ψ • M.vacuum‖ ^ 2 +
        ‖inner ℝ M.vacuum ψ‖ ^ 2 := by
  exact real_unit_orthogonal_scalar_decomposition_norm_sq
    M.vacuum M.vacuum_norm ψ

/-- Structured receipt for the normalized scalar-coordinate decomposition. -/
structure WightmanOSVacuumScalarCoordinateReceipt : Prop where
  generic_equiv :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (Ω : H) (hΩ : ‖Ω‖ = 1),
      Nonempty (H ≃ₗᵢ[ℝ] WithLp 2 (((ℝ ∙ Ω)ᗮ) × ℝ))
  generic_symm_apply :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (Ω : H) (hΩ : ‖Ω‖ = 1) (φ : (ℝ ∙ Ω)ᗮ) (a : ℝ),
      (realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ).symm
          (WithLp.toLp 2 (φ, a)) = (φ : H) + a • Ω
  generic_snd :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (Ω : H) (hΩ : ‖Ω‖ = 1) (ψ : H),
      (realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ ψ).snd =
        inner ℝ Ω ψ
  generic_fst :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (Ω : H) (hΩ : ‖Ω‖ = 1) (ψ : H),
      ((realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ ψ).fst : H) =
        ψ - inner ℝ Ω ψ • Ω
  actual_equiv :
    ∀ M : ExplicitWightmanOSReconstructedModel,
      Nonempty (M.H ≃ₗᵢ[ℝ] WithLp 2 (M.vacuumOrthogonal × ℝ))
  actual_snd :
    ∀ (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H),
      (explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv M ψ).snd =
        inner ℝ M.vacuum ψ
  actual_fst :
    ∀ (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H),
      ((explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv M ψ).fst : M.H) =
        ψ - inner ℝ M.vacuum ψ • M.vacuum
  actual_norm_sq :
    ∀ (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H),
      ‖ψ‖ ^ 2 =
        ‖ψ - inner ℝ M.vacuum ψ • M.vacuum‖ ^ 2 +
          ‖inner ℝ M.vacuum ψ‖ ^ 2
  claim_boundary : True

/-- The vacuum scalar-coordinate receipt is inhabited. -/
theorem wightmanOSVacuumScalarCoordinateReceipt_proved :
    WightmanOSVacuumScalarCoordinateReceipt := by
  exact
    { generic_equiv := fun Ω hΩ =>
        ⟨realUnitOrthogonalScalarDecompositionLinearIsometryEquiv Ω hΩ⟩
      generic_symm_apply := real_unit_orthogonal_scalar_decomposition_symm_apply
      generic_snd := real_unit_orthogonal_scalar_decomposition_snd
      generic_fst := real_unit_orthogonal_scalar_decomposition_fst
      actual_equiv := fun M =>
        ⟨explicitWightmanOSVacuumScalarDecompositionLinearIsometryEquiv M⟩
      actual_snd := explicit_wightman_os_vacuum_scalar_decomposition_snd
      actual_fst := explicit_wightman_os_vacuum_scalar_decomposition_fst
      actual_norm_sq := explicit_wightman_os_vacuum_scalar_decomposition_norm_sq
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
