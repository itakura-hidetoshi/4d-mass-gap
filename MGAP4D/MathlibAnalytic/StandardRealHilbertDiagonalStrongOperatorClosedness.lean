import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalStarSubalgebraCompleteClosed
import MGAP4D.MathlibAnalytic.RealHilbertBoundedOperatorComplexificationConjugationCommutantFromRealFormDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Topology

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The canonical embedding of the real Hilbert space into its standard
complexification, bundled as a real-linear isometry. -/
noncomputable def standardOfRealLinearIsometry :
    H →ₗᵢ[ℝ] StandardRealHilbertComplexification H where
  toLinearMap :=
    { toFun := ofReal
      map_add' := by
        intro x y
        apply Prod.ext <;> simp [ofReal]
      map_smul' := by
        intro r x
        apply Prod.ext <;> simp [ofReal] }
  norm_map' := norm_ofReal

@[simp]
theorem standardOfRealLinearIsometry_apply (x : H) :
    standardOfRealLinearIsometry (H := H) x = ofReal x :=
  rfl

/-- Standard conjugation, bundled as a real-linear isometry. -/
noncomputable def standardConjugationLinearIsometry :
    StandardRealHilbertComplexification H →ₗᵢ[ℝ]
      StandardRealHilbertComplexification H where
  toLinearMap :=
    { toFun := conjugation
      map_add' := by
        intro z w
        apply Prod.ext <;> simp [conjugation]
      map_smul' := by
        intro r z
        apply Prod.ext <;> simp [conjugation] }
  norm_map' := norm_conjugation

@[simp]
theorem standardConjugationLinearIsometry_apply
    (z : StandardRealHilbertComplexification H) :
    standardConjugationLinearIsometry (H := H) z = conjugation z :=
  rfl

/-- Standard conjugation is continuous. -/
theorem continuous_standardConjugation :
    Continuous (conjugation : StandardRealHilbertComplexification H →
      StandardRealHilbertComplexification H) :=
  (standardConjugationLinearIsometry (H := H)).continuous

/-- The real-coordinate projection as a real-linear map. -/
def standardRealPartLinearMap :
    StandardRealHilbertComplexification H →ₗ[ℝ] H where
  toFun z := z.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem standardRealPartLinearMap_apply
    (z : StandardRealHilbertComplexification H) :
    standardRealPartLinearMap (H := H) z = z.1 :=
  rfl

/-- The real-coordinate norm is bounded by the standard complexification norm. -/
theorem norm_standardRealPart_le
    (z : StandardRealHilbertComplexification H) :
    ‖z.1‖ ≤ ‖z‖ := by
  have hsq : ‖z.1‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [norm_eq_standardNorm, standardNorm_sq]
    nlinarith [sq_nonneg ‖z.2‖]
  exact (sq_le_sq₀ (norm_nonneg z.1) (norm_nonneg z)).mp hsq

/-- The real-coordinate projection as a bounded real-linear map. -/
noncomputable def standardRealPartContinuousLinearMap :
    StandardRealHilbertComplexification H →L[ℝ] H :=
  (standardRealPartLinearMap (H := H)).mkContinuous 1 fun z => by
    simpa using norm_standardRealPart_le (H := H) z

@[simp]
theorem standardRealPartContinuousLinearMap_apply
    (z : StandardRealHilbertComplexification H) :
    standardRealPartContinuousLinearMap (H := H) z = z.1 :=
  rfl

/-- A vector fixed by standard conjugation has zero imaginary coordinate. -/
theorem imag_eq_zero_of_conjugation_eq
    (z : StandardRealHilbertComplexification H)
    (hz : conjugation z = z) :
    z.2 = 0 := by
  have hcoord := congrArg Prod.snd hz
  change -z.2 = z.2 at hcoord
  have hsum : z.2 + z.2 = 0 := by
    calc
      z.2 + z.2 = z.2 + (-z.2) :=
        congrArg (fun w : H => z.2 + w) hcoord.symm
      _ = 0 := add_neg_cancel _
  have htwo : (2 : ℝ) • z.2 = 0 := by
    simpa [two_smul] using hsum
  have h := congrArg (fun w : H => (2 : ℝ)⁻¹ • w) htwo
  simpa [smul_smul] using h

/-- A vector fixed by standard conjugation is exactly its embedded real part. -/
theorem ofReal_realPart_eq_of_conjugation_eq
    (z : StandardRealHilbertComplexification H)
    (hz : conjugation z = z) :
    ofReal z.1 = z := by
  apply Prod.ext
  · simp [ofReal]
  · simpa [ofReal] using (imag_eq_zero_of_conjugation_eq (H := H) z hz).symm

/-- The concrete standard complexification supplies the generic real-form
operator-complexification interface. -/
noncomputable def standardRealFormDecompositionData :
    RealHilbertBoundedOperatorComplexificationRealFormDecompositionData
      H (StandardRealHilbertComplexification H) where
  complexify := diagonalComplexificationStarAlgHom
  isometry_complexify := by
    simpa only [diagonalComplexificationStarAlgHom_apply] using
      diagonalComplexification_isometry (H := H)
  conjugation := conjugation
  ofReal := (standardOfRealLinearIsometry (H := H)).toContinuousLinearMap
  realPart := standardRealPartContinuousLinearMap (H := H)
  imagPart := fun z => z.2
  decompose := by
    intro z
    simpa using decompose z
  conjugation_ofReal := by
    intro x
    simpa using conjugation_ofReal x
  fixed_eq_ofReal_realPart := by
    intro z hz
    simpa using ofReal_realPart_eq_of_conjugation_eq (H := H) z hz
  complexify_apply_ofReal := by
    intro T x
    simpa using diagonalComplexification_ofReal T x
  complexify_commutes := by
    intro T z
    simpa using (diagonalComplexification_conjugation T z).symm

/-- A complex bounded operator belongs to the diagonal real-form range exactly
when it commutes with standard conjugation. -/
theorem mem_diagonalComplexificationStarSubalgebra_iff_commutes
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H) :
    X ∈ diagonalComplexificationStarSubalgebra (H := H) ↔
      ∀ z : StandardRealHilbertComplexification H,
        conjugation (X z) = X (conjugation z) := by
  constructor
  · intro hX
    rcases (mem_diagonalComplexificationStarSubalgebra_iff (H := H) X).1 hX with
      ⟨T, hT⟩
    intro z
    rw [← hT]
    exact (diagonalComplexification_conjugation T z).symm
  · intro hX
    have hrange :
        X ∈ (diagonalComplexificationStarAlgHom (H := H)).range :=
      ((standardRealFormDecompositionData (H := H)).range_iff_commutes X).2 hX
    rcases hrange with ⟨T, hT⟩
    exact (mem_diagonalComplexificationStarSubalgebra_iff (H := H) X).2
      ⟨T, by simpa only [diagonalComplexificationStarAlgHom_apply] using hT⟩

/-- The diagonal real-form range is closed under pointwise strong-operator
limits along any nontrivial filter.  No uniform operator-norm bound is needed
once the limit is already supplied as a bounded complex-linear operator. -/
theorem mem_diagonalComplexificationStarSubalgebra_of_tendsto_apply
    {ι : Type*} {l : Filter ι} [NeBot l]
    (F : ι → diagonalComplexificationStarSubalgebra (H := H))
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H)
    (hF : ∀ z : StandardRealHilbertComplexification H,
      Tendsto (fun i => (F i : StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) z) l (nhds (X z))) :
    X ∈ diagonalComplexificationStarSubalgebra (H := H) := by
  rw [mem_diagonalComplexificationStarSubalgebra_iff_commutes]
  intro z
  have hconj :
      Tendsto
        (fun i => conjugation
          ((F i : StandardRealHilbertComplexification H →L[ℂ]
            StandardRealHilbertComplexification H) z))
        l (nhds (conjugation (X z))) :=
    (continuous_standardConjugation (H := H)).tendsto (X z) |>.comp (hF z)
  have hfun :
      (fun i => conjugation
        ((F i : StandardRealHilbertComplexification H →L[ℂ]
          StandardRealHilbertComplexification H) z)) =
      (fun i => (F i : StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) (conjugation z)) := by
    funext i
    exact
      (mem_diagonalComplexificationStarSubalgebra_iff_commutes
        (H := H) (F i : StandardRealHilbertComplexification H →L[ℂ]
          StandardRealHilbertComplexification H)).1 (F i).property z
  rw [hfun] at hconj
  exact tendsto_nhds_unique hconj (hF (conjugation z))

/-- A pointwise strong limit of diagonal complexifications is the
complexification of a unique bounded real operator. -/
theorem tendsto_diagonalComplexification_apply_existsUnique_real_limit
    {ι : Type*} {l : Filter ι} [NeBot l]
    (f : ι → H →L[ℝ] H)
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H)
    (hF : ∀ z : StandardRealHilbertComplexification H,
      Tendsto (fun i => diagonalComplexification (f i) z) l (nhds (X z))) :
    ∃! T : H →L[ℝ] H, diagonalComplexification T = X := by
  let F : ι → diagonalComplexificationStarSubalgebra (H := H) :=
    fun i => diagonalComplexificationStarAlgEquiv (H := H) (f i)
  have hF' : ∀ z : StandardRealHilbertComplexification H,
      Tendsto (fun i => (F i : StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) z) l (nhds (X z)) := by
    intro z
    simpa [F] using hF z
  have hmem :=
    mem_diagonalComplexificationStarSubalgebra_of_tendsto_apply
      (H := H) F X hF'
  rcases (mem_diagonalComplexificationStarSubalgebra_iff (H := H) X).1 hmem with
    ⟨T, hT⟩
  refine ⟨T, hT, ?_⟩
  intro U hU
  apply (diagonalComplexificationLinearIsometry (H := H)).injective
  simpa only [diagonalComplexificationLinearIsometry_apply] using hT.trans hU.symm

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
