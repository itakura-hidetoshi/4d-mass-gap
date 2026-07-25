import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalStarAlgHom
import Mathlib.Algebra.Star.Subalgebra

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The star subalgebra of complex bounded endomorphisms obtained by diagonal complexification. -/
noncomputable def diagonalComplexificationStarSubalgebra :
    StarSubalgebra ℝ
      (StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) :=
  (⊤ : StarSubalgebra ℝ (H →L[ℝ] H)).map diagonalComplexificationStarAlgHom

@[simp]
theorem mem_diagonalComplexificationStarSubalgebra_iff
    (S : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H) :
    S ∈ diagonalComplexificationStarSubalgebra (H := H) ↔
      ∃ T : H →L[ℝ] H, diagonalComplexification T = S := by
  simp [diagonalComplexificationStarSubalgebra]

/-- Diagonal complexification, with codomain restricted to its star-subalgebra range. -/
noncomputable def diagonalComplexificationToStarSubalgebra :
    (H →L[ℝ] H) →⋆ₐ[ℝ] diagonalComplexificationStarSubalgebra (H := H) where
  toFun T := ⟨diagonalComplexification T, by
    exact (mem_diagonalComplexificationStarSubalgebra_iff
      (H := H) (diagonalComplexification T)).2 ⟨T, rfl⟩⟩
  map_one' := Subtype.ext (map_one diagonalComplexificationStarAlgHom)
  map_mul' T U := Subtype.ext (map_mul diagonalComplexificationStarAlgHom T U)
  map_zero' := Subtype.ext (map_zero diagonalComplexificationStarAlgHom)
  map_add' T U := Subtype.ext (map_add diagonalComplexificationStarAlgHom T U)
  commutes' r := Subtype.ext (map_algebraMap diagonalComplexificationStarAlgHom r)
  map_star' T := Subtype.ext (map_star diagonalComplexificationStarAlgHom T)

@[simp]
theorem diagonalComplexificationToStarSubalgebra_apply (T : H →L[ℝ] H) :
    (diagonalComplexificationToStarSubalgebra (H := H) T :
      StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) =
      diagonalComplexification T :=
  rfl

/-- The restricted diagonal complexification map is injective. -/
theorem diagonalComplexificationToStarSubalgebra_injective :
    Function.Injective (diagonalComplexificationToStarSubalgebra (H := H)) := by
  intro T U h
  apply diagonalComplexificationStarAlgHom_injective (H := H)
  exact congr_arg Subtype.val h

/-- The restricted diagonal complexification map is surjective onto its bundled range. -/
theorem diagonalComplexificationToStarSubalgebra_surjective :
    Function.Surjective (diagonalComplexificationToStarSubalgebra (H := H)) := by
  intro S
  rcases (mem_diagonalComplexificationStarSubalgebra_iff (H := H) S.1).1 S.2 with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  exact Subtype.ext hT

/-- The real bounded endomorphism star algebra is star-algebra equivalent to the diagonal range. -/
noncomputable def diagonalComplexificationStarAlgEquiv :
    (H →L[ℝ] H) ≃⋆ₐ[ℝ] diagonalComplexificationStarSubalgebra (H := H) :=
  StarAlgEquiv.ofBijective
    (diagonalComplexificationToStarSubalgebra (H := H))
    ⟨diagonalComplexificationToStarSubalgebra_injective (H := H),
      diagonalComplexificationToStarSubalgebra_surjective (H := H)⟩

@[simp]
theorem diagonalComplexificationStarAlgEquiv_apply (T : H →L[ℝ] H) :
    (diagonalComplexificationStarAlgEquiv (H := H) T :
      StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) =
      diagonalComplexification T :=
  rfl

@[simp]
theorem diagonalComplexificationStarAlgEquiv_symm_apply_apply (T : H →L[ℝ] H) :
    (diagonalComplexificationStarAlgEquiv (H := H)).symm
      (diagonalComplexificationStarAlgEquiv (H := H) T) = T :=
  StarAlgEquiv.symm_apply_apply _ T

@[simp]
theorem diagonalComplexificationStarAlgEquiv_apply_symm_apply
    (S : diagonalComplexificationStarSubalgebra (H := H)) :
    diagonalComplexificationStarAlgEquiv (H := H)
      ((diagonalComplexificationStarAlgEquiv (H := H)).symm S) = S :=
  StarAlgEquiv.apply_symm_apply _ S

/-- The diagonal range inclusion recovers the original diagonal complexification homomorphism. -/
theorem diagonalComplexificationStarSubalgebra_subtype_comp :
    (diagonalComplexificationStarSubalgebra (H := H)).subtype.comp
      (diagonalComplexificationToStarSubalgebra (H := H)) =
        diagonalComplexificationStarAlgHom := by
  ext T
  rfl

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
