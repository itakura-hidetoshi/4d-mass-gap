import MGAP4D.MathlibAnalytic.FiniteDimensionalPositiveSpectralSupportIntertwining
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- If the positive spectral support is empty, positivity forces every
transfer eigenvalue to vanish and hence the full transfer is zero. -/
theorem operator_eq_zero_of_not_nonempty_positiveSpectralIndex
    (hempty : ¬ Nonempty D.PositiveSpectralIndex) :
    D.operator = 0 := by
  have hzero : ∀ i : Fin D.dimension, D.eigenvalue i = 0 := by
    intro i
    apply le_antisymm
    · apply le_of_not_gt
      intro hpos
      exact hempty ⟨⟨i, hpos⟩⟩
    · exact D.eigenvalue_nonneg i
  apply ContinuousLinearMap.ext
  intro x
  apply D.eigenbasis.repr.injective
  ext i
  rw [D.symmetric.eigenvectorBasis_apply_self_apply (by rfl)]
  simp [hzero i]

/-- Every nonzero finite-dimensional positive symmetric contraction has at
least one strictly positive transfer eigenvalue. -/
theorem nonempty_positiveSpectralIndex_of_operator_ne_zero
    (hne : D.operator ≠ 0) :
    Nonempty D.PositiveSpectralIndex := by
  by_contra hempty
  exact hne (D.operator_eq_zero_of_not_nonempty_positiveSpectralIndex hempty)

/-- For a nonzero transfer, the positive-support Hilbert space contains a
canonical nonzero coordinate vector. -/
theorem exists_nonzero_positiveSpectralSpace_of_operator_ne_zero
    (hne : D.operator ≠ 0) :
    ∃ x : D.PositiveSpectralSpace, x ≠ 0 := by
  let i : D.PositiveSpectralIndex :=
    Classical.choice (D.nonempty_positiveSpectralIndex_of_operator_ne_zero hne)
  refine ⟨EuclideanSpace.single i 1, ?_⟩
  intro hzero
  have hcoord := congrArg (fun x : D.PositiveSpectralSpace => x i) hzero
  simpa using hcoord

/-- The synthesized positive-support sector is nontrivial whenever the
original transfer is nonzero. -/
theorem exists_nonzero_positiveSpectralSynthesis_of_operator_ne_zero
    (hne : D.operator ≠ 0) :
    ∃ x : D.PositiveSpectralSpace,
      D.positiveSpectralSynthesis x ≠ 0 := by
  obtain ⟨x, hx⟩ := D.exists_nonzero_positiveSpectralSpace_of_operator_ne_zero hne
  refine ⟨x, ?_⟩
  intro hsynth
  exact hx (D.positiveSpectralSynthesis_injective hsynth)

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
