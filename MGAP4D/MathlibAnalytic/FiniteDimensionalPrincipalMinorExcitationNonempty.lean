import MGAP4D.MathlibAnalytic.FiniteDimensionalFullGroundExcitationNullDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- If the strictly excited sector is empty, every transfer eigenvalue is zero
or one, so the transfer is an idempotent positive projection. -/
theorem operator_comp_self_eq_self_of_not_nonempty_excitedSpectralIndex
    (hempty : ¬ Nonempty D.ExcitedSpectralIndex) :
    D.operator.comp D.operator = D.operator := by
  apply ContinuousLinearMap.ext
  intro x
  apply D.eigenbasis.repr.injective
  ext i
  have hdiag :
      D.eigenbasis.repr (D.operator x) i =
        D.eigenvalue i * D.eigenbasis.repr x i := by
    simpa [eigenbasis, eigenvalue] using
      D.symmetric.eigenvectorBasis_apply_self_apply (by rfl) x i
  have hdiag2 :
      D.eigenbasis.repr (D.operator (D.operator x)) i =
        D.eigenvalue i * D.eigenbasis.repr (D.operator x) i := by
    simpa [eigenbasis, eigenvalue] using
      D.symmetric.eigenvectorBasis_apply_self_apply
        (by rfl) (D.operator x) i
  change
    D.eigenbasis.repr (D.operator (D.operator x)) i =
      D.eigenbasis.repr (D.operator x) i
  rw [hdiag2, hdiag]
  rcases D.eigenvalue_trichotomy i with hz | he | hg
  · simp [hz]
  · exact False.elim (hempty ⟨⟨i, he⟩⟩)
  · simp [hg]

/-- A positive two-state transfer principal minor rules out collapse of the
entire transfer image onto one fixed ray.  Hence, once every fixed vector is
known to lie on one ray, the strictly excited spectral sector is inhabited. -/
theorem nonempty_excitedSpectralIndex_of_fixed_space_generated_and_minor_pos
    (p : E)
    (hfixed : ∀ g : E, D.operator g = g → ∃ c : ℝ, g = c • p)
    (u v : E)
    (hminor :
      0 < inner ℝ (D.operator u) u * inner ℝ (D.operator v) v -
        inner ℝ (D.operator u) v * inner ℝ (D.operator v) u) :
    Nonempty D.ExcitedSpectralIndex := by
  by_contra hempty
  have hidem :=
    D.operator_comp_self_eq_self_of_not_nonempty_excitedSpectralIndex hempty
  have hufix : D.operator (D.operator u) = D.operator u := by
    have h := congrArg
      (fun T : E →L[ℝ] E => T u) hidem
    simpa using h
  have hvfix : D.operator (D.operator v) = D.operator v := by
    have h := congrArg
      (fun T : E →L[ℝ] E => T v) hidem
    simpa using h
  obtain ⟨a, ha⟩ := hfixed (D.operator u) hufix
  obtain ⟨b, hb⟩ := hfixed (D.operator v) hvfix
  rw [ha, hb] at hminor
  simp only [real_inner_smul_left] at hminor
  nlinarith

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
