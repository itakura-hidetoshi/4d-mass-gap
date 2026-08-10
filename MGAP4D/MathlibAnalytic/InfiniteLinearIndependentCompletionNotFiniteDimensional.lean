import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.LinearAlgebra.Dimension.Finite

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u

/-- A real vector space containing an `ℕ`-indexed linearly independent family
cannot be finite-dimensional.

This is the direct contrapositive of Mathlib's
`Module.Finite.not_linearIndependent_of_infinite` for the infinite index type
`ℕ`. -/
theorem not_finiteDimensional_of_nat_linearIndependent
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    (v : ℕ → V) (hv : LinearIndependent ℝ v) :
    ¬ FiniteDimensional ℝ V := by
  intro hFinite
  letI : FiniteDimensional ℝ V := hFinite
  exact (Module.Finite.not_linearIndependent_of_infinite v) hv

/-- Non-finite-dimensionality passes from a normed real vector space to its
uniform completion.

Indeed, if the completion were finite-dimensional, Mathlib's canonical linear
isometry into the completion would be an injective linear map into a
finite-dimensional target, and `FiniteDimensional.of_injective` would force the
source to be finite-dimensional as well. -/
theorem completion_not_finiteDimensional_of_not_finiteDimensional
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hInfinite : ¬ FiniteDimensional ℝ V) :
    ¬ FiniteDimensional ℝ (UniformSpace.Completion V) := by
  intro hCompletionFinite
  letI : FiniteDimensional ℝ (UniformSpace.Completion V) := hCompletionFinite
  have hSourceFinite : FiniteDimensional ℝ V :=
    FiniteDimensional.of_injective
      (UniformSpace.Completion.toComplₗᵢ :
        V →ₗᵢ[ℝ] UniformSpace.Completion V).toLinearMap
      (UniformSpace.Completion.toComplₗᵢ :
        V →ₗᵢ[ℝ] UniformSpace.Completion V).injective
  exact hInfinite hSourceFinite

/-- A countable linearly independent family in a normed real vector space
therefore forces its Hilbert/uniform completion to be non-finite-dimensional. -/
theorem completion_not_finiteDimensional_of_nat_linearIndependent
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : ℕ → V) (hv : LinearIndependent ℝ v) :
    ¬ FiniteDimensional ℝ (UniformSpace.Completion V) :=
  completion_not_finiteDimensional_of_not_finiteDimensional
    (not_finiteDimensional_of_nat_linearIndependent v hv)

end

end MathlibAnalytic
end MGAP4D
