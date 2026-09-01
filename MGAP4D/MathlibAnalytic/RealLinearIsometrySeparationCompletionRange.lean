import MGAP4D.MathlibAnalytic.RealLinearIsometrySeparationCompletion

namespace MGAP4D
namespace MathlibAnalytic

open Set Topology UniformSpace

noncomputable section

variable {E F : Type*}
  [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- The image of a linear isometry after extending it to the uniform
completion is exactly the closure of its original image.

The forward inclusion is completion induction into the closed set
`closure (range f)`.  The reverse inclusion uses that an isometry from the
complete domain `Completion E` is a closed embedding. -/
theorem range_realLinearIsometryCompletionExtension_eq_closure_range
    (f : E →ₗᵢ[ℝ] F) :
    Set.range (realLinearIsometryCompletionExtension f) =
      closure (Set.range f) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    induction x using Completion.induction_on with
    | hp =>
        exact isClosed_closure.preimage
          (realLinearIsometryCompletionExtension f).continuous
    | ih x =>
        rw [realLinearIsometryCompletionExtension_coe]
        exact subset_closure (Set.mem_range_self x)
  · apply closure_minimal
    · rintro y ⟨x, rfl⟩
      exact ⟨(x : Completion E), by
        rw [realLinearIsometryCompletionExtension_coe]⟩
    · exact
        (realLinearIsometryCompletionExtension f).isometry.isClosedEmbedding.isClosed_range

/-- Passing through Mathlib's separation quotient does not change the image of
a linear isometry.  Surjectivity of `SeparationQuotient.mk` removes precisely
the zero-seminorm directions on which an isometry already vanishes. -/
theorem range_realLinearIsometrySeparationQuotient_eq_range
    (f : E →ₗᵢ[ℝ] F) :
    Set.range (realLinearIsometrySeparationQuotient f) = Set.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
    exact ⟨x, by
      rw [realLinearIsometrySeparationQuotient_mk]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨SeparationQuotient.mk x, by
      rw [realLinearIsometrySeparationQuotient_mk]⟩

/-- The canonical separation-plus-completion lift has image exactly the closure
of the original seminormed image.

This is the generic Hilbert-completion statement used by the Wilson OS
boundary realization: completion adds limit points and nothing else. -/
theorem range_realLinearIsometrySeparationCompletion_eq_closure_range
    (f : E →ₗᵢ[ℝ] F) :
    Set.range (realLinearIsometrySeparationCompletion f) =
      closure (Set.range f) := by
  rw [realLinearIsometrySeparationCompletion,
    range_realLinearIsometryCompletionExtension_eq_closure_range,
    range_realLinearIsometrySeparationQuotient_eq_range]

end

end MathlibAnalytic
end MGAP4D
