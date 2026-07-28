import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSPreHilbert

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The complete real Hilbert space obtained by completing the separated temporal
Osterwalder--Schrader pre-Hilbert space. -/
abbrev Hilbert
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :=
  UniformSpace.Completion D.Separated

noncomputable instance hilbertNormedAddCommGroup
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    NormedAddCommGroup D.Hilbert := by
  infer_instance

noncomputable instance hilbertInnerProductSpace
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    InnerProductSpace ℝ D.Hilbert := by
  infer_instance

noncomputable instance hilbertCompleteSpace
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    CompleteSpace D.Hilbert := by
  infer_instance

/-- The canonical dense embedding of the separated OS pre-Hilbert space into its
Hilbert completion. -/
def completedClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.Separated) : D.Hilbert :=
  (x : UniformSpace.Completion D.Separated)

/-- The completed Hilbert vector represented by a positive-time cylinder
observable. -/
def completedObservableClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) : D.Hilbert :=
  D.completedClass (D.observableClass F)

/-- The separated OS pre-Hilbert space has dense image in its completion. -/
theorem separated_dense_in_hilbert
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    DenseRange D.completedClass := by
  exact UniformSpace.Completion.denseRange_coe

/-- Completion preserves the inner product of separated OS vectors. -/
@[simp] theorem inner_completedClass_completedClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x y : D.Separated) :
    inner ℝ (D.completedClass x) (D.completedClass y) = inner ℝ x y := by
  exact UniformSpace.Completion.inner_coe x y

/-- The inner product of completed positive-time observable classes is exactly the
full two-sided path-space temporal OS form. -/
@[simp] theorem inner_completedObservableClass_completedObservableClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    inner ℝ (D.completedObservableClass F) (D.completedObservableClass G) =
      linearMarkovTwoSidedIntegerPathOSForm
        D.initial D.transition D.detailedBalance F G := by
  rw [completedObservableClass, completedObservableClass,
    D.inner_completedClass_completedClass]
  exact D.separated_inner_observableClass_observableClass F G

/-- The completed temporal OS space is positive definite. -/
theorem hilbert_inner_self_eq_zero_iff
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.Hilbert) :
    inner ℝ x x = 0 ↔ x = 0 := by
  rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero]

/-- The completed temporal OS carrier is complete. -/
theorem hilbert_complete
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    CompleteSpace D.Hilbert := by
  infer_instance

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
