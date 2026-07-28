import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertCompletion
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSShiftContraction
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The contractive positive-time shift extended continuously to the completed
 temporal OS Hilbert space. -/
noncomputable def hilbertShiftContinuousLinearMap
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.Hilbert →L[ℝ] D.Hilbert :=
  D.separatedShiftContinuousLinearMap.completion

/-- The completed shift agrees with the separated shift on the canonical dense
 embedding. -/
@[simp] theorem hilbertShiftContinuousLinearMap_completedClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.Separated) :
    D.hilbertShiftContinuousLinearMap (D.completedClass x) =
      D.completedClass (D.separatedShiftContinuousLinearMap x) := by
  exact ContinuousLinearMap.completion_apply_coe
    D.separatedShiftContinuousLinearMap x

/-- On completed observable classes, the Hilbert-space shift is the original
 positive-time translation. -/
@[simp] theorem hilbertShiftContinuousLinearMap_completedObservableClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    D.hilbertShiftContinuousLinearMap (D.completedObservableClass F) =
      D.completedObservableClass (linearMarkovPositiveTimeShiftAlgHom F) := by
  rw [completedObservableClass, completedObservableClass,
    D.hilbertShiftContinuousLinearMap_completedClass,
    D.separatedShiftContinuousLinearMap_observableClass]

/-- The completed temporal shift remains norm nonincreasing. -/
theorem norm_hilbertShiftContinuousLinearMap_le
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.Hilbert) :
    ‖D.hilbertShiftContinuousLinearMap x‖ ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le
      (continuous_norm.comp D.hilbertShiftContinuousLinearMap.continuous)
      continuous_norm) ?_
  intro y
  change ‖D.hilbertShiftContinuousLinearMap (D.completedClass y)‖ ≤
    ‖D.completedClass y‖
  rw [D.hilbertShiftContinuousLinearMap_completedClass]
  simpa [completedClass] using D.norm_separatedShiftLinearMap_le y

/-- The Hilbert-space extension is uniquely determined by its action on the dense
 separated OS subspace. -/
theorem hilbertShiftContinuousLinearMap_unique
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (T : D.Hilbert →L[ℝ] D.Hilbert)
    (hT : ∀ x : D.Separated,
      T (D.completedClass x) =
        D.completedClass (D.separatedShiftContinuousLinearMap x)) :
    T = D.hilbertShiftContinuousLinearMap := by
  ext z
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq T.continuous D.hilbertShiftContinuousLinearMap.continuous) ?_
  intro x
  change T (D.completedClass x) =
    D.hilbertShiftContinuousLinearMap (D.completedClass x)
  rw [hT x, D.hilbertShiftContinuousLinearMap_completedClass]

/-- Symmetry of the separated temporal shift extends to the complete temporal OS
 Hilbert space. -/
theorem inner_hilbertShiftContinuousLinearMap_left_eq_right
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x y : D.Hilbert) :
    inner ℝ (D.hilbertShiftContinuousLinearMap x) y =
      inner ℝ x (D.hilbertShiftContinuousLinearMap y) := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u v
  change inner ℝ
      (D.hilbertShiftContinuousLinearMap (D.completedClass u))
      (D.completedClass v) =
    inner ℝ (D.completedClass u)
      (D.hilbertShiftContinuousLinearMap (D.completedClass v))
  rw [D.hilbertShiftContinuousLinearMap_completedClass,
    D.hilbertShiftContinuousLinearMap_completedClass,
    D.inner_completedClass_completedClass,
    D.inner_completedClass_completedClass]
  exact D.inner_separatedShiftContinuousLinearMap_left_eq_right u v

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
