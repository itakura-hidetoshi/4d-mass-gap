import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSCauchySchwarz

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The OS null space of the positive-time cylinder algebra. -/
def linearMarkovTwoSidedIntegerPathOSNull
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition) :
    Submodule ℝ
      (linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) where
  carrier := {F |
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F = 0}
  zero_mem' := by
    exact linearMarkovTwoSidedIntegerPathOSForm_zero_left
      initial transition hdb 0
  add_mem' := by
    intro F G hF hG
    change
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F = 0 at hF
    change
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G G = 0 at hG
    change
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
        (F + G) (F + G) = 0
    rw [linearMarkovTwoSidedIntegerPathOSForm_add_left,
      linearMarkovTwoSidedIntegerPathOSForm_add_right,
      linearMarkovTwoSidedIntegerPathOSForm_add_right,
      hF, hG,
      linearMarkovTwoSidedIntegerPathOSForm_eq_zero_of_left_null
        initial transition hdb F hF G,
      linearMarkovTwoSidedIntegerPathOSForm_eq_zero_of_left_null
        initial transition hdb G hG F]
    norm_num
  smul_mem' := by
    intro c F hF
    change
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F = 0 at hF
    change
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
        (c • F) (c • F) = 0
    rw [linearMarkovTwoSidedIntegerPathOSForm_smul_left,
      linearMarkovTwoSidedIntegerPathOSForm_smul_right, hF]
    ring

@[simp] theorem mem_linearMarkovTwoSidedIntegerPathOSNull_iff
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    F ∈ linearMarkovTwoSidedIntegerPathOSNull initial transition hdb ↔
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F = 0 :=
  Iff.rfl

/-- Membership in the OS null space is equivalent to orthogonality against every
positive-time cylinder observable. -/
theorem mem_linearMarkovTwoSidedIntegerPathOSNull_iff_forall_orthogonal
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    F ∈ linearMarkovTwoSidedIntegerPathOSNull initial transition hdb ↔
      ∀ G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω),
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G = 0 := by
  constructor
  · intro hF G
    exact linearMarkovTwoSidedIntegerPathOSForm_eq_zero_of_left_null
      initial transition hdb F hF G
  · intro hF
    exact hF F

end

end MathlibAnalytic
end MGAP4D
