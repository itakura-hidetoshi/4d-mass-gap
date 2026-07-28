import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSFormBasic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Quadratic expansion needed for the semidefinite Cauchy--Schwarz argument. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_quadratic_sub_smul
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (a b : ℝ)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
        (a • F - b • G) (a • F - b • G) =
      a ^ 2 * linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F -
        2 * a * b *
          linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G +
        b ^ 2 * linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G G := by
  simp only [linearMarkovTwoSidedIntegerPathOSForm_sub_left,
    linearMarkovTwoSidedIntegerPathOSForm_sub_right,
    linearMarkovTwoSidedIntegerPathOSForm_smul_left,
    linearMarkovTwoSidedIntegerPathOSForm_smul_right]
  rw [linearMarkovTwoSidedIntegerPathOSForm_symmetric
    initial transition hdb G F]
  ring

/-- Cauchy--Schwarz inequality for the full path-space positive semidefinite OS
form. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_cauchy_schwarz
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    (linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G) ^ 2 ≤
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F *
        linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G G := by
  let A :=
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F
  let B :=
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G
  let C :=
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb G G
  have hA : 0 ≤ A := by
    dsimp [A]
    exact linearMarkovTwoSidedIntegerPathOSForm_nonneg
      initial transition hdb F
  have hC : 0 ≤ C := by
    dsimp [C]
    exact linearMarkovTwoSidedIntegerPathOSForm_nonneg
      initial transition hdb G
  by_cases hC0 : C = 0
  · have hz :=
      linearMarkovTwoSidedIntegerPathOSForm_nonneg
        initial transition hdb (B • F - (A + 1) • G)
    rw [linearMarkovTwoSidedIntegerPathOSForm_quadratic_sub_smul] at hz
    change
      0 ≤ B ^ 2 * A - 2 * B * (A + 1) * B + (A + 1) ^ 2 * C at hz
    change B ^ 2 ≤ A * C
    rw [hC0] at hz ⊢
    nlinarith [sq_nonneg B]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hz :=
      linearMarkovTwoSidedIntegerPathOSForm_nonneg
        initial transition hdb (C • F - B • G)
    rw [linearMarkovTwoSidedIntegerPathOSForm_quadratic_sub_smul] at hz
    change 0 ≤ C ^ 2 * A - 2 * C * B * B + B ^ 2 * C at hz
    change B ^ 2 ≤ A * C
    nlinarith [sq_nonneg B, sq_nonneg C]

/-- A null vector is OS-orthogonal to every positive-time cylinder observable. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_eq_zero_of_left_null
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω))
    (hF : linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F = 0)
    (G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G = 0 := by
  have hcs :=
    linearMarkovTwoSidedIntegerPathOSForm_cauchy_schwarz
      initial transition hdb F G
  rw [hF, zero_mul] at hcs
  nlinarith [sq_nonneg
    (linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F G)]

end

end MathlibAnalytic
end MGAP4D
