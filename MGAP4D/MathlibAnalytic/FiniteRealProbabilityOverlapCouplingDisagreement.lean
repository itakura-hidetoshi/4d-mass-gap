import MGAP4D.MathlibAnalytic.FiniteRealProbabilityOverlapCoupling
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteRealProbabilityData

variable {G : Type} [DecidableEq G] [Fintype G]

/-- Unhalved `L¹` distance between two finite real probability laws. -/
def l1Distance
    (P Q : FiniteRealProbabilityData G) : ℝ :=
  ∑ g : G, |P.probability g - Q.probability g|

/-- The `L¹` distance is nonnegative. -/
theorem l1Distance_nonneg
    (P Q : FiniteRealProbabilityData G) :
    0 ≤ P.l1Distance Q := by
  exact Finset.sum_nonneg fun g _hg => abs_nonneg _

/-- The two residuals at one point add to the absolute probability
difference. -/
theorem leftResidual_add_rightResidual_eq_abs_sub
    (P Q : FiniteRealProbabilityData G)
    (g : G) :
    P.leftResidual Q g + P.rightResidual Q g =
      |P.probability g - Q.probability g| := by
  rcases le_total (P.probability g) (Q.probability g) with hpq | hqp
  · rw [leftResidual, rightResidual, overlap, min_eq_left hpq,
      abs_of_nonpos (sub_nonpos.mpr hpq)]
    ring
  · rw [leftResidual, rightResidual, overlap, min_eq_right hqp,
      abs_of_nonneg (sub_nonneg.mpr hqp)]
    ring

/-- The repository's unhalved `L¹` normalization is exactly twice the common
residual mass. -/
theorem l1Distance_eq_two_mul_residualMass
    (P Q : FiniteRealProbabilityData G) :
    P.l1Distance Q = 2 * P.residualMass Q := by
  unfold l1Distance
  calc
    (∑ g : G, |P.probability g - Q.probability g|) =
        ∑ g : G, (P.leftResidual Q g + P.rightResidual Q g) := by
      apply Finset.sum_congr rfl
      intro g _hg
      exact (P.leftResidual_add_rightResidual_eq_abs_sub Q g).symm
    _ = (∑ g : G, P.leftResidual Q g) +
          ∑ g : G, P.rightResidual Q g :=
      Finset.sum_add_distrib
    _ = P.residualMass Q + P.residualMass Q := by
      rw [P.sum_leftResidual Q, P.sum_rightResidual Q]
    _ = 2 * P.residualMass Q := by ring

/-- Equivalently, the common residual mass is half the unhalved `L¹`
distance. -/
theorem residualMass_eq_half_mul_l1Distance
    (P Q : FiniteRealProbabilityData G) :
    P.residualMass Q = (2 : ℝ)⁻¹ * P.l1Distance Q := by
  rw [P.l1Distance_eq_two_mul_residualMass Q]
  ring

end FiniteRealProbabilityData

namespace FiniteRealCouplingData

variable {G : Type} [DecidableEq G] [Fintype G]
variable {P Q : FiniteRealProbabilityData G}

/-- Coupling mass carried by equal-coordinate pairs. -/
def diagonalMass
    (C : FiniteRealCouplingData P Q) : ℝ :=
  ∑ g : G, C.joint g g

/-- Coupling disagreement mass, defined as total mass minus diagonal mass. -/
def disagreementMass
    (C : FiniteRealCouplingData P Q) : ℝ :=
  1 - C.diagonalMass

end FiniteRealCouplingData

namespace FiniteRealProbabilityData

variable {G : Type} [DecidableEq G] [Fintype G]

/-- The overlap coupling carries exactly the pointwise common mass on the
diagonal. -/
theorem overlapCouplingData_diagonalMass_eq_overlapMass
    (P Q : FiniteRealProbabilityData G) :
    (P.overlapCouplingData Q).diagonalMass = P.overlapMass Q := by
  by_cases hMass : P.residualMass Q = 0
  · have hOverlap : P.overlapMass Q = 1 := by
      unfold residualMass at hMass
      linarith
    calc
      (P.overlapCouplingData Q).diagonalMass =
          ∑ g : G, P.probability g := by
        unfold FiniteRealCouplingData.diagonalMass overlapCouplingData
        apply Finset.sum_congr rfl
        intro g _hg
        simp [overlapCoupling, hMass]
      _ = 1 := P.probability_sum_eq_one
      _ = P.overlapMass Q := hOverlap.symm
  · calc
      (P.overlapCouplingData Q).diagonalMass =
          ∑ g : G, P.overlap Q g := by
        unfold FiniteRealCouplingData.diagonalMass overlapCouplingData
        apply Finset.sum_congr rfl
        intro g _hg
        simp [overlapCoupling, hMass, overlapDiagonal,
          P.leftResidual_mul_rightResidual_eq_zero Q g]
      _ = P.overlapMass Q := rfl

/-- The overlap coupling disagreement mass is exactly the common residual
mass. -/
theorem overlapCouplingData_disagreementMass_eq_residualMass
    (P Q : FiniteRealProbabilityData G) :
    (P.overlapCouplingData Q).disagreementMass = P.residualMass Q := by
  unfold FiniteRealCouplingData.disagreementMass residualMass
  rw [P.overlapCouplingData_diagonalMass_eq_overlapMass Q]

/-- Hence overlap-coupling disagreement is exactly half the repository's
unhalved conditional `L¹` distance. -/
theorem overlapCouplingData_disagreementMass_eq_half_mul_l1Distance
    (P Q : FiniteRealProbabilityData G) :
    (P.overlapCouplingData Q).disagreementMass =
      (2 : ℝ)⁻¹ * P.l1Distance Q := by
  rw [P.overlapCouplingData_disagreementMass_eq_residualMass Q,
    P.residualMass_eq_half_mul_l1Distance Q]

/-- A weaker coefficient-friendly form: disagreement is bounded by the
unhalved `L¹` distance itself. -/
theorem overlapCouplingData_disagreementMass_le_l1Distance
    (P Q : FiniteRealProbabilityData G) :
    (P.overlapCouplingData Q).disagreementMass ≤ P.l1Distance Q := by
  rw [P.overlapCouplingData_disagreementMass_eq_half_mul_l1Distance Q]
  have hL1 := P.l1Distance_nonneg Q
  nlinarith

end FiniteRealProbabilityData

end

end MathlibAnalytic
end MGAP4D
