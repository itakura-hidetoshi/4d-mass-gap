import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A real-valued probability mass function on a finite carrier. -/
structure FiniteRealProbabilityData
    (G : Type) [Fintype G] where
  probability : G → ℝ
  probability_nonneg : ∀ g : G, 0 ≤ probability g
  probability_sum_eq_one : ∑ g : G, probability g = 1

/-- A nonnegative finite coupling with prescribed left and right marginals. -/
structure FiniteRealCouplingData
    {G : Type} [DecidableEq G] [Fintype G]
    (P Q : FiniteRealProbabilityData G) where
  joint : G → G → ℝ
  joint_nonneg : ∀ g h : G, 0 ≤ joint g h
  left_marginal : ∀ g : G, ∑ h : G, joint g h = P.probability g
  right_marginal : ∀ h : G, ∑ g : G, joint g h = Q.probability h

namespace FiniteRealProbabilityData

variable {G : Type} [DecidableEq G] [Fintype G]

/-- Pointwise common mass of two finite real probability laws. -/
def overlap
    (P Q : FiniteRealProbabilityData G)
    (g : G) : ℝ :=
  min (P.probability g) (Q.probability g)

/-- Left residual after removing the pointwise common mass. -/
def leftResidual
    (P Q : FiniteRealProbabilityData G)
    (g : G) : ℝ :=
  P.probability g - P.overlap Q g

/-- Right residual after removing the pointwise common mass. -/
def rightResidual
    (P Q : FiniteRealProbabilityData G)
    (g : G) : ℝ :=
  Q.probability g - P.overlap Q g

/-- Total pointwise common mass. -/
def overlapMass
    (P Q : FiniteRealProbabilityData G) : ℝ :=
  ∑ g : G, P.overlap Q g

/-- The common residual mass on either side. -/
def residualMass
    (P Q : FiniteRealProbabilityData G) : ℝ :=
  1 - P.overlapMass Q

/-- Left residuals are nonnegative. -/
theorem leftResidual_nonneg
    (P Q : FiniteRealProbabilityData G)
    (g : G) :
    0 ≤ P.leftResidual Q g := by
  unfold leftResidual overlap
  exact sub_nonneg.mpr (min_le_left _ _)

/-- Right residuals are nonnegative. -/
theorem rightResidual_nonneg
    (P Q : FiniteRealProbabilityData G)
    (g : G) :
    0 ≤ P.rightResidual Q g := by
  unfold rightResidual overlap
  exact sub_nonneg.mpr (min_le_right _ _)

/-- The left residuals sum to the residual mass. -/
theorem sum_leftResidual
    (P Q : FiniteRealProbabilityData G) :
    ∑ g : G, P.leftResidual Q g = P.residualMass Q := by
  unfold leftResidual residualMass overlapMass
  rw [Finset.sum_sub_distrib, P.probability_sum_eq_one]

/-- The right residuals sum to the same residual mass. -/
theorem sum_rightResidual
    (P Q : FiniteRealProbabilityData G) :
    ∑ g : G, P.rightResidual Q g = P.residualMass Q := by
  unfold rightResidual residualMass overlapMass
  rw [Finset.sum_sub_distrib, Q.probability_sum_eq_one]

/-- The residual mass is nonnegative. -/
theorem residualMass_nonneg
    (P Q : FiniteRealProbabilityData G) :
    0 ≤ P.residualMass Q := by
  rw [← P.sum_leftResidual Q]
  exact Finset.sum_nonneg fun g _hg => P.leftResidual_nonneg Q g

/-- At every carrier point at least one residual vanishes. -/
theorem leftResidual_mul_rightResidual_eq_zero
    (P Q : FiniteRealProbabilityData G)
    (g : G) :
    P.leftResidual Q g * P.rightResidual Q g = 0 := by
  rcases le_total (P.probability g) (Q.probability g) with hpq | hqp
  · rw [leftResidual, rightResidual, overlap, min_eq_left hpq]
    ring
  · rw [leftResidual, rightResidual, overlap, min_eq_right hqp]
    ring

/-- Vanishing total residual mass forces every left residual to vanish. -/
theorem leftResidual_eq_zero_of_residualMass_eq_zero
    (P Q : FiniteRealProbabilityData G)
    (hMass : P.residualMass Q = 0)
    (g : G) :
    P.leftResidual Q g = 0 := by
  have hSingle :
      P.leftResidual Q g ≤ ∑ x : G, P.leftResidual Q x := by
    exact Finset.single_le_sum
      (fun x _hx => P.leftResidual_nonneg Q x)
      (Finset.mem_univ g)
  rw [P.sum_leftResidual Q, hMass] at hSingle
  exact le_antisymm hSingle (P.leftResidual_nonneg Q g)

/-- Vanishing total residual mass forces every right residual to vanish. -/
theorem rightResidual_eq_zero_of_residualMass_eq_zero
    (P Q : FiniteRealProbabilityData G)
    (hMass : P.residualMass Q = 0)
    (g : G) :
    P.rightResidual Q g = 0 := by
  have hSingle :
      P.rightResidual Q g ≤ ∑ x : G, P.rightResidual Q x := by
    exact Finset.single_le_sum
      (fun x _hx => P.rightResidual_nonneg Q x)
      (Finset.mem_univ g)
  rw [P.sum_rightResidual Q, hMass] at hSingle
  exact le_antisymm hSingle (P.rightResidual_nonneg Q g)

/-- Zero residual mass is exactly equality of the two finite laws. -/
theorem probability_eq_of_residualMass_eq_zero
    (P Q : FiniteRealProbabilityData G)
    (hMass : P.residualMass Q = 0)
    (g : G) :
    P.probability g = Q.probability g := by
  have hLeft := P.leftResidual_eq_zero_of_residualMass_eq_zero Q hMass g
  have hRight := P.rightResidual_eq_zero_of_residualMass_eq_zero Q hMass g
  change P.probability g - P.overlap Q g = 0 at hLeft
  change Q.probability g - P.overlap Q g = 0 at hRight
  linarith

/-- Diagonal common-mass contribution to the overlap coupling. -/
def overlapDiagonal
    (P Q : FiniteRealProbabilityData G)
    (g h : G) : ℝ :=
  if g = h then P.overlap Q g else 0

/-- The finite overlap coupling.  If the residual mass is positive, the common
part is coupled diagonally and the two residual laws are coupled independently.
If the residual mass vanishes, the common law is coupled diagonally. -/
def overlapCoupling
    (P Q : FiniteRealProbabilityData G)
    (g h : G) : ℝ :=
  if _hMass : P.residualMass Q = 0 then
    if g = h then P.probability g else 0
  else
    P.overlapDiagonal Q g h +
      P.leftResidual Q g * P.rightResidual Q h /
        P.residualMass Q

/-- The diagonal common-mass contribution is nonnegative. -/
theorem overlapDiagonal_nonneg
    (P Q : FiniteRealProbabilityData G)
    (g h : G) :
    0 ≤ P.overlapDiagonal Q g h := by
  unfold overlapDiagonal overlap
  split_ifs
  · exact le_min (P.probability_nonneg g) (Q.probability_nonneg g)
  · exact le_rfl

/-- The overlap coupling is nonnegative. -/
theorem overlapCoupling_nonneg
    (P Q : FiniteRealProbabilityData G)
    (g h : G) :
    0 ≤ P.overlapCoupling Q g h := by
  unfold overlapCoupling
  split_ifs
  · exact P.probability_nonneg g
  · exact le_rfl
  · exact add_nonneg
      (P.overlapDiagonal_nonneg Q g h)
      (div_nonneg
        (mul_nonneg
          (P.leftResidual_nonneg Q g)
          (P.rightResidual_nonneg Q h))
        (P.residualMass_nonneg Q))

/-- The overlap coupling has the prescribed left marginal. -/
theorem sum_overlapCoupling_right
    (P Q : FiniteRealProbabilityData G)
    (g : G) :
    ∑ h : G, P.overlapCoupling Q g h = P.probability g := by
  by_cases hMass : P.residualMass Q = 0
  · simp [overlapCoupling, hMass]
  · rw [show (∑ h : G, P.overlapCoupling Q g h) =
        ∑ h : G,
          (P.overlapDiagonal Q g h +
            P.leftResidual Q g * P.rightResidual Q h /
              P.residualMass Q) by
        apply Finset.sum_congr rfl
        intro h _hh
        simp [overlapCoupling, hMass]]
    rw [Finset.sum_add_distrib]
    have hDiagonal :
        ∑ h : G, P.overlapDiagonal Q g h = P.overlap Q g := by
      simp [overlapDiagonal]
    have hResidual :
        (∑ h : G,
          P.leftResidual Q g * P.rightResidual Q h /
            P.residualMass Q) = P.leftResidual Q g := by
      rw [← Finset.sum_div, ← Finset.mul_sum, P.sum_rightResidual Q]
      field_simp
    rw [hDiagonal, hResidual]
    unfold leftResidual
    ring

/-- The overlap coupling has the prescribed right marginal. -/
theorem sum_overlapCoupling_left
    (P Q : FiniteRealProbabilityData G)
    (h : G) :
    ∑ g : G, P.overlapCoupling Q g h = Q.probability h := by
  by_cases hMass : P.residualMass Q = 0
  · have hEq : ∀ g : G, P.probability g = Q.probability g :=
      P.probability_eq_of_residualMass_eq_zero Q hMass
    simp [overlapCoupling, hMass, hEq h]
  · rw [show (∑ g : G, P.overlapCoupling Q g h) =
        ∑ g : G,
          (P.overlapDiagonal Q g h +
            P.leftResidual Q g * P.rightResidual Q h /
              P.residualMass Q) by
        apply Finset.sum_congr rfl
        intro g _hg
        simp [overlapCoupling, hMass]]
    rw [Finset.sum_add_distrib]
    have hDiagonal :
        ∑ g : G, P.overlapDiagonal Q g h = P.overlap Q h := by
      simp [overlapDiagonal]
    have hResidual :
        (∑ g : G,
          P.leftResidual Q g * P.rightResidual Q h /
            P.residualMass Q) = P.rightResidual Q h := by
      rw [← Finset.sum_div, ← Finset.sum_mul, P.sum_leftResidual Q]
      field_simp
    rw [hDiagonal, hResidual]
    unfold rightResidual
    ring

/-- The canonical overlap coupling data. -/
def overlapCouplingData
    (P Q : FiniteRealProbabilityData G) :
    FiniteRealCouplingData P Q :=
  { joint := P.overlapCoupling Q
    joint_nonneg := P.overlapCoupling_nonneg Q
    left_marginal := P.sum_overlapCoupling_right Q
    right_marginal := P.sum_overlapCoupling_left Q }

end FiniteRealProbabilityData

namespace FiniteRealCouplingData

variable {G : Type} [DecidableEq G] [Fintype G]
variable {P Q : FiniteRealProbabilityData G}

/-- Every finite coupling has total mass one. -/
theorem totalMass_eq_one
    (C : FiniteRealCouplingData P Q) :
    ∑ g : G, ∑ h : G, C.joint g h = 1 := by
  simp_rw [C.left_marginal]
  exact P.probability_sum_eq_one

end FiniteRealCouplingData

end

end MathlibAnalytic
end MGAP4D
