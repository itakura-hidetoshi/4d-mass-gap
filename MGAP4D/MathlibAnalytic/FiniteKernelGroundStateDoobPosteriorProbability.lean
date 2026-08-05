import MGAP4D.MathlibAnalytic.FiniteRealProbabilityOverlapCoupling
import MGAP4D.MathlibAnalytic.FiniteStrictlyPositiveKernelGroundStateDoobJointMeasure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Total mass of a finite real weight. -/
def finiteRealWeightPartition
    {α : Type}
    [Fintype α]
    (weight : α → ℝ) : ℝ :=
  ∑ x : α, weight x

/-- Global normalization of a finite real weight. -/
def finiteRealWeightProbability
    {α : Type}
    [Fintype α]
    (weight : α → ℝ)
    (x : α) : ℝ :=
  weight x / finiteRealWeightPartition weight

/-- A nonnegative finite weight with positive total mass defines a finite real
probability law. -/
noncomputable def finiteRealWeightProbabilityData
    {α : Type}
    [Fintype α]
    (weight : α → ℝ)
    (hweight : ∀ x : α, 0 ≤ weight x)
    (hPartition : 0 < finiteRealWeightPartition weight) :
    FiniteRealProbabilityData α :=
  { probability := finiteRealWeightProbability weight
    probability_nonneg := fun x =>
      div_nonneg (hweight x) (le_of_lt hPartition)
    probability_sum_eq_one := by
      unfold finiteRealWeightProbability
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hPartition) }

namespace FiniteKernelGroundStateDoobData

variable {α : Type} [Fintype α]

/-- Unnormalized posterior weight of the first layer conditioned on a fixed
second-layer state. -/
def groundPosteriorWeight
    (D : FiniteKernelGroundStateDoobData α)
    (y x : α) : ℝ :=
  D.kernel x y * D.ground x

/-- The ground posterior weight is nonnegative. -/
theorem groundPosteriorWeight_nonneg
    (D : FiniteKernelGroundStateDoobData α)
    (y x : α) :
    0 ≤ D.groundPosteriorWeight y x := by
  exact mul_nonneg (D.kernel_nonneg x y) (le_of_lt (D.ground_pos x))

/-- The posterior partition is exactly the ground-weighted kernel column mass. -/
theorem groundPosteriorWeight_partition
    (D : FiniteKernelGroundStateDoobData α)
    (y : α) :
    finiteRealWeightPartition (D.groundPosteriorWeight y) =
      D.groundWeightedColumnMass y := by
  rfl

/-- Every ground posterior has strictly positive total mass. -/
theorem groundPosteriorWeight_partition_pos
    (D : FiniteKernelGroundStateDoobData α)
    (y : α) :
    0 < finiteRealWeightPartition (D.groundPosteriorWeight y) := by
  rw [D.groundPosteriorWeight_partition y]
  exact D.groundWeightedColumnMass_pos y

/-- The normalized ground posterior probability law. -/
noncomputable def groundPosteriorProbabilityData
    (D : FiniteKernelGroundStateDoobData α)
    (y : α) :
    FiniteRealProbabilityData α :=
  finiteRealWeightProbabilityData
    (D.groundPosteriorWeight y)
    (D.groundPosteriorWeight_nonneg y)
    (D.groundPosteriorWeight_partition_pos y)

/-- Pointwise, the normalized ground posterior is exactly the ground-state
Doob row. -/
theorem groundPosteriorProbabilityData_probability_eq_doobKernel
    (D : FiniteKernelGroundStateDoobData α)
    (y x : α) :
    (D.groundPosteriorProbabilityData y).probability x =
      D.doobKernel x y := by
  unfold groundPosteriorProbabilityData finiteRealWeightProbabilityData
    finiteRealWeightProbability groundPosteriorWeight
  rw [D.groundPosteriorWeight_partition]
  exact (D.doobKernel_eq_groundPosterior x y).symm

/-- The Doob row itself, packaged directly as a finite probability law. -/
noncomputable def doobRowProbabilityData
    (D : FiniteKernelGroundStateDoobData α)
    (y : α) :
    FiniteRealProbabilityData α :=
  { probability := fun x => D.doobKernel x y
    probability_nonneg := fun x => D.doobKernel_nonneg x y
    probability_sum_eq_one := D.doobKernel_sum_eq_one y }

/-- The direct Doob-row package and the normalized-posterior package coincide. -/
theorem doobRowProbabilityData_eq_groundPosteriorProbabilityData
    (D : FiniteKernelGroundStateDoobData α)
    (y : α) :
    D.doobRowProbabilityData y = D.groundPosteriorProbabilityData y := by
  cases D.doobRowProbabilityData y with
  | mk p hp hsum =>
      cases D.groundPosteriorProbabilityData y with
      | mk q hq qsum =>
          simp only [doobRowProbabilityData, groundPosteriorProbabilityData]
          congr 1
          funext x
          exact
            (D.groundPosteriorProbabilityData_probability_eq_doobKernel y x).symm

/-- Canonical full-state overlap coupling between two geometric Doob rows. -/
noncomputable def doobRowOverlapCouplingData
    [DecidableEq α]
    (D : FiniteKernelGroundStateDoobData α)
    (left right : α) :
    FiniteRealCouplingData
      (D.doobRowProbabilityData left)
      (D.doobRowProbabilityData right) :=
  (D.doobRowProbabilityData left).overlapCouplingData
    (D.doobRowProbabilityData right)

/-- The left marginal of the geometric Doob-row coupling is exactly the left
Doob row. -/
theorem doobRowOverlapCouplingData_leftMarginal
    [DecidableEq α]
    (D : FiniteKernelGroundStateDoobData α)
    (left right x : α) :
    ∑ y : α, (D.doobRowOverlapCouplingData left right).joint x y =
      D.doobKernel x left := by
  exact (D.doobRowOverlapCouplingData left right).left_marginal x

/-- The right marginal of the geometric Doob-row coupling is exactly the right
Doob row. -/
theorem doobRowOverlapCouplingData_rightMarginal
    [DecidableEq α]
    (D : FiniteKernelGroundStateDoobData α)
    (left right y : α) :
    ∑ x : α, (D.doobRowOverlapCouplingData left right).joint x y =
      D.doobKernel y right := by
  exact (D.doobRowOverlapCouplingData left right).right_marginal y

end FiniteKernelGroundStateDoobData

end

end MathlibAnalytic
end MGAP4D
