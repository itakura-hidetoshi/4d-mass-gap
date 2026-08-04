import MGAP4D.MathlibAnalytic.FiniteStrictlyPositiveKernelGroundStateDoobTransform
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

namespace FiniteKernelGroundStateDoobData

variable {α : Type} [Fintype α]

/-- Column mass obtained by weighting the original positive kernel with its
Perron ground. -/
def groundWeightedColumnMass
    (D : FiniteKernelGroundStateDoobData α)
    (y : α) : ℝ :=
  ∑ x : α, D.kernel x y * D.ground x

/-- Every ground-weighted column mass is strictly positive. -/
theorem groundWeightedColumnMass_pos
    (D : FiniteKernelGroundStateDoobData α)
    (y : α) :
    0 < D.groundWeightedColumnMass y := by
  have hNorm : 0 < ‖finiteKernelOperator D.kernel‖ :=
    norm_pos_iff.mpr D.raw_ne_zero
  have hInv : 0 < ‖finiteKernelOperator D.kernel‖⁻¹ :=
    inv_pos.mpr hNorm
  have hProd :
      0 < ‖finiteKernelOperator D.kernel‖⁻¹ *
        D.groundWeightedColumnMass y := by
    rw [groundWeightedColumnMass, D.normalized_kernel_ground_sum]
    exact D.ground_pos y
  nlinarith

/-- The Doob kernel is exactly the posterior obtained by normalizing the
original kernel column against the positive Perron ground.  The operator norm
normalization cancels completely. -/
theorem doobKernel_eq_groundPosterior
    (D : FiniteKernelGroundStateDoobData α)
    (x y : α) :
    D.doobKernel x y =
      (D.kernel x y * D.ground x) /
        D.groundWeightedColumnMass y := by
  have hNorm : 0 < ‖finiteKernelOperator D.kernel‖ :=
    norm_pos_iff.mpr D.raw_ne_zero
  have hMass : 0 < D.groundWeightedColumnMass y :=
    D.groundWeightedColumnMass_pos y
  unfold doobKernel
  rw [← D.normalized_kernel_ground_sum y]
  change
    (‖finiteKernelOperator D.kernel‖⁻¹ * D.kernel x y * D.ground x) /
        (‖finiteKernelOperator D.kernel‖⁻¹ *
          D.groundWeightedColumnMass y) =
      (D.kernel x y * D.ground x) /
        D.groundWeightedColumnMass y
  field_simp [ne_of_gt hNorm, ne_of_gt hMass]

/-- Symmetric two-layer weight associated with the reversible Doob chain. -/
def jointWeight
    (D : FiniteKernelGroundStateDoobData α)
    (x y : α) : ℝ :=
  D.ground y ^ 2 * D.doobKernel x y

/-- The joint weight is nonnegative. -/
theorem jointWeight_nonneg
    (D : FiniteKernelGroundStateDoobData α)
    (x y : α) :
    0 ≤ D.jointWeight x y := by
  exact mul_nonneg (sq_nonneg _) (D.doobKernel_nonneg x y)

/-- Detailed balance is precisely symmetry of the two-layer joint weight. -/
theorem jointWeight_symmetric
    (D : FiniteKernelGroundStateDoobData α)
    (x y : α) :
    D.jointWeight x y = D.jointWeight y x := by
  exact D.doobKernel_detailedBalance x y

/-- The joint weight can also be written directly from the normalized original
kernel and both Perron ground factors. -/
theorem jointWeight_eq_normalizedKernel_mul_ground
    (D : FiniteKernelGroundStateDoobData α)
    (x y : α) :
    D.jointWeight x y =
      ‖finiteKernelOperator D.kernel‖⁻¹ *
        D.kernel x y * D.ground x * D.ground y := by
  unfold jointWeight doobKernel
  field_simp [ne_of_gt (D.ground_pos y)]

/-- The right marginal of the joint weight is the reversible Perron density
`ground²`.  No normalization of the chosen Perron vector is required. -/
theorem jointWeight_rightMarginal
    (D : FiniteKernelGroundStateDoobData α)
    (y : α) :
    ∑ x : α, D.jointWeight x y = D.ground y ^ 2 := by
  unfold jointWeight
  rw [← Finset.mul_sum, D.doobKernel_sum_eq_one, mul_one]

/-- Symmetry gives the same Perron density as the left marginal. -/
theorem jointWeight_leftMarginal
    (D : FiniteKernelGroundStateDoobData α)
    (x : α) :
    ∑ y : α, D.jointWeight x y = D.ground x ^ 2 := by
  calc
    (∑ y : α, D.jointWeight x y) =
        ∑ y : α, D.jointWeight y x := by
      apply Finset.sum_congr rfl
      intro y _hy
      exact D.jointWeight_symmetric x y
    _ = D.ground x ^ 2 := D.jointWeight_rightMarginal x

/-- The total mass of the two-layer joint weight equals the squared norm of the
chosen Perron ground. -/
theorem jointWeight_totalMass
    (D : FiniteKernelGroundStateDoobData α) :
    ∑ y : α, ∑ x : α, D.jointWeight x y = ‖D.ground‖ ^ 2 := by
  simp_rw [D.jointWeight_rightMarginal]
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro y _hy
  simpa [Real.norm_eq_abs, sq_abs] using
    (real_inner_self_eq_norm_sq (D.ground.ofLp y)).symm

/-- The weighted Doob quadratic form is the two-layer correlation quadratic
form under the symmetric joint weight. -/
theorem weightedDoobQuadratic_eq_jointCorrelation
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) :
    D.weightedDoobQuadratic f =
      ∑ y : α, ∑ x : α,
        D.jointWeight x y * f x * f y := by
  unfold weightedDoobQuadratic weightedInner
  simp only [finiteKernelOperator_apply]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _hx
  unfold jointWeight
  ring

/-- The first-coordinate square moment of the joint weight is the weighted
Perron norm. -/
theorem jointFirstSquare_eq_weightedNormSq
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) :
    (∑ y : α, ∑ x : α, D.jointWeight x y * f x ^ 2) =
      D.weightedNormSq f := by
  rw [Finset.sum_comm]
  unfold weightedNormSq weightedInner
  apply Finset.sum_congr rfl
  intro x _hx
  rw [← Finset.sum_mul, D.jointWeight_leftMarginal]
  ring

/-- The second-coordinate square moment has the same weighted Perron norm. -/
theorem jointSecondSquare_eq_weightedNormSq
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) :
    (∑ y : α, ∑ x : α, D.jointWeight x y * f y ^ 2) =
      D.weightedNormSq f := by
  unfold weightedNormSq weightedInner
  apply Finset.sum_congr rfl
  intro y _hy
  rw [← Finset.sum_mul, D.jointWeight_rightMarginal]
  ring

/-- Exact reversible Dirichlet-form identity for the ground-state Doob chain. -/
theorem weightedNormSq_sub_weightedDoobQuadratic_eq_jointDifference
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) :
    D.weightedNormSq f - D.weightedDoobQuadratic f =
      (2 : ℝ)⁻¹ *
        ∑ y : α, ∑ x : α,
          D.jointWeight x y * (f x - f y) ^ 2 := by
  have hFirst := D.jointFirstSquare_eq_weightedNormSq f
  have hSecond := D.jointSecondSquare_eq_weightedNormSq f
  have hCross := D.weightedDoobQuadratic_eq_jointCorrelation f
  calc
    D.weightedNormSq f - D.weightedDoobQuadratic f =
        (2 : ℝ)⁻¹ *
          (D.weightedNormSq f -
            2 * D.weightedDoobQuadratic f +
            D.weightedNormSq f) := by ring
    _ = (2 : ℝ)⁻¹ *
          ((∑ y : α, ∑ x : α, D.jointWeight x y * f x ^ 2) -
            2 * (∑ y : α, ∑ x : α,
              D.jointWeight x y * f x * f y) +
            (∑ y : α, ∑ x : α,
              D.jointWeight x y * f y ^ 2)) := by
      rw [hFirst, hSecond, ← hCross]
    _ = (2 : ℝ)⁻¹ *
        ∑ y : α, ∑ x : α,
          D.jointWeight x y * (f x - f y) ^ 2 := by
      congr 1
      have hTwo :
          2 * (∑ y : α, ∑ x : α,
              D.jointWeight x y * f x * f y) =
            ∑ y : α, ∑ x : α,
              2 * (D.jointWeight x y * f x * f y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Finset.mul_sum]
      rw [hTwo]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _hx
      ring

end FiniteKernelGroundStateDoobData

end

end MathlibAnalytic
end MGAP4D
