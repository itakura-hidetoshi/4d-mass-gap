import MGAP4D.MathlibAnalytic.FiniteProductHammingLipschitzVariation
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityExpectation
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityMixtureCouplingCost
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteRealCouplingData

variable {G : Type} [DecidableEq G] [Fintype G]
variable {P Q : FiniteRealProbabilityData G}

/-- A left marginal expectation can be written as a joint expectation under
any exact coupling. -/
theorem left_expectation_eq_joint
    (C : FiniteRealCouplingData P Q)
    (f : G → ℝ) :
    P.expectation f =
      ∑ x : G, ∑ y : G, C.joint x y * f x := by
  unfold FiniteRealProbabilityData.expectation
  apply Finset.sum_congr rfl
  intro x _hx
  calc
    P.probability x * f x =
        (∑ y : G, C.joint x y) * f x := by
      rw [C.left_marginal x]
    _ = ∑ y : G, C.joint x y * f x := by
      rw [Finset.sum_mul]

/-- A right marginal expectation can be written in the same joint order under
any exact coupling. -/
theorem right_expectation_eq_joint
    (C : FiniteRealCouplingData P Q)
    (f : G → ℝ) :
    Q.expectation f =
      ∑ x : G, ∑ y : G, C.joint x y * f y := by
  unfold FiniteRealProbabilityData.expectation
  calc
    (∑ y : G, Q.probability y * f y) =
        ∑ y : G, ∑ x : G, C.joint x y * f y := by
      apply Finset.sum_congr rfl
      intro y _hy
      calc
        Q.probability y * f y =
            (∑ x : G, C.joint x y) * f y := by
          rw [C.right_marginal y]
        _ = ∑ x : G, C.joint x y * f y := by
          rw [Finset.sum_mul]
    _ = ∑ x : G, ∑ y : G, C.joint x y * f y := by
      rw [Finset.sum_comm]

/-- Difference of marginal expectations is the joint expectation of the
pointwise observable difference. -/
theorem expectation_sub_eq_joint_difference
    (C : FiniteRealCouplingData P Q)
    (f : G → ℝ) :
    P.expectation f - Q.expectation f =
      ∑ x : G, ∑ y : G,
        C.joint x y * (f x - f y) := by
  rw [C.left_expectation_eq_joint f, C.right_expectation_eq_joint f]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _hy
  ring

/-- Finite Kantorovich weak duality: if an observable difference is bounded
pointwise by a pair cost, then its difference of marginal expectations is
bounded by the coupling's expected cost. -/
theorem expectation_difference_abs_le_expectedCost
    (C : FiniteRealCouplingData P Q)
    (cost : G → G → ℝ)
    (f : G → ℝ)
    (hCost : ∀ x y : G, |f x - f y| ≤ cost x y) :
    |P.expectation f - Q.expectation f| ≤
      C.expectedCost cost := by
  rw [C.expectation_sub_eq_joint_difference f]
  calc
    |∑ x : G, ∑ y : G,
        C.joint x y * (f x - f y)| ≤
        ∑ x : G, |∑ y : G,
          C.joint x y * (f x - f y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : G, ∑ y : G,
          |C.joint x y * (f x - f y)| := by
      apply Finset.sum_le_sum
      intro x _hx
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x : G, ∑ y : G,
          C.joint x y * |f x - f y| := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      rw [abs_mul, abs_of_nonneg (C.joint_nonneg x y)]
    _ ≤ ∑ x : G, ∑ y : G,
          C.joint x y * cost x y := by
      apply Finset.sum_le_sum
      intro x _hx
      apply Finset.sum_le_sum
      intro y _hy
      exact mul_le_mul_of_nonneg_left
        (hCost x y) (C.joint_nonneg x y)
    _ = C.expectedCost cost := by
      rfl

end FiniteRealCouplingData

namespace FiniteRealProbabilityData

variable {ι G : Type}
variable [DecidableEq ι] [Fintype ι]
variable [DecidableEq G] [Fintype G]

/-- A bound on the expectation difference of every real Hamming
`1`-Lipschitz observable.  This is the dual side of finite Hamming transport. -/
def HammingDualBound
    (P Q : FiniteRealProbabilityData (ι → G))
    (bound : ℝ) : Prop :=
  ∀ f : (ι → G) → ℝ,
    FiniteProductHammingOneLipschitz f →
      |P.expectation f - Q.expectation f| ≤ bound

/-- Every exact coupling supplies a Hamming dual bound equal to its expected
Hamming cost. -/
theorem hammingDualBound_expectedHammingCost
    (P Q : FiniteRealProbabilityData (ι → G))
    (C : FiniteRealCouplingData P Q) :
    P.HammingDualBound Q
      (C.expectedCost finiteProductHammingDistanceReal) := by
  intro f hLipschitz
  exact C.expectation_difference_abs_le_expectedCost
    finiteProductHammingDistanceReal f hLipschitz

/-- Pointwise domination of one bound by another preserves a finite Hamming
dual bound. -/
theorem HammingDualBound.mono
    {P Q : FiniteRealProbabilityData (ι → G)}
    {leftBound rightBound : ℝ}
    (hBound : P.HammingDualBound Q leftBound)
    (hLe : leftBound ≤ rightBound) :
    P.HammingDualBound Q rightBound := by
  intro f hLipschitz
  exact (hBound f hLipschitz).trans hLe

/-- Symmetry of the finite Hamming dual bound. -/
theorem HammingDualBound.symm
    {P Q : FiniteRealProbabilityData (ι → G)}
    {bound : ℝ}
    (hBound : P.HammingDualBound Q bound) :
    Q.HammingDualBound P bound := by
  intro f hLipschitz
  simpa [abs_sub_comm] using hBound f hLipschitz

end FiniteRealProbabilityData

end

end MathlibAnalytic
end MGAP4D
