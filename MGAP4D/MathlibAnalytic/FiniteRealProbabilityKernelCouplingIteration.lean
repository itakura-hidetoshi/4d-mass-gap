import MGAP4D.MathlibAnalytic.FiniteRealProbabilityMixtureCouplingCost
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

/-- Push a finite real probability law through a finite probability kernel. -/
noncomputable def finiteRealProbabilityKernelPushforwardData
    {G : Type} [Fintype G]
    (law : FiniteRealProbabilityData G)
    (kernel : G → FiniteRealProbabilityData G) :
    FiniteRealProbabilityData G :=
  finiteRealProbabilityMixtureData law kernel

/-- Iterate a finite probability kernel on an initial finite law. -/
noncomputable def finiteRealProbabilityKernelIterateData
    {G : Type} [Fintype G]
    (kernel : G → FiniteRealProbabilityData G)
    (n : ℕ)
    (law : FiniteRealProbabilityData G) :
    FiniteRealProbabilityData G :=
  match n with
  | 0 => law
  | n + 1 =>
      finiteRealProbabilityKernelPushforwardData
        (finiteRealProbabilityKernelIterateData kernel n law) kernel

/-- Advance an exact finite coupling by coupling every pair of component
kernel rows and mixing with the current joint law. -/
noncomputable def finiteRealProbabilityKernelCouplingStepData
    {G : Type} [DecidableEq G] [Fintype G]
    {leftLaw rightLaw : FiniteRealProbabilityData G}
    (leftKernel rightKernel : G → FiniteRealProbabilityData G)
    (current : FiniteRealCouplingData leftLaw rightLaw)
    (rowCoupling : ∀ left right : G,
      FiniteRealCouplingData
        (leftKernel left) (rightKernel right)) :
    FiniteRealCouplingData
      (finiteRealProbabilityKernelPushforwardData leftLaw leftKernel)
      (finiteRealProbabilityKernelPushforwardData rightLaw rightKernel) :=
  finiteRealProbabilityMixtureCouplingData current rowCoupling

/-- Iterate a prescribed row coupling together with the two finite kernels. -/
noncomputable def finiteRealProbabilityKernelCouplingIterateData
    {G : Type} [DecidableEq G] [Fintype G]
    (leftKernel rightKernel : G → FiniteRealProbabilityData G)
    (rowCoupling : ∀ left right : G,
      FiniteRealCouplingData
        (leftKernel left) (rightKernel right))
    {leftLaw rightLaw : FiniteRealProbabilityData G}
    (initial : FiniteRealCouplingData leftLaw rightLaw)
    (n : ℕ) :
    FiniteRealCouplingData
      (finiteRealProbabilityKernelIterateData leftKernel n leftLaw)
      (finiteRealProbabilityKernelIterateData rightKernel n rightLaw) :=
  match n with
  | 0 => initial
  | n + 1 =>
      finiteRealProbabilityKernelCouplingStepData
        leftKernel rightKernel
        (finiteRealProbabilityKernelCouplingIterateData
          leftKernel rightKernel rowCoupling initial n)
        rowCoupling

/-- A uniform rowwise expected-cost contraction passes through one coupling
kernel step. -/
theorem finiteRealProbabilityKernelCouplingStepData_expectedCost_le_rate_mul
    {G : Type} [DecidableEq G] [Fintype G]
    {leftLaw rightLaw : FiniteRealProbabilityData G}
    (leftKernel rightKernel : G → FiniteRealProbabilityData G)
    (current : FiniteRealCouplingData leftLaw rightLaw)
    (rowCoupling : ∀ left right : G,
      FiniteRealCouplingData
        (leftKernel left) (rightKernel right))
    (cost : G → G → ℝ)
    (rate : ℝ)
    (hRow : ∀ left right : G,
      (rowCoupling left right).expectedCost cost ≤ rate * cost left right) :
    (finiteRealProbabilityKernelCouplingStepData
        leftKernel rightKernel current rowCoupling).expectedCost cost ≤
      rate * current.expectedCost cost := by
  calc
    (finiteRealProbabilityKernelCouplingStepData
        leftKernel rightKernel current rowCoupling).expectedCost cost ≤
      ∑ left : G, ∑ right : G,
        current.joint left right * (rate * cost left right) := by
      exact finiteRealProbabilityMixtureCoupling_expectedCost_le
        current rowCoupling cost (fun left right => rate * cost left right) hRow
    _ = rate * current.expectedCost cost := by
      unfold FiniteRealCouplingData.expectedCost
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro left _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro right _
      ring

/-- Iterating a nonnegative uniform rowwise contraction gives the exact
geometric expected-cost bound `rate ^ n`. -/
theorem finiteRealProbabilityKernelCouplingIterateData_expectedCost_le_pow_mul
    {G : Type} [DecidableEq G] [Fintype G]
    (leftKernel rightKernel : G → FiniteRealProbabilityData G)
    (rowCoupling : ∀ left right : G,
      FiniteRealCouplingData
        (leftKernel left) (rightKernel right))
    {leftLaw rightLaw : FiniteRealProbabilityData G}
    (initial : FiniteRealCouplingData leftLaw rightLaw)
    (cost : G → G → ℝ)
    (rate : ℝ)
    (hRate : 0 ≤ rate)
    (hRow : ∀ left right : G,
      (rowCoupling left right).expectedCost cost ≤ rate * cost left right)
    (n : ℕ) :
    (finiteRealProbabilityKernelCouplingIterateData
        leftKernel rightKernel rowCoupling initial n).expectedCost cost ≤
      rate ^ n * initial.expectedCost cost := by
  induction n with
  | zero =>
      simpa only [finiteRealProbabilityKernelCouplingIterateData, pow_zero, one_mul] using
        (le_refl (initial.expectedCost cost))
  | succ n ih =>
      calc
        (finiteRealProbabilityKernelCouplingIterateData
            leftKernel rightKernel rowCoupling initial (n + 1)).expectedCost cost ≤
          rate *
            (finiteRealProbabilityKernelCouplingIterateData
              leftKernel rightKernel rowCoupling initial n).expectedCost cost := by
            simpa only [finiteRealProbabilityKernelCouplingIterateData] using
              finiteRealProbabilityKernelCouplingStepData_expectedCost_le_rate_mul
                leftKernel rightKernel
                (finiteRealProbabilityKernelCouplingIterateData
                  leftKernel rightKernel rowCoupling initial n)
                rowCoupling cost rate hRow
        _ ≤ rate * (rate ^ n * initial.expectedCost cost) :=
          mul_le_mul_of_nonneg_left ih hRate
        _ = rate ^ (n + 1) * initial.expectedCost cost := by
          rw [pow_succ]
          ring

end
end MathlibAnalytic
end MGAP4D
