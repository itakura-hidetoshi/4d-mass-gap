import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

namespace ComplexStrictlyPositiveOperator

universe u

variable {H : Type u}
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The canonical logarithmic Hamiltonian associated with a strictly positive
complex transfer operator. -/
noncomputable def logHamiltonian
    (T : H →L[ℂ] H) : H →L[ℂ] H :=
  -CFC.log T

/-- Bundled positivity together with invertibility gives strict positivity. -/
theorem isStrictlyPositive_of_isPositive_isUnit
    (T : H →L[ℂ] H)
    (hpositive : T.IsPositive)
    (hunit : IsUnit T) :
    IsStrictlyPositive T :=
  hunit.isStrictlyPositive
    ((ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive)

/-- A logarithmic Hamiltonian is self-adjoint. -/
theorem logHamiltonian_isSelfAdjoint
    (T : H →L[ℂ] H) :
    IsSelfAdjoint (logHamiltonian T) := by
  unfold logHamiltonian
  exact IsSelfAdjoint.log.neg

/-- Exponentiating the negative logarithmic Hamiltonian reconstructs the
original strictly positive transfer operator. -/
theorem exp_neg_logHamiltonian
    (T : H →L[ℂ] H)
    (hstrict : IsStrictlyPositive T) :
    NormedSpace.exp (-logHamiltonian T) = T := by
  unfold logHamiltonian
  simp only [neg_neg]
  exact CFC.exp_log T hstrict

/-- An exponential scalar upper bound on a strictly positive transfer operator
becomes the matching lower bound on its logarithmic Hamiltonian. -/
theorem algebraMap_le_logHamiltonian_of_le_exp_neg_algebraMap
    (T : H →L[ℂ] H)
    (δ : ℝ)
    (hstrict : IsStrictlyPositive T)
    (hle : T ≤ algebraMap ℝ (H →L[ℂ] H) (Real.exp (-δ))) :
    algebraMap ℝ (H →L[ℂ] H) δ ≤ logHamiltonian T := by
  have hlog := CFC.log_le_log hle hstrict
  have hscalar :
      CFC.log (algebraMap ℝ (H →L[ℂ] H) (Real.exp (-δ))) =
        algebraMap ℝ (H →L[ℂ] H) (-δ) := by
    rw [CFC.log_algebraMap, Real.log_exp]
  rw [hscalar] at hlog
  unfold logHamiltonian
  have hneg := neg_le_neg hlog
  simpa using hneg

/-- A positive scalar lower bound makes the logarithmic Hamiltonian
nonnegative. -/
theorem logHamiltonian_nonneg_of_pos_lower_bound
    (T : H →L[ℂ] H)
    (δ : ℝ)
    (hδ : 0 < δ)
    (hlower : algebraMap ℝ (H →L[ℂ] H) δ ≤ logHamiltonian T) :
    0 ≤ logHamiltonian T := by
  exact
    (isStrictlyPositive_algebraMap
      (A := H →L[ℂ] H) hδ).nonneg.trans hlower

end ComplexStrictlyPositiveOperator

end

end MathlibAnalytic
end MGAP4D
