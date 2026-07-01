import MGAP4D.MathlibAnalytic.ContinuousLinearMapResolventThreePointDividedDifference
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The symmetric Lagrange-coefficient expansion associated with three real
parameters and three bounded operator values. -/
def threePointLagrangeCombination
    (Rlambda Rmu Rnu : E →L[ℝ] E)
    (lambda mu nu : ℝ) :
    E →L[ℝ] E :=
  ((lambda - mu)⁻¹ * (lambda - nu)⁻¹) • Rlambda +
    ((mu - lambda)⁻¹ * (mu - nu)⁻¹) • Rmu +
      ((nu - lambda)⁻¹ * (nu - mu)⁻¹) • Rnu

@[simp] theorem threePointLagrangeCombination_apply
    (Rlambda Rmu Rnu : E →L[ℝ] E)
    (lambda mu nu : ℝ)
    (x : E) :
    threePointLagrangeCombination Rlambda Rmu Rnu lambda mu nu x =
      ((lambda - mu)⁻¹ * (lambda - nu)⁻¹) • Rlambda x +
        ((mu - lambda)⁻¹ * (mu - nu)⁻¹) • Rmu x +
          ((nu - lambda)⁻¹ * (nu - mu)⁻¹) • Rnu x := rfl

/-- For three pairwise-distinct parameters, the nested divided difference is
the symmetric Lagrange linear combination of the three operator values. -/
theorem threePointDividedDifference_eq_threePointLagrangeCombination
    (Rlambda Rmu Rnu : E →L[ℝ] E)
    (lambda mu nu : ℝ)
    (hlambdaMu : lambda ≠ mu)
    (hlambdaNu : lambda ≠ nu)
    (hmuNu : mu ≠ nu) :
    threePointDividedDifference Rlambda Rmu Rnu lambda mu nu =
      threePointLagrangeCombination Rlambda Rmu Rnu lambda mu nu := by
  have hMuCoeff :
      -((lambda - mu)⁻¹ * (mu - nu)⁻¹) =
        (mu - lambda)⁻¹ * (mu - nu)⁻¹ := by
    rw [show mu - lambda = -(lambda - mu) by ring, inv_neg]
    ring
  have hNuCoeff :
      (lambda - mu)⁻¹ *
          ((mu - nu)⁻¹ - (lambda - nu)⁻¹) =
        (nu - lambda)⁻¹ * (nu - mu)⁻¹ := by
    field_simp [
      sub_ne_zero.mpr hlambdaMu,
      sub_ne_zero.mpr hlambdaNu,
      sub_ne_zero.mpr hmuNu,
      sub_ne_zero.mpr hlambdaNu.symm,
      sub_ne_zero.mpr hmuNu.symm]
    <;> ring
  have hExpand :
      threePointDividedDifference Rlambda Rmu Rnu lambda mu nu =
        ((lambda - mu)⁻¹ * (lambda - nu)⁻¹) • Rlambda +
          (-((lambda - mu)⁻¹ * (mu - nu)⁻¹)) • Rmu +
            ((lambda - mu)⁻¹ *
              ((mu - nu)⁻¹ - (lambda - nu)⁻¹)) • Rnu := by
    unfold threePointDividedDifference
    module
  rw [hMuCoeff, hNuCoeff] at hExpand
  exact hExpand

/-- A triple product satisfying the three resolvent identities has the explicit
three-point Lagrange partial-fraction expansion. -/
theorem comp_comp_eq_threePointLagrangeCombination_of_resolvent_identities
    (Rlambda Rmu Rnu : E →L[ℝ] E)
    (lambda mu nu : ℝ)
    (hlambdaMu : lambda ≠ mu)
    (hlambdaNu : lambda ≠ nu)
    (hmuNu : mu ≠ nu)
    (hLambdaMu :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda.comp Rmu))
    (hLambdaNu :
      Rlambda - Rnu =
        (lambda - nu) • (Rlambda.comp Rnu))
    (hMuNu :
      Rmu - Rnu =
        (mu - nu) • (Rmu.comp Rnu)) :
    Rlambda.comp (Rmu.comp Rnu) =
      threePointLagrangeCombination Rlambda Rmu Rnu lambda mu nu := by
  calc
    Rlambda.comp (Rmu.comp Rnu) =
        threePointDividedDifference Rlambda Rmu Rnu lambda mu nu :=
      comp_comp_eq_threePointDividedDifference_of_resolvent_identities
        Rlambda Rmu Rnu lambda mu nu
        hlambdaMu hlambdaNu hmuNu hLambdaMu hLambdaNu hMuNu
    _ = threePointLagrangeCombination Rlambda Rmu Rnu lambda mu nu :=
      threePointDividedDifference_eq_threePointLagrangeCombination
        Rlambda Rmu Rnu lambda mu nu hlambdaMu hlambdaNu hmuNu

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
