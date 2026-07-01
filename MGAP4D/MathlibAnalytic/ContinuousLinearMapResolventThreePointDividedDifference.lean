import MGAP4D.MathlibAnalytic.ContinuousLinearMapResolventDividedDifference
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The nested three-point divided difference of three bounded operator values. -/
def threePointDividedDifference
    (Rlambda Rmu Rnu : E →L[ℝ] E)
    (lambda mu nu : ℝ) :
    E →L[ℝ] E :=
  (lambda - mu)⁻¹ •
    ((lambda - nu)⁻¹ • (Rlambda - Rnu) -
      (mu - nu)⁻¹ • (Rmu - Rnu))

@[simp] theorem threePointDividedDifference_apply
    (Rlambda Rmu Rnu : E →L[ℝ] E)
    (lambda mu nu : ℝ)
    (x : E) :
    threePointDividedDifference Rlambda Rmu Rnu lambda mu nu x =
      (lambda - mu)⁻¹ •
        ((lambda - nu)⁻¹ • (Rlambda x - Rnu x) -
          (mu - nu)⁻¹ • (Rmu x - Rnu x)) := rfl

/-- Three pairwise-distinct resolvent values compose to their nested
three-point divided difference. -/
theorem comp_comp_eq_threePointDividedDifference_of_resolvent_identities
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
      threePointDividedDifference Rlambda Rmu Rnu lambda mu nu := by
  apply ContinuousLinearMap.ext
  intro x
  rw [threePointDividedDifference_apply]
  calc
    Rlambda (Rmu (Rnu x)) =
        (lambda - mu)⁻¹ •
          (Rlambda (Rnu x) - Rmu (Rnu x)) :=
      comp_apply_eq_inv_smul_sub_apply_of_resolvent_identity_of_ne
        Rlambda Rmu lambda mu hlambdaMu hLambdaMu (Rnu x)
    _ = (lambda - mu)⁻¹ •
        ((lambda - nu)⁻¹ • (Rlambda x - Rnu x) -
          (mu - nu)⁻¹ • (Rmu x - Rnu x)) := by
      rw [
        comp_apply_eq_inv_smul_sub_apply_of_resolvent_identity_of_ne
          Rlambda Rnu lambda nu hlambdaNu hLambdaNu x,
        comp_apply_eq_inv_smul_sub_apply_of_resolvent_identity_of_ne
          Rmu Rnu mu nu hmuNu hMuNu x]

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
