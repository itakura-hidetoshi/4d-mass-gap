import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventIdentity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A resolvent identity at two distinct real parameters expresses the product
of the two bounded resolvents as the divided difference of the resolvent map. -/
theorem comp_eq_inv_smul_sub_of_resolvent_identity_of_ne
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (hne : lambda ≠ mu)
    (hIdentity :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda.comp Rmu)) :
    Rlambda.comp Rmu =
      (lambda - mu)⁻¹ • (Rlambda - Rmu) := by
  rw [hIdentity, smul_smul]
  rw [inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]

/-- Pointwise form of the two-point resolvent divided-difference formula. -/
theorem comp_apply_eq_inv_smul_sub_apply_of_resolvent_identity_of_ne
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (hne : lambda ≠ mu)
    (hIdentity :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda.comp Rmu))
    (x : E) :
    Rlambda (Rmu x) =
      (lambda - mu)⁻¹ • (Rlambda x - Rmu x) := by
  have hOperator :=
    comp_eq_inv_smul_sub_of_resolvent_identity_of_ne
      Rlambda Rmu lambda mu hne hIdentity
  calc
    Rlambda (Rmu x) = (Rlambda.comp Rmu) x := rfl
    _ = ((lambda - mu)⁻¹ • (Rlambda - Rmu)) x := by
      rw [hOperator]
    _ = (lambda - mu)⁻¹ • (Rlambda x - Rmu x) := rfl

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
