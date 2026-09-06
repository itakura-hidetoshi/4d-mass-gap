import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBoundedColorCoercivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 1000000

/-- The normalized bounded-color residual is invariant under translation by a
vector fixed by every color block.

This is the elementary quotient-space fact needed for a genuine Poincare
estimate: the residual sees only the class modulo the full common fixed space.
No orthogonal-projection choice is needed for this statement. -/
theorem boundedColorNormalizedResidualEnergy_add_of_mem_commonFixedSpace
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E)
    (x z : E)
    (hz : z ∈ boundedColorCommonFixedSpace P) :
    boundedColorNormalizedResidualEnergy P (x + z) =
      boundedColorNormalizedResidualEnergy P x := by
  change ∀ c : C, P c z = z at hz
  unfold boundedColorNormalizedResidualEnergy
  apply congrArg
    (fun s : ℝ => ((Fintype.card C : ℝ)⁻¹) * s)
  apply Finset.sum_congr rfl
  intro c _
  have hres : x + z - P c (x + z) = x - P c x := by
    rw [map_add, hz c]
    abel
  rw [hres]

/-- Subtracting a common-fixed vector likewise leaves the normalized residual
unchanged.  This is the centered form used by relative Poincare estimates. -/
theorem boundedColorNormalizedResidualEnergy_sub_of_mem_commonFixedSpace
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E)
    (x z : E)
    (hz : z ∈ boundedColorCommonFixedSpace P) :
    boundedColorNormalizedResidualEnergy P (x - z) =
      boundedColorNormalizedResidualEnergy P x := by
  change ∀ c : C, P c z = z at hz
  unfold boundedColorNormalizedResidualEnergy
  apply congrArg
    (fun s : ℝ => ((Fintype.card C : ℝ)⁻¹) * s)
  apply Finset.sum_congr rfl
  intro c _
  have hres : x - z - P c (x - z) = x - P c x := by
    rw [map_sub, hz c]
    abel
  rw [hres]

/-- Relative bounded-color coercivity.

Instead of asking the residual to control the full norm, choose for each vector
any representative `fixedPart x` in the common fixed space and control the
centered norm `‖x - fixedPart x‖`.  Translation invariance then transports the
centered residual back to the original residual before the model comparison is
applied.

This is the correct quotient-space version of the bounded-color reduction and
is independent of a particular orthogonal projection onto the common fixed
space. -/
theorem boundedColorRelativeCoercivity_sq_defect_lower_bound
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E)
    (κ η : ℝ)
    (hη0 : 0 ≤ η)
    (fixedPart : E → E)
    (hfixed : ∀ x : E, fixedPart x ∈ boundedColorCommonFixedSpace P)
    (defect : E → ℝ)
    (hframe : ∀ x : E,
      κ * ‖x - fixedPart x‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy P (x - fixedPart x))
    (hcompare : ∀ x : E,
      η * boundedColorNormalizedResidualEnergy P x ≤ defect x)
    (x : E) :
    (η * κ) * ‖x - fixedPart x‖ ^ 2 ≤ defect x := by
  have hscaled := mul_le_mul_of_nonneg_left (hframe x) hη0
  have hres :=
    boundedColorNormalizedResidualEnergy_sub_of_mem_commonFixedSpace
      P x (fixedPart x) (hfixed x)
  calc
    (η * κ) * ‖x - fixedPart x‖ ^ 2 =
        η * (κ * ‖x - fixedPart x‖ ^ 2) := by ring
    _ ≤ η * boundedColorNormalizedResidualEnergy P (x - fixedPart x) := hscaled
    _ = η * boundedColorNormalizedResidualEnergy P x := by rw [hres]
    _ ≤ defect x := hcompare x

/-- On any sector on which the chosen common-fixed part vanishes, relative
coercivity immediately becomes the ordinary full-norm defect estimate. -/
theorem boundedColorRelativeCoercivity_sq_defect_lower_bound_of_fixedPart_eq_zero
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E)
    (κ η : ℝ)
    (hη0 : 0 ≤ η)
    (fixedPart : E → E)
    (hfixed : ∀ x : E, fixedPart x ∈ boundedColorCommonFixedSpace P)
    (defect : E → ℝ)
    (hframe : ∀ x : E,
      κ * ‖x - fixedPart x‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy P (x - fixedPart x))
    (hcompare : ∀ x : E,
      η * boundedColorNormalizedResidualEnergy P x ≤ defect x)
    (x : E)
    (hx0 : fixedPart x = 0) :
    (η * κ) * ‖x‖ ^ 2 ≤ defect x := by
  simpa [hx0] using
    boundedColorRelativeCoercivity_sq_defect_lower_bound
      P κ η hη0 fixedPart hfixed defect hframe hcompare x

end

end MathlibAnalytic
end MGAP4D
