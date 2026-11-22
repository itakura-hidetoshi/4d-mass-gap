import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstHaarExplicitPositiveBetaV5_PZ37ANX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANY — exact original finite-volume positive coupling interval

ANX constructs a positive original-Wilson coupling for every finite H.
ANY proves the same genuine physical top/first Gauss-law overlap is strictly
negative for EVERY positive coupling within the explicit interval,
not merely at ANX's single selected coupling.

The finite-volume physical Hilbert, full original one-slab Wilson action,
its spatial halfweights and temporal crossings, Haar measure and first
physical Gram–Schmidt mode are unchanged.
No uniform-in-H coupling interval, OS reconstruction or continuum
four-dimensional Yang–Mills mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Explicit H-dependent positive-coupling radius for the actual Wilson
physical top/first-mode signed overlap. -/
noncomputable def p4Q2PZ37ANY_originalPhysicalFirstModeBetaRadius (H : ℕ) : ℝ :=
  1 / (1024 *
    (1 + periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)^2)

/-- This actual-model coupling radius is strictly positive at every finite H. -/
theorem p4Q2PZ37ANY_originalPhysicalFirstModeBetaRadius_pos (H : ℕ) :
    0 < p4Q2PZ37ANY_originalPhysicalFirstModeBetaRadius H := by
  have hC :
      0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
    positivity
  have hd :
      0 < (1 : ℝ) +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
    linarith
  unfold p4Q2PZ37ANY_originalPhysicalFirstModeBetaRadius
  positivity

/-- On the WHOLE H-dependent positive coupling interval, the actual SU(2)
physical Wilson top mode has strictly negative first Gauss-law overlap.
This only strengthens the local finite-volume statement ANX. -/
theorem p4Q2PZ37ANY_originalPhysicalTopFirstOverlap_neg_on_beta_interval
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (hupper : beta ≤ p4Q2PZ37ANY_originalPhysicalFirstModeBetaRadius H) :
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) beta hbeta.le)
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) < 0 := by
  let C : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let d : ℝ := 1 + C
  have hC : 0 ≤ C := by
    dsimp [C, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget]
    positivity
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hdenom : 0 < 1024 * d^2 := by positivity
  have hbetaUpper : beta ≤ 1 / (1024 * d^2) := by
    simpa only [p4Q2PZ37ANY_originalPhysicalFirstModeBetaRadius, d, C]
      using hupper
  have hCd : C ≤ d^2 := by
    dsimp [d]
    nlinarith [sq_nonneg C]
  have hC2d : C^2 ≤ d^2 := by
    dsimp [d]
    nlinarith
  have hCdiv : C / (1024 * d^2) ≤ (1 / 64 : ℝ) :=
    (div_le_iff₀ hdenom).2 (by nlinarith [hCd, sq_nonneg d])
  have hC2div : C^2 / (1024 * d^2) ≤ (1 / 256 : ℝ) :=
    (div_le_iff₀ hdenom).2 (by nlinarith [hC2d, sq_nonneg d])
  have hlinear :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ (1 / 64 : ℝ) := by
    change C * beta ≤ (1 / 64 : ℝ)
    calc
      C * beta ≤ C * (1 / (1024 * d^2)) :=
        mul_le_mul_of_nonneg_left hbetaUpper hC
      _ = C / (1024 * d^2) := by ring
      _ ≤ (1 / 64 : ℝ) := hCdiv
  have hquadratic :
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)^2 *
        beta ≤ (1 / 256 : ℝ) := by
    change C^2 * beta ≤ (1 / 256 : ℝ)
    calc
      C^2 * beta ≤ C^2 * (1 / (1024 * d^2)) :=
        mul_le_mul_of_nonneg_left hbetaUpper (sq_nonneg C)
      _ = C^2 / (1024 * d^2) := by ring
      _ ≤ (1 / 256 : ℝ) := hC2div
  exact p4Q2PZ37ANX_originalPhysicalTopFirstOverlap_neg_of_explicit_bounds
    H beta hbeta hlinear hquadratic

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANY_originalPhysicalFirstModeBetaRadius_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANY_originalPhysicalTopFirstOverlap_neg_on_beta_interval
