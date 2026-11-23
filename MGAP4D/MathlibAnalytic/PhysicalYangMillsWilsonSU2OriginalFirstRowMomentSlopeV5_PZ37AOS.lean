import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstRowQuadraticBudgetV5_PZ37AOR
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOS — finite-volume original Wilson first-Haar-moment quadratic error

DIAGNOSTIC CANDIDATE ONLY. The unchanged original SU(2) Wilson one-slab
kernel, true normalized spatial Haar, and primary cyclic character enter
in the literal moment. AOR (canonical Formal, independently Lean/MCP
certified) bounds its -2-scaled response by (64+8*C_H)*beta².

This candidate algebraically divides that already certified factor of 2,
without discarding the finite-volume original global action budget C_H.
No H-uniform Taylor constant, fixed-positive-beta physical spectral gap,
continuum limit, or 4D Yang--Mills mass-gap theorem is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

/-- The exact original Wilson row's first Haar moment has slope coefficient
1/8 with a finite-volume H-dependent quadratic error. This is NOT an
independent H-uniform limit or a physical Hamiltonian spectral gap. -/
theorem p4Q2PZ37AOS_originalFirstRowHaarMoment_quadraticError_abs_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 8 * beta ≤ 1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |(∫ B,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta A B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) -
        beta / 8| ≤
      (32 + 4 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) *
        beta^2 := by
  let I : ℝ :=
    ∫ B,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
  let C : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hAOR :
      |(-2 : ℝ) * I + beta / 4| ≤ (64 + 8 * C) * beta^2 := by
    dsimp [I, C]
    exact p4Q2PZ37AOR_originalFirstRowResponse_quadraticGlobalBudget
      H beta hbeta hsmall A
  have hAlgebra : (-2 : ℝ) * I + beta / 4 =
      (-2 : ℝ) * (I - beta / 8) := by ring
  have hAbs :
      |(-2 : ℝ) * I + beta / 4| = 2 * |I - beta / 8| := by
    rw [hAlgebra, abs_mul]
    norm_num
  rw [hAbs] at hAOR
  have hCoeff :
      (64 + 8 * C) * beta^2 =
        2 * ((32 + 4 * C) * beta^2) := by ring
  rw [hCoeff] at hAOR
  have hDivided :
      |I - beta / 8| ≤ (32 + 4 * C) * beta^2 := by
    nlinarith only [hAOR]
  change |I - beta / 8| ≤ (32 + 4 * C) * beta^2
  exact hDivided

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOS_originalFirstRowHaarMoment_quadraticError_abs_le
