import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRowLocalLinearResponseV5_PZ37AOM
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRowMassDeficitBoundV5_PZ37AOO
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOP — Original row response with real Wilson row-mass deficit

Diagnostic candidate only. Exact finite-volume SU(2) Wilson one-slab kernel,
normalized original Haar measure, primary character, fixed left boundary, and
single-link center twist are unchanged.

AOM controls the interacting beta-dependent row response relative to the genuine
flipped-kernel action-gap coefficient. AOO bounds the difference of that
coefficient from -1/4 by the original Wilson row-mass deficit. Their algebraic
combination provides a beta-relative first Haar moment estimate.

This theorem does NOT prove a volume-uniform o(beta) rate for row mass deficit,
a uniform positive-coupling coefficient, a normalized physical top-state slope,
a Hamiltonian spectral gap, or the continuum 4D Yang--Mills mass gap.
No candidate-to-canonical promotion until direct Lean, real Lean MCP,
independent exact-head CI, and postmerge push CI all succeed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

/-- Original interacting SU(2) Wilson first Haar row moment has an absolute
error relative to beta/4, controlled by the true original row-mass deficit.
The right-hand term has no asserted H-uniform vanishing rate. -/
theorem p4Q2PZ37AOP_originalRowResponse_abs_error_le_rowMassDeficit
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 8 * beta ≤ 1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |(-2 : ℝ) *
      (∫ B,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 beta A B *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) +
      beta / 4| ≤
        64 * beta^2 +
          8 * beta *
            (1 - (∫ B,
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H 2 beta A B
              ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))) := by
  let I : ℝ :=
    ∫ B,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
  let D : ℝ :=
    ∫ B,
      p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
        (p4Q2PZ37ANV_singleLinkCenterTwist H
          (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B) *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
  let Z : ℝ :=
    ∫ B,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
  have hResponse : |(-2 : ℝ) * I - beta * D| ≤ 64 * beta^2 := by
    dsimp [I, D]
    exact p4Q2PZ37AOM_originalFixedLeftRowLocalLinearResponse_abs_le
      H beta hbeta hsmall A
  have hDeficit : |D + (1 / 4 : ℝ)| ≤ 8 * (1 - Z) := by
    dsimp [D, Z]
    exact p4Q2PZ37AOO_originalWilsonCoefficient_sub_zero_abs_le_rowMassDeficit
      H beta hbeta A
  have hScale : |beta * (D + (1 / 4 : ℝ))| ≤ beta * (8 * (1 - Z)) := by
    rw [abs_mul, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left hDeficit hbeta
  have hBound :
      |((-2 : ℝ) * I - beta * D) + beta * (D + (1 / 4 : ℝ))| ≤
        64 * beta^2 + 8 * beta * (1 - Z) := by
    calc
      _ ≤ |(-2 : ℝ) * I - beta * D| + |beta * (D + (1 / 4 : ℝ))| :=
        abs_add_le _ _
      _ ≤ 64 * beta^2 + beta * (8 * (1 - Z)) :=
        add_le_add hResponse hScale
      _ = 64 * beta^2 + 8 * beta * (1 - Z) := by ring
  have hAlgebra :
      ((-2 : ℝ) * I - beta * D) + beta * (D + (1 / 4 : ℝ)) =
        (-2 : ℝ) * I + beta / 4 := by ring
  rw [hAlgebra] at hBound
  change |(-2 : ℝ) * I + beta / 4| ≤ 64 * beta^2 + 8 * beta * (1 - Z)
  exact hBound

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOP_originalRowResponse_abs_error_le_rowMassDeficit
