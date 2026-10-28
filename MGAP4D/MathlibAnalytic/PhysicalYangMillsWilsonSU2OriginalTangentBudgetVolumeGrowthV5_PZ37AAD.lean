import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTangentExplicitVolumeRateV5_PZ37AAA
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGlobalActionBudgetWindowObstructionV5_PZ37AAB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAD — genuine Wilson global-tangent budget volume-growth obstruction

The true original SU(2) global Wilson action budget B_H is
>=4(H+1) by the proved AAB genuine plaquette-count injection.
AAA constructed the explicit actual physical-tangent ERROR UPPER
budget
  A_H = 2 B_H |d_H+kappa_H| + B_H ||W_H|| + 20 B_H².
The first two terms are nonnegative, so
  A_H >= 20 B_H² >= 320 (H+1)².
Thus the literal AAA proof budget A_H is UNBOUNDED across all
genuine finite periodic Wilson volumes. Its global-norm error proof
cannot simply be made volume-uniform by claiming a common A_H cap.

IMPORTANT authority boundary: this proves growth of a COARSE,
globally assembled valid upper BUDGET, NOT growth of the actual
tangent error, NOR failure of a sharper local/centered-source or
posterior-based estimate. It does not rule out all-volume physical
Rayleigh coercivity, endpoint E/F, H1-H4 or continuum YM mass gap.
No new axiom, sorry/admit/native_decide, or surrogate posterior.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAD_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAD_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAD_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAD_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAD_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- A_H is at least 20 times the squared LITERAL genuine global
one-slab Wilson action budget; it is an explicit upper estimate. -/
theorem p4Q2PZ37AAD_originalTangentErrorBudget_ge_twenty_actionBudget_sq
    (H : ℕ) :
    20 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)^2 ≤
      p4Q2PZ37AAA_originalPhysicalTangentRateBudget H := by
  let B : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let d := inner ℝ (p4Q2PZ37ZQ_originalPhysicalRawDerivative H) U
  let k := p4Q2JE_originalWilsonHaarZeroDerivativeConstant H
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hOne : 0 ≤ 2 * B * |d+k| := by positivity
  have hTwo : 0 ≤ B * ‖W‖ := by positivity
  change 20 * B^2 ≤ 2*B*|d+k| + B*‖W‖ + 20*B^2
  linarith

/-- The original physical Wilson tangent's explicit finite-H
GLOBAL upper rate certificate grows at least quadratically with
the periodic volume parameter. No actual-error lower bound is claimed. -/
theorem p4Q2PZ37AAD_originalTangentErrorBudget_ge_quadraticVolume
    (H : ℕ) :
    (320 : ℝ) * (((H+1 : ℕ) : ℝ))^2 ≤
      p4Q2PZ37AAA_originalPhysicalTangentRateBudget H := by
  let B : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hSide : 0 ≤ (4 : ℝ) * (((H+1 : ℕ) : ℝ)) := by positivity
  have hB : (4 : ℝ) * (((H+1 : ℕ) : ℝ)) ≤ B :=
    p4Q2PZ37AAB_originalGlobalActionBudget_ge_four_sideParameter H
  have hSq : ((4 : ℝ) * (((H+1 : ℕ) : ℝ)))^2 ≤ B^2 :=
    pow_le_pow_left₀ hSide hB 2
  calc
    (320 : ℝ) * (((H+1 : ℕ) : ℝ))^2 =
        20 * ((4 : ℝ) * (((H+1 : ℕ) : ℝ)))^2 := by ring
    _ ≤ 20 * B^2 :=
      mul_le_mul_of_nonneg_left hSq (by norm_num)
    _ ≤ p4Q2PZ37AAA_originalPhysicalTangentRateBudget H :=
      p4Q2PZ37AAD_originalTangentErrorBudget_ge_twenty_actionBudget_sq H

/-- For every numerical bound one finds a genuine Wilson finite
periodic volume whose original globally derived tangent-rate
UPPER CERTIFICATE exceeds it. -/
theorem p4Q2PZ37AAD_originalTangentErrorBudget_unbounded :
    ∀ K : ℝ, ∃ H : ℕ, K <
      p4Q2PZ37AAA_originalPhysicalTangentRateBudget H := by
  intro K
  obtain ⟨H, hH⟩ := exists_nat_gt K
  refine ⟨H, ?_⟩
  have hQuad :=
    p4Q2PZ37AAD_originalTangentErrorBudget_ge_quadraticVolume H
  have hCast : (((H+1 : ℕ) : ℝ)) = (H : ℝ) + 1 := by
    push_cast
    ring
  have hPos : 0 ≤ (H : ℝ) := Nat.cast_nonneg H
  have hSmall :
      (H : ℝ) ≤ (320 : ℝ) * (((H+1 : ℕ) : ℝ))^2 := by
    rw [hCast]
    nlinarith [sq_nonneg (H : ℝ)]
  exact lt_of_lt_of_le hH (hSmall.trans hQuad)

/-- No H-INDEPENDENT bound exists for the concrete AAA global
tangent-rate certificate. This says NOTHING about a potentially
sharper genuine local or centered physical Rayleigh estimate. -/
theorem p4Q2PZ37AAD_no_uniform_originalGlobalTangentRateBudget :
    ¬ ∃ K : ℝ, ∀ H : ℕ,
      p4Q2PZ37AAA_originalPhysicalTangentRateBudget H ≤ K := by
  rintro ⟨K, hAll⟩
  obtain ⟨H, hH⟩ :=
    p4Q2PZ37AAD_originalTangentErrorBudget_unbounded K
  exact (not_lt_of_ge (hAll H)) hH

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAD_originalTangentErrorBudget_ge_twenty_actionBudget_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAD_originalTangentErrorBudget_ge_quadraticVolume
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAD_originalTangentErrorBudget_unbounded
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAD_no_uniform_originalGlobalTangentRateBudget
