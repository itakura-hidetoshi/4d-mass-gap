import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalRMSPhysicalBudgetV5_FI
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUnitReceiverStrictPositiveBeta
import Mathlib.Tactic

/-!
# P4-Q2-FJ: actual positive-beta SU(2) physical constant source has positive Wilson RMS mass

The genuine SU(2) ORIGINAL Wilson constant-unit receiver has
strictly positive full-link projection loss at beta > 0, proved by
the original Wilson kernel crossing witness (P4-Q2-J).
P4-Q2-FG/FH identify exactly the SAME original physical residual
energy with the outer pair-Haar integral of the INNER genuine
Wilson posterior-link conditional response RMS.

We connect the old strictly positive physical energy to FG/FH:
  beta > 0 -> 0 < sum_e mean_pairHaar_z M2_originalWilson(e,u,z).
Consequently an actual spatial link has strictly positive RMS mean.
This does NOT upgrade qualitative finite-volume positivity to a
per-link floor, spatial localization, uniform summability or C3 closure.
No independent Haar conditional kernel, new axiom or sorry.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

private noncomputable instance p4Q2FJ_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The original positive-beta SU(2) constant physical source has
strictly positive TOTAL Wilson conditional RMS link mass. It is the
literal FG/FH law, not an independent Haar posterior surrogate.
The per-link positivity is not inferred here. -/
theorem p4Q2FJ_originalWilsonUnitConditionalRMSFullMass_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    0 < p4Q2FH_originalWilsonSpatialRMSMass H 2
      (Nat.zero_lt_succ 1) beta (le_of_lt hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  let hN : 0 < (2 : ℕ) := Nat.zero_lt_succ 1
  let hBeta : 0 ≤ beta := le_of_lt hbeta
  let f := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 hN beta hBeta‖⁻¹
  let M : ℝ := p4Q2FH_originalWilsonSpatialRMSMass H 2 hN beta hBeta f
    (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  let E : ℝ := physicalOriginalUnitReceiverFullLinkEnergy H 2 hN beta hBeta
  have hL : 0 < L := inv_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 hN beta hBeta)
  have hE : 0 < E :=
    physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2 H beta hbeta
  have hDef : E =
      p4Q2FD_originalPhysicalRestrictedLinkEnergy H 2 hN beta hBeta f
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
    rfl
  have hBridge :=
    p4Q2FH_originalPhysicalPatchEnergy_eq_spatialRMSMass
      H 2 hN beta hBeta f
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  have hEq : E = (1 / 2 : ℝ) * L ^ 2 * M := by
    rw [hDef]
    exact hBridge
  have hCoeff : 0 < (1 / 2 : ℝ) * L ^ 2 :=
    mul_pos (by norm_num) (pow_pos hL 2)
  have hM : 0 < M := by
    by_contra hNot
    have hNonPos : M ≤ 0 := le_of_not_gt hNot
    have hMul : ((1 / 2 : ℝ) * L ^ 2) * M ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hCoeff.le hNonPos
    have : E ≤ 0 := by rw [hEq]; nlinarith [hMul]
    exact (not_le_of_gt hE) this
  exact hM

/-- No extra uniformity: strict positivity of the true full Wilson
RMS mass implies the existence of at least ONE actual spatial link
with positive pair-Haar mean of genuine conditional response. -/
theorem p4Q2FJ_exists_originalWilsonUnitConditionalRMSLinkMean_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      0 < p4Q2FH_originalWilsonConditionalRMSLinkMean
        H 2 (Nat.zero_lt_succ 1) beta (le_of_lt hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) e := by
  let f := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let M := p4Q2FH_originalWilsonConditionalRMSLinkMean
    H 2 (Nat.zero_lt_succ 1) beta (le_of_lt hbeta) f
  have hMass :
      0 < p4Q2FH_originalWilsonSpatialRMSMass
        H 2 (Nat.zero_lt_succ 1) beta (le_of_lt hbeta) f
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :=
    p4Q2FJ_originalWilsonUnitConditionalRMSFullMass_pos H beta hbeta
  by_contra hNo
  push Not at hNo
  have hSumNonpos :
      p4Q2FH_originalWilsonSpatialRMSMass
        H 2 (Nat.zero_lt_succ 1) beta (le_of_lt hbeta) f
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≤ 0 := by
    change (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, M e) ≤ 0
    calc
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, M e) ≤
          ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H, (0 : ℝ) := by
            apply Finset.sum_le_sum
            intro e _he
            exact hNo e
      _ = 0 := by simp
  exact (not_le_of_gt hMass) hSumNonpos

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FJ_originalWilsonUnitConditionalRMSFullMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FJ_exists_originalWilsonUnitConditionalRMSLinkMean_pos
