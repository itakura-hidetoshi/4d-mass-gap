import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioTwoStepRemoteTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance fixedRightTargetRatioTwoStepRemoteColumnSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Sum of the exact two-step represented-source transport over every target
other than the distinguished source.  This is deliberately larger than the
later geometric remote set, so any bound proved here is safe for the genuinely
remote column as well. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ target ∈ (Finset.univ.erase source),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target)
      2 (Sum.inr source)

/-- The complete non-source two-step represented-right transport column is
bounded independently of the periodic volume.  The two random-scan factors
cancel the possible target count, leaving only the physical diagonal
cross-boundary coefficient times the off-fiber coefficient and the singleton
`exp (16 * beta)` magnitude. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum
        H beta hbeta source ≤
      2 * (((Real.exp (8 * beta)) ^ 2 - 1) /
        ((Real.exp (8 * beta)) ^ 2 + 1)) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta * Real.exp (16 * beta)) := by
  classical
  let M : ℝ := Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let q : ℝ :=
    2 * (((Real.exp (8 * beta)) ^ 2 - 1) /
      ((Real.exp (8 * beta)) ^ 2 + 1))
  let r : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
      beta
  let E : ℝ := Real.exp (16 * beta)
  let C : ℝ := q * (r * E)
  have hMNat : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    periodicHypercubicEvenSpatialSliceLink_card_pos_for_stationaryFiniteStepResponse H
  have hMpos : 0 < M := by
    dsimp [M]
    exact_mod_cast hMNat
  have hMone : 1 ≤ M := by
    dsimp [M]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hMNat))
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hInvNonneg : 0 ≤ M⁻¹ := inv_nonneg.mpr hMpos.le
  have hInvLeOne : M⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hMpos).2 hMone
  have hExp8 : 1 ≤ Real.exp (8 * beta) := by
    apply Real.one_le_exp
    nlinarith
  have hSq : 1 ≤ (Real.exp (8 * beta)) ^ 2 := by
    nlinarith [Real.exp_pos (8 * beta)]
  have hQNonneg : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (by norm_num)
      (div_nonneg (sub_nonneg.mpr hSq) (by positivity))
  have hRNonneg : 0 ≤ r := by
    dsimp [r]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_nonneg
        beta hbeta
  have hENonneg : 0 ≤ E := by
    dsimp [E]
    exact (Real.exp_pos _).le
  have hCNonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hQNonneg (mul_nonneg hRNonneg hENonneg)
  have hCardNat :
      (Finset.univ.erase source).card ≤
        Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
    simpa using Finset.card_le_univ (Finset.univ.erase source)
  have hCard : ((Finset.univ.erase source).card : ℝ) ≤ M := by
    dsimp [M]
    exact_mod_cast hCardNat
  have hSumEq :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum
          H beta hbeta source =
        ((Finset.univ.erase source).card : ℝ) *
          (M⁻¹ * (q * (M⁻¹ * (r * E)))) := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum
    calc
      (∑ target ∈ (Finset.univ.erase source),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
            H beta target)
          2 (Sum.inr source)) =
          ∑ _target ∈ (Finset.univ.erase source),
            (M⁻¹ * (q * (M⁻¹ * (r * E)))) := by
        apply Finset.sum_congr rfl
        intro target hTarget
        have hne : target ≠ source := Finset.ne_of_mem_erase hTarget
        simpa [M, q, r, E] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightSource_eq
            H beta hbeta hne
      _ = ((Finset.univ.erase source).card : ℝ) *
          (M⁻¹ * (q * (M⁻¹ * (r * E)))) := by
        simp
  rw [hSumEq]
  have hInnerNonneg : 0 ≤ M⁻¹ * (q * (M⁻¹ * (r * E))) := by
    exact mul_nonneg hInvNonneg
      (mul_nonneg hQNonneg (mul_nonneg hInvNonneg (mul_nonneg hRNonneg hENonneg)))
  calc
    ((Finset.univ.erase source).card : ℝ) *
        (M⁻¹ * (q * (M⁻¹ * (r * E)))) ≤
      M * (M⁻¹ * (q * (M⁻¹ * (r * E)))) :=
        mul_le_mul_of_nonneg_right hCard hInnerNonneg
    _ = M⁻¹ * C := by
      dsimp [C]
      rw [← mul_assoc M M⁻¹, mul_inv_cancel₀ hMne, one_mul]
      ring
    _ ≤ C := by
      simpa using mul_le_mul_of_nonneg_right hInvLeOne hCNonneg
    _ =
      2 * (((Real.exp (8 * beta)) ^ 2 - 1) /
        ((Real.exp (8 * beta)) ^ 2 + 1)) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta * Real.exp (16 * beta)) := by
      rfl

end

end MathlibAnalytic
end MGAP4D
