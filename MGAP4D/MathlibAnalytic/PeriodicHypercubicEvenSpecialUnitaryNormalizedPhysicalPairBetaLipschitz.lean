import MGAP4D.MathlibAnalytic.RealInverseSquarePerturbation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalizationFloor
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaLipschitz
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairBetaLipschitz
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TransferContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedBlockTransferRestriction
import Mathlib.Tactic

/-!
# Beta perturbation of the normalized physical pair transfer

The normalized pair transfer is

  S_beta = a_beta P_beta,

where

  a_beta = (||T_phys(beta)||^2)^(-1)

and P_beta is the raw ordered-pair one-slab transfer.

The previous finite-volume estimates provide:

* a_beta <= m_H(beta)^(-2) from the explicit Wilson minorization floor;
* ||T_phys(gamma)|| is beta-Lipschitz with coefficient B_H;
* P_beta is a contraction;
* ||P_gamma - P_beta|| <= 2 B_H ||gamma-beta||.

This file combines them without simplifying inverse-square arithmetic through
the large operator-valued definitions.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance normalizedPairBetaLipschitzTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance normalizedPairBetaLipschitzCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance normalizedPairBetaLipschitzSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance normalizedPairBetaLipschitzMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance normalizedPairBetaLipschitzBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance normalizedPairBetaLipschitzSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Explicit finite-volume Lipschitz coefficient for the normalized physical
pair transfer, using gamma for the first normalization factor in the standard
split S_gamma-S_beta = a_gamma(P_gamma-P_beta)+(a_gamma-a_beta)P_beta. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferBetaLipschitzConstant
    (H : ℕ) (beta gamma : ℝ) : ℝ :=
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let mGamma :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      H gamma
  let mBeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      H beta
  (mGamma ^ 2)⁻¹ * (2 * B) +
    (mGamma⁻¹ * mBeta⁻¹ * (mGamma⁻¹ + mBeta⁻¹)) * B

theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferBetaLipschitzConstant_nonneg
    (H : ℕ) (beta gamma : ℝ) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferBetaLipschitzConstant
        H beta gamma := by
  unfold
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferBetaLipschitzConstant
  have hB :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hGamma :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
      H gamma
  have hBeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
      H beta
  positivity

/-- The inverse-square normalization coefficient is beta-Lipschitz with a
fully explicit finite-volume coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferNormSqInv_norm_sub_le_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    ‖(‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN gamma hgamma‖ ^ 2)⁻¹ -
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2)⁻¹‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
            H gamma)⁻¹ *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
            H beta)⁻¹ *
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
              H gamma)⁻¹ +
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
              H beta)⁻¹) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  let tGamma : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN gamma hgamma‖
  let tBeta : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let mGamma : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      H gamma
  let mBeta : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      H beta
  let B : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let D : ℝ := ‖gamma - beta‖
  have htGamma : 0 < tGamma := by
    dsimp [tGamma]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN gamma hgamma
  have htBeta : 0 < tBeta := by
    dsimp [tBeta]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta
  have hmGamma : 0 < mGamma := by
    dsimp [mGamma]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
        H gamma
  have hmBeta : 0 < mBeta := by
    dsimp [mBeta]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
        H beta
  have hmGamma_le : mGamma ≤ tGamma := by
    dsimp [mGamma, tGamma]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_transferNorm
        H N hN gamma hgamma
  have hmBeta_le : mBeta ≤ tBeta := by
    dsimp [mBeta, tBeta]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_transferNorm
        H N hN beta hbeta
  have hScalar :
      ‖(tGamma ^ 2)⁻¹ - (tBeta ^ 2)⁻¹‖ ≤
        (mGamma⁻¹ * mBeta⁻¹ * (mGamma⁻¹ + mBeta⁻¹)) *
          ‖tGamma - tBeta‖ :=
    real_inv_sq_norm_sub_inv_sq_le_of_pos_lower_bounds
      tGamma tBeta mGamma mBeta
      htGamma htBeta hmGamma hmBeta hmGamma_le hmBeta_le
  have hNormVariation :
      ‖tGamma - tBeta‖ ≤ B * D := by
    dsimp [tGamma, tBeta, B, D]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_norm_sub_le_beta
        H N hN beta gamma hbeta hgamma
  have hCoeffNonneg :
      0 ≤ mGamma⁻¹ * mBeta⁻¹ * (mGamma⁻¹ + mBeta⁻¹) := by
    positivity
  change
    ‖(tGamma ^ 2)⁻¹ - (tBeta ^ 2)⁻¹‖ ≤
      (mGamma⁻¹ * mBeta⁻¹ * (mGamma⁻¹ + mBeta⁻¹)) * B * D
  calc
    ‖(tGamma ^ 2)⁻¹ - (tBeta ^ 2)⁻¹‖ ≤
        (mGamma⁻¹ * mBeta⁻¹ * (mGamma⁻¹ + mBeta⁻¹)) *
          ‖tGamma - tBeta‖ := hScalar
    _ ≤
        (mGamma⁻¹ * mBeta⁻¹ * (mGamma⁻¹ + mBeta⁻¹)) *
          (B * D) := by
      exact mul_le_mul_of_nonneg_left hNormVariation hCoeffNonneg
    _ =
        (mGamma⁻¹ * mBeta⁻¹ * (mGamma⁻¹ + mBeta⁻¹)) * B * D := by
      ring

/-- The actual normalized physical pair transfer is beta-Lipschitz in operator
norm with an explicit finite-volume coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_norm_sub_le_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferBetaLipschitzConstant
          H beta gamma *
        ‖gamma - beta‖ := by
  let tGamma : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN gamma hgamma‖
  let tBeta : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖
  let aGamma : ℝ := (tGamma ^ 2)⁻¹
  let aBeta : ℝ := (tBeta ^ 2)⁻¹
  let pGamma :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
      H N hN gamma hgamma
  let pBeta :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
      H N hN beta hbeta
  let mGamma : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      H gamma
  let mBeta : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      H beta
  let B : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let D : ℝ := ‖gamma - beta‖
  let cScalar : ℝ :=
    (mGamma⁻¹ * mBeta⁻¹ * (mGamma⁻¹ + mBeta⁻¹)) * B
  have hmGamma : 0 < mGamma := by
    dsimp [mGamma]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
        H gamma
  have hmBeta : 0 < mBeta := by
    dsimp [mBeta]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
        H beta
  have hB : 0 ≤ B := by
    dsimp [B]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hD : 0 ≤ D := norm_nonneg _
  have haGammaNonneg : 0 ≤ aGamma := by
    dsimp [aGamma]
    positivity
  have haGammaNorm : ‖aGamma‖ = aGamma := by
    rw [Real.norm_eq_abs, abs_of_nonneg haGammaNonneg]
  have haGammaFloor :
      aGamma ≤ (mGamma ^ 2)⁻¹ := by
    dsimp [aGamma, tGamma, mGamma]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferNorm_sq_inv_le_globalMinorizationFloor_sq_inv
        H N hN gamma hgamma
  have hFloorGammaSqInvNonneg : 0 ≤ (mGamma ^ 2)⁻¹ := by
    positivity
  have hPairDiff :
      ‖pGamma - pBeta‖ ≤ (2 * B) * D := by
    dsimp [pGamma, pBeta, B, D]
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_norm_sub_le
        H N hN beta gamma hbeta hgamma
  have hPairBeta :
      ‖pBeta‖ ≤ 1 := by
    dsimp [pBeta]
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_norm_le_one
        H N hN beta hbeta
  have hScalarDiff :
      ‖aGamma - aBeta‖ ≤ cScalar * D := by
    dsimp [aGamma, aBeta, tGamma, tBeta, cScalar, mGamma, mBeta, B, D]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferNormSqInv_norm_sub_le_beta
        H N hN beta gamma hbeta hgamma
  have hcScalarNonneg : 0 ≤ cScalar := by
    dsimp [cScalar]
    positivity
  have hSplit :
      aGamma • pGamma - aBeta • pBeta =
        aGamma • (pGamma - pBeta) +
          (aGamma - aBeta) • pBeta := by
    module
  change
    ‖aGamma • pGamma - aBeta • pBeta‖ ≤
      ((mGamma ^ 2)⁻¹ * (2 * B) + cScalar) * D
  rw [hSplit]
  calc
    ‖aGamma • (pGamma - pBeta) +
        (aGamma - aBeta) • pBeta‖ ≤
      ‖aGamma • (pGamma - pBeta)‖ +
        ‖(aGamma - aBeta) • pBeta‖ := norm_add_le _ _
    _ =
      ‖aGamma‖ * ‖pGamma - pBeta‖ +
        ‖aGamma - aBeta‖ * ‖pBeta‖ := by
      rw [norm_smul, norm_smul]
    _ =
      aGamma * ‖pGamma - pBeta‖ +
        ‖aGamma - aBeta‖ * ‖pBeta‖ := by
      rw [haGammaNorm]
    _ ≤
      (mGamma ^ 2)⁻¹ * ((2 * B) * D) +
        (cScalar * D) * 1 := by
      exact add_le_add
        (mul_le_mul haGammaFloor hPairDiff
          (norm_nonneg _) hFloorGammaSqInvNonneg)
        (mul_le_mul hScalarDiff hPairBeta
          (norm_nonneg _)
          (mul_nonneg hcScalarNonneg hD))
    _ =
      ((mGamma ^ 2)⁻¹ * (2 * B) + cScalar) * D := by
      ring

end

end MathlibAnalytic
end MGAP4D
