import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFrozenHalfDensityPairHaarL2
import Mathlib.Tactic

/-!
# Genuine half-density joint receiver: L2 resampling and frozen initial energy

PR #5261 identifies the ORIGINAL frozen joint receiver W*M_f with the
pair-Haar half-density transport of lambda^(-1) times the right-coordinate
pullback of the normalized physical one-slab transfer S f.

The original posterior resampling energy for any joint BCF is bounded by
twice the squared norm of the true joint-L2 class, as proved in PR #5260.
Combining these EXACT identities, without taking the supremum of W, gives

  E_e(W*M_f) <= 2 * (lambda^(-1) * ||S f||)^2
             <= 2 * (lambda^(-1) * ||f||)^2.

For a physical orbit factor of norm at most one, this becomes
  E_e(W*M_f) <= 2 * lambda^(-2).

This file substitutes the resulting bound into the ORIGINAL frozen
six-color initial energy (retaining 1/12 sum over actual spatial links)
and into each ORIGINAL left one-link residual (retaining its 1/2 factor).
The actual adjacent orbit uses beta(n+1) in its inputs and beta(n) in
the frozen transfer and true posterior/joint law.

The inverse top norm lambda^(-1) and the actual spatial-link count are
EXPLICIT and may depend on volume. No volume-uniform Yang--Mills gap,
new Dobrushin argument, transfer/orbit commutation, positive-depth
local support, or removal of the signed source/output drift is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3HalfDensityEnergyTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3HalfDensityEnergyCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3HalfDensityEnergySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3HalfDensityEnergyMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3HalfDensityEnergyBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3HalfDensityEnergySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3HalfDensityEnergyJointProbability
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

namespace GroundStatePosteriorJoint

/-- The original posterior resampling energy of the COMPLETE joint receiver,
including the real output half-density, is bounded by twice its exact
pair-Haar-transport norm squared.  This does not bound any supremum norm. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_le_two_transfer_image_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) ≤
      2 * (
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖⁻¹ *
        ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta f‖) ^ 2 := by
  have h :=
    posteriorResamplingEnergy_le_two_jointL2_norm_sq
      H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f)
  rw [
    normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_norm_eq_inv_transferNorm
      H N hN beta hbeta f
  ] at h
  exact h

/-- Physical-transfer contraction yields an input-norm estimate without
an inverse-vacuum supremum; only the true physical lambda remains. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_le_two_input_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) ≤
      2 * (
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖⁻¹ * ‖f‖) ^ 2 := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let a :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  have hEnergy :
      posteriorResamplingEnergy H N hN beta hbeta e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) ≤
        2 * (a * ‖S f‖) ^ 2 := by
    simpa [a, S] using
      (normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_le_two_transfer_image_sq
        H N hN beta hbeta f e)
  have hS : ‖S‖ = 1 := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
        H N hN beta hbeta
  have hf : ‖S f‖ ≤ ‖f‖ := by
    calc
      ‖S f‖ ≤ ‖S‖ * ‖f‖ := ContinuousLinearMap.le_opNorm S f
      _ = ‖f‖ := by rw [hS, one_mul]
  have ha : 0 ≤ a := by
    exact
      (inv_pos.mpr
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
          H N hN beta hbeta)).le
  have hMul : a * ‖S f‖ ≤ a * ‖f‖ :=
    mul_le_mul_of_nonneg_left hf ha
  have hSq : (a * ‖S f‖) ^ 2 ≤ (a * ‖f‖) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg ha (norm_nonneg _)) hMul 2
  have hBound :=
    hEnergy.trans (mul_le_mul_of_nonneg_left hSq (by norm_num : (0 : ℝ) ≤ 2))
  simpa [a, S] using hBound

/-- If the actual physical input is in the L2 unit ball, every individual
genuine joint right-link resampling energy is at most 2*lambda^(-2). -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_le_two_inv_norm_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hf : ‖f‖ ≤ 1)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) ≤
      2 *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ ^ 2 := by
  let a :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  have hEnergy :
      posteriorResamplingEnergy H N hN beta hbeta e
        (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) ≤
      2 * (a * ‖f‖) ^ 2 := by
    simpa [a] using
      (normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_le_two_input_sq
        H N hN beta hbeta f e)
  have ha : 0 ≤ a := by
    exact
      (inv_pos.mpr
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
          H N hN beta hbeta)).le
  have hMul : a * ‖f‖ ≤ a := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hf ha
  have hSq : (a * ‖f‖) ^ 2 ≤ a ^ 2 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (mul_nonneg ha (norm_nonneg _)) hMul 2)
  have hBound :=
    hEnergy.trans (mul_le_mul_of_nonneg_left hSq (by norm_num : (0 : ℝ) ≤ 2))
  simpa [a] using hBound

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    Hn 2 Pos (beta n) (hbeta n)
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "CommonRight" =>
  fineOrbitCommonRightBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "SeedRight" =>
  physicalYangMillsSU2AdjacentFineSeedRightBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Frozen" =>
  physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "PLeft" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
    Hn 2 Pos (beta n) (hbeta n)

/-- The exact mode-independent original common-right BCF has per-link
energy ≤ 2*lambda^(-2), with the full output half-density included. -/
theorem fineOrbitCommonRightResamplingEnergy_le_two_inv_transferNorm_sq
    (e : Link) :
    posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
        e (CommonRight n r) ≤ 2 * ‖T‖⁻¹ ^ 2 := by
  rw [fineOrbitCommonRightBCF_eq_jointReceiverProductBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r]
  exact normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_le_two_inv_norm_sq
    Hn 2 Pos (beta n) (hbeta n) (RightFactor n r)
    (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor_norm_le_one
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) e

/-- The exact mode-dependent swapped seed-right BCF has the same
half-density-inclusive resampling energy budget at each link. -/
theorem fineOrbitSeedRightResamplingEnergy_le_two_inv_transferNorm_sq
    (k : Fin 3) (e : Link) :
    posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
        e (SeedRight n r k) ≤ 2 * ‖T‖⁻¹ ^ 2 := by
  rw [physicalYangMillsSU2AdjacentFineSeedRightBCF_eq_jointReceiverProductBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r k]
  exact normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_le_two_inv_norm_sq
    Hn 2 Pos (beta n) (hbeta n) (LeftFactor n r k)
    (fineOrbitLeftFactor_norm_le_one
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k) e

/-- The ORIGINAL six-color initial residual remains a literal 1/12 sum
over the actual links and admits a single norm-based bound with no
supremum of the half-density W or of the posterior mean M. -/
theorem fineFrozenInitialEnergy_le_invNorm_sq_link_sum
    (k : Fin 3) :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
      (Frozen n r k) ≤
      (1 / 12 : ℝ) * ∑ _e : Link, 2 * ‖T‖⁻¹ ^ 2 := by
  have hOriginal :=
    fineFrozenInitialEnergy_le_commonRightResampling
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  have hSum :
      (∑ e : Link,
        posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
          e (CommonRight n r)) ≤
      ∑ _e : Link, 2 * ‖T‖⁻¹ ^ 2 := by
    apply Finset.sum_le_sum
    intro e _he
    exact fineOrbitCommonRightResamplingEnergy_le_two_inv_transferNorm_sq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e
  exact hOriginal.trans
    (mul_le_mul_of_nonneg_left hSum (by norm_num : (0 : ℝ) ≤ 1 / 12))

/-- The unavoidable actual spatial-link count is exposed explicitly:
the bound is NOT uniform in spatial volume. -/
theorem fineFrozenInitialEnergy_le_invNorm_sq_link_card
    (k : Fin 3) :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
      (Frozen n r k) ≤
      (1 / 6 : ℝ) * (Fintype.card Link : ℝ) * ‖T‖⁻¹ ^ 2 := by
  have h :=
    fineFrozenInitialEnergy_le_invNorm_sq_link_sum
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  calc
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (Frozen n r k) ≤
      (1 / 12 : ℝ) * (Fintype.card Link : ℝ) *
        (2 * ‖T‖⁻¹ ^ 2) := by
      simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_assoc] using h
    _ = (1 / 6 : ℝ) * (Fintype.card Link : ℝ) * ‖T‖⁻¹ ^ 2 := by ring

/-- Each ORIGINAL frozen left one-link residual is controlled by a single
inverse physical top-norm factor, using exact swap and true Dirichlet law. -/
theorem fineFrozenLeftSpatialLinkResidual_sq_le_inv_transferNorm_sq
    (k : Fin 3) (e : Link) :
    ‖Frozen n r k - PLeft e (Frozen n r k)‖ ^ 2 ≤ ‖T‖⁻¹ ^ 2 := by
  have hOriginal :=
    physicalYangMillsSU2AdjacentFineFrozenStep_leftSpatialLinkResidual_sq_le_half_seedRightResampling
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e
  have hEnergy :=
    fineOrbitSeedRightResamplingEnergy_le_two_inv_transferNorm_sq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e
  have hScaled :=
    mul_le_mul_of_nonneg_left hEnergy (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact hOriginal.trans (by nlinarith)

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
