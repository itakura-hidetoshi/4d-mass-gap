import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaOrthogonalReceiverTransferDifference
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaLipschitz
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalizationFloor
import Mathlib.Tactic

/-!
# P4-Q2: explicit finite-volume quadratic-beta genuine receiver bound

PR #5310 controlled the ORIGINAL constant-orthogonal receiver through
the normalized physical operator difference S_beta - S_0, without a
quantitative beta rate. The already proved ORIGINAL physical one-slab
Wilson transfer is beta-Lipschitz in operator norm with the finite-volume
global action budget B_H. Its beta-zero action is exactly rank one.

On physical inputs f orthogonal to the canonical constant Haar vector,
T_0 f = 0, and the ORIGINAL half-density receiver retains TWO physical
inverse-transfer-normalization factors:

  ||V_beta f|| = ||T_beta||^(-2) ||(T_beta-T_0)f||
    <= m_H(beta)^(-2) B_H beta ||f||.

Here m_H(beta) is the previously proved positive, finite-volume original
Wilson global minorization floor. This is a concrete O_H(beta) receiver
bound, not a uniform-in-H estimate. Combining it with the genuine
posterior projection Pythagoras of #5310 gives

  A_beta(f) <= |SpatialLinks(H)| (m_H(beta)^(-2) B_H beta ||f||)^2.

The actual combined-orthogonal physical Gram Rayleigh inequality has
coefficient ONE, not two. No Dobrushin, substitute posterior, infinite-volume
constant, spacing-scaled generator or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4Q2ExplicitTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2ExplicitCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2ExplicitSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2ExplicitMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2ExplicitBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4Q2ExplicitLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Actual unnormalized beta-zero physical transfer annihilates every
constant-orthogonal physical vector, by the exact Wilson beta-zero
rank-one action, before either inverse normalization is introduced. -/
theorem physicalOriginalOneSlabTransfer_zero_of_constantOrthogonal
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN 0 (by norm_num) f = 0 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_apply
    H N hN f, horth]
  simp

/-- Physical beta-Lipschitz variation, restricted to an input killed
exactly by beta-zero transfer. The coefficient B_H is the ORIGINAL
Wilson one-slab action budget, and may scale with volume. -/
theorem physicalOriginalOneSlabTransfer_orthogonal_norm_le_actionBudget_beta
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta f‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta) * ‖f‖ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let T₀ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let B := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have h0 : T₀ f = 0 :=
    physicalOriginalOneSlabTransfer_zero_of_constantOrthogonal H N hN f horth
  have hLip : ‖T - T₀‖ ≤ B * beta := by
    simpa [T, T₀, B, Real.norm_eq_abs, abs_of_nonneg hbeta] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
        H N hN 0 beta (by norm_num) hbeta)
  have hDiff : (T - T₀) f = T f := by
    change T f - T₀ f = T f
    rw [h0, sub_zero]
  change ‖T f‖ ≤ (B * beta) * ‖f‖
  calc
    ‖T f‖ = ‖(T - T₀) f‖ := by rw [hDiff]
    _ ≤ ‖T - T₀‖ * ‖f‖ := (T - T₀).le_opNorm f
    _ ≤ (B * beta) * ‖f‖ :=
      mul_le_mul_of_nonneg_right hLip (norm_nonneg f)

/-- Exact norm formula for the ORIGINAL positive-beta pair-Haar
receiver in the constant-orthogonal sector. The two inverse physical
transfer factors are both mathematically necessary, because the
receiver definition already contains one extra inverse normalization. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_orthogonal_norm_eq_sqInv_rawDifference
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ ^ 2 *
        ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN 0 (by norm_num)) f‖ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let T₀ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let a : ℝ := ‖T‖⁻¹
  have ha : 0 ≤ a := inv_nonneg.mpr (norm_nonneg T)
  have h0 : T₀ f = 0 :=
    physicalOriginalOneSlabTransfer_zero_of_constantOrthogonal H N hN f horth
  have hDiff : (T - T₀) f = T f := by
    change T f - T₀ f = T f
    rw [h0, sub_zero]
  have hReceiver :=
    normalizedPhysicalOneSlabPairHaarReceiver_norm_eq_inv_transferNorm
      H N hN beta hbeta f
  change ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ =
    a ^ 2 * ‖(T - T₀) f‖
  calc
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ =
        a * ‖a • T f‖ := by
      simpa only [a, T,
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply]
        using hReceiver
    _ = a ^ 2 * ‖T f‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      ring
    _ = a ^ 2 * ‖(T - T₀) f‖ := by rw [hDiff]

/-- Explicit H-dependent, beta-linear coefficient for the TRUE
positive-beta receiver, with the canonical Wilson global floor. -/
noncomputable def physicalOriginalOrthogonalReceiverBetaLipschitzBudget
    (H : ℕ) (beta : ℝ) : ℝ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      H beta)⁻¹ ^ 2 *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      beta

theorem physicalOriginalOrthogonalReceiverBetaLipschitzBudget_nonneg
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 ≤ physicalOriginalOrthogonalReceiverBetaLipschitzBudget H beta := by
  unfold physicalOriginalOrthogonalReceiverBetaLipschitzBudget
  exact mul_nonneg
    (mul_nonneg (sq_nonneg _)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H))
    hbeta

@[simp] theorem physicalOriginalOrthogonalReceiverBetaLipschitzBudget_zero
    (H : ℕ) :
    physicalOriginalOrthogonalReceiverBetaLipschitzBudget H 0 = 0 := by
  simp [physicalOriginalOrthogonalReceiverBetaLipschitzBudget]

/-- Genuine P4-Q2 receiver bound, now a concrete O_H(beta) estimate
at beta=0 for the actual finite-volume SU(N) physical operator. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_orthogonal_norm_le_explicitBeta
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ ≤
      physicalOriginalOrthogonalReceiverBetaLipschitzBudget H beta * ‖f‖ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let T₀ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let a : ℝ := ‖T‖⁻¹
  let m : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta
  let B : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have ha : 0 ≤ a := inv_nonneg.mpr (norm_nonneg T)
  have hInv : a ≤ m⁻¹ := by
    simpa only [a, T, m] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferNorm_inv_le_globalMinorizationFloor_inv
        H N hN beta hbeta)
  have hInvSq : a ^ 2 ≤ m⁻¹ ^ 2 :=
    pow_le_pow_left₀ ha hInv 2
  have hRaw : ‖(T - T₀) f‖ ≤ (B * beta) * ‖f‖ := by
    have hLip : ‖T - T₀‖ ≤ B * beta := by
      simpa [T, T₀, B, Real.norm_eq_abs, abs_of_nonneg hbeta] using
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
          H N hN 0 beta (by norm_num) hbeta)
    exact ((T - T₀).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right hLip (norm_nonneg f))
  have hExact :
      ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ =
        a ^ 2 * ‖(T - T₀) f‖ := by
    simpa only [T, T₀, a] using
      (normalizedPhysicalOneSlabPairHaarReceiver_orthogonal_norm_eq_sqInv_rawDifference
        H N hN beta hbeta f horth)
  calc
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ =
        a ^ 2 * ‖(T - T₀) f‖ := hExact
    _ ≤ m⁻¹ ^ 2 * ‖(T - T₀) f‖ :=
      mul_le_mul_of_nonneg_right hInvSq (norm_nonneg _)
    _ ≤ m⁻¹ ^ 2 * ((B * beta) * ‖f‖) :=
      mul_le_mul_of_nonneg_left hRaw (sq_nonneg _)
    _ = physicalOriginalOrthogonalReceiverBetaLipschitzBudget H beta * ‖f‖ := by
      dsimp [physicalOriginalOrthogonalReceiverBetaLipschitzBudget, m, B]
      ring

/-- Unconditional genuine Wilson positive-beta posterior receiver
estimate with explicit beta^2 suppression at each finite H.
Its link count, global action budget and minorization floor are
visible; none is asserted to be uniformly bounded in H. -/
theorem physicalOrthogonalReceiverBetaZeroDriftFullLinkEnergy_le_explicitBetaSquared
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) f = 0) :
    physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta f ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      (physicalOriginalOrthogonalReceiverBetaLipschitzBudget H beta * ‖f‖) ^ 2 := by
  classical
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta
  let C := physicalOriginalOrthogonalReceiverBetaLipschitzBudget H beta
  have hv : ‖v‖ ≤ C * ‖f‖ :=
    normalizedPhysicalOneSlabPairHaarReceiver_orthogonal_norm_le_explicitBeta
      H N hN beta hbeta f horth
  have hsq : ‖v‖ ^ 2 ≤ (C * ‖f‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg v) hv 2
  have hsum : 0 ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖Q e v‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro e _he
    exact sq_nonneg _
  rw [physicalOrthogonalReceiverBetaZeroDriftFullLinkEnergy_eq_normLoss
    H N hN beta hbeta f horth]
  change (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      ‖v‖ ^ 2 - ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖Q e v‖ ^ 2 ≤
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      (C * ‖f‖) ^ 2
  calc
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        ‖v‖ ^ 2 - ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖Q e v‖ ^ 2 ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        ‖v‖ ^ 2 := by linarith
    _ ≤ (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          (C * ‖f‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)

/-- The original combined physical input, rather than individual
Gram basis vectors, controls the exact orthogonal Rayleigh form.
This upgrades the P4-Q2 structural theorem to a genuine beta-squared
finite-volume energy bound with coefficient one. -/
theorem pairHaarSpatialLinkResidualGram_orthogonal_rayleigh_le_explicitBetaSquared
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ)
    (horth : inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
      (∑ i : ι, a i • f i) = 0) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H N hN beta hbeta
          (fun i : ι => normalizedPhysicalOneSlabPairHaarReceiver
            H N hN beta hbeta (f i))) a) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (physicalOriginalOrthogonalReceiverBetaLipschitzBudget H beta *
          ‖∑ i : ι, a i • f i‖) ^ 2 := by
  classical
  calc
    star a ⬝ᵥ
        (Matrix.mulVec
          (pairHaarSpatialLinkResidualGram H N hN beta hbeta
            (fun i : ι => normalizedPhysicalOneSlabPairHaarReceiver
              H N hN beta hbeta (f i))) a) =
      physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy H N hN beta hbeta
        (∑ i : ι, a i • f i) :=
      pairHaarSpatialLinkResidualGram_physicalFamily_rayleigh_eq_receiverDrift_of_combinedOrthogonal
        H N hN beta hbeta f a horth
    _ ≤ _ :=
      physicalOrthogonalReceiverBetaZeroDriftFullLinkEnergy_le_explicitBetaSquared
        H N hN beta hbeta (∑ i : ι, a i • f i) horth

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
