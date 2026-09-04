import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2PhysicalCompressedTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance pairPhysicalCompressedPowersTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairPhysicalCompressedPowersCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairPhysicalCompressedPowersSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairPhysicalCompressedPowersMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairPhysicalCompressedPowersBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance pairPhysicalCompressedPowersSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pairPhysicalCompressedPowersSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Exact algebraic power factorization of the represented one-sided physical
compression.  This is a theorem about powers of the excitation-space operator
`C` itself; it does not identify these powers with ambient literal pair-transfer
powers and assumes no invariance of the one-sided ambient range. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_pow
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ) :
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta ^ k =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k •
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ k := by
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  change (c • R) ^ k = c ^ k • R ^ k
  rw [smul_pow]

/-- Pointwise form of the exact compressed power factorization. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_pow_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta ^ k) f =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k •
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta) ^ k) f := by
  rw [periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_pow]
  rfl

/-- The norm of the `k`th compressed power is bounded by the exact raw
pair-vacuum normalization power times the `k`th power of the normalized
physical excitation norm.  The `k = 0` case uses the general `‖id‖ ≤ 1`
operator-norm bound, so no nontriviality assumption on the excitation space is
introduced. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_pow_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta ^ k‖ ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ k := by
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  change
    ‖(c • R) ^ k‖ ≤ c ^ k * ‖R‖ ^ k
  cases k with
  | zero =>
      change ‖ContinuousLinearMap.id ℝ _‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
  | succ k =>
      rw [smul_pow, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (sq_nonneg _) (Nat.succ k))]
      exact
        mul_le_mul_of_nonneg_left
          (norm_pow_le' R (Nat.succ_pos k))
          (pow_nonneg (sq_nonneg _) (Nat.succ k))

/-- Vector-level finite-volume geometric bound for powers of the represented
compressed excitation dynamics. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_pow_apply_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖(periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta ^ k) f‖ ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2) ^ k *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ k * ‖f‖ := by
  calc
    ‖(periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta ^ k) f‖ ≤
        ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta ^ k‖ * ‖f‖ :=
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
        H N hN beta hbeta ^ k).le_opNorm f
    _ ≤
        ((‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ ^ 2) ^ k *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖ ^ k) * ‖f‖ :=
      mul_le_mul_of_nonneg_right
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_pow_norm_le
          H N hN beta hbeta k)
        (norm_nonneg f)

/-- Vacuum-normalized relative power bound.  The denominator is strictly
positive because the raw physical one-slab transfer has positive norm. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_relative_pow_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta ^ k‖ /
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ ^ 2) ^ k ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ k := by
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2
  have hc : 0 < c :=
    pow_pos
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta) 2
  have hck : 0 < c ^ k := pow_pos hc k
  apply (div_le_iff₀ hck).2
  simpa [c, mul_comm] using
    (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_pow_norm_le
      H N hN beta hbeta k)

/-- Finite-volume relative exponential-decay package for the represented
one-sided compressed dynamics.  The witness is the normalized physical
excitation contraction ratio `q = ‖R‖`, which is strictly below one at this
fixed finite volume.  This theorem does not assert scale-uniform decay,
continuum decay, ambient one-sided range invariance, or a Yang--Mills mass gap. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_finiteVolumeRelativeExponentialDecay
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∃ q : ℝ,
      0 ≤ q ∧
      q < 1 ∧
      ∀ k : ℕ,
        ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
              H N hN beta hbeta ^ k‖ /
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                H N hN beta hbeta‖ ^ 2) ^ k ≤
          q ^ k := by
  let q : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  refine ⟨q, norm_nonneg _, ?_, ?_⟩
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  · intro k
    simpa [q] using
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_relative_pow_norm_le
        H N hN beta hbeta k)

end

end MathlibAnalytic
end MGAP4D
