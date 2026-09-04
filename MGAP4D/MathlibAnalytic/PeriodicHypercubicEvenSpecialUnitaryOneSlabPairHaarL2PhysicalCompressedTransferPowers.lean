import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2PhysicalCompressedTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

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

/-- Power action of a real scalar multiple of a generic normalized-transfer
orthogonal restriction.  The proof is pointwise, so it never asks for a
scalar-tower structure on the operator algebra itself. -/
private theorem realHilbertTopEigenspaceOrthogonalRestriction_smul_pow_apply
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (c : ℝ)
    (k : ℕ)
    (f : (realHilbertTopEigenspace S)ᗮ) :
    ((c • realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ k) f =
      c ^ k •
        ((realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ k) f := by
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  change ((c • R) ^ k) f = c ^ k • (R ^ k) f
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      change
        ((c • R) ^ k) ((c • R) f) =
          (c ^ k * c) • (R ^ k) (R f)
      rw [ih]
      change
        c ^ k • (R ^ k) (c • R f) =
          (c ^ k * c) • (R ^ k) (R f)
      rw [map_smul, smul_smul]

/-- Operator equality corresponding to the preceding pointwise power formula.
It is derived by extensionality rather than `smul_pow`, deliberately avoiding
an operator-space scalar-tower requirement. -/
private theorem realHilbertTopEigenspaceOrthogonalRestriction_smul_pow
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (c : ℝ)
    (k : ℕ) :
    (c • realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ k =
      c ^ k • (realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ k := by
  apply ContinuousLinearMap.ext
  intro f
  exact realHilbertTopEigenspaceOrthogonalRestriction_smul_pow_apply S hS c k f

/-- Generic pointwise geometric bound for powers of a nonnegative real scalar
multiple of a normalized-transfer orthogonal restriction.  Scalar norm
homogeneity is used only on vectors, never on the operator space itself. -/
private theorem realHilbertTopEigenspaceOrthogonalRestriction_smul_pow_apply_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (c : ℝ)
    (hc : 0 ≤ c)
    (k : ℕ)
    (f : (realHilbertTopEigenspace S)ᗮ) :
    ‖((c • realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ k) f‖ ≤
      c ^ k * ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ ^ k * ‖f‖ := by
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  change ‖((c • R) ^ k) f‖ ≤ c ^ k * ‖R‖ ^ k * ‖f‖
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      change
        ‖((c • R) ^ k) ((c • R) f)‖ ≤
          c ^ Nat.succ k * ‖R‖ ^ Nat.succ k * ‖f‖
      calc
        ‖((c • R) ^ k) ((c • R) f)‖ ≤
            c ^ k * ‖R‖ ^ k * ‖(c • R) f‖ := ih ((c • R) f)
        _ = c ^ k * ‖R‖ ^ k * (c * ‖R f‖) := by
          change
            c ^ k * ‖R‖ ^ k * ‖c • R f‖ =
              c ^ k * ‖R‖ ^ k * (c * ‖R f‖)
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
        _ ≤ c ^ k * ‖R‖ ^ k * (c * (‖R‖ * ‖f‖)) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm R f) hc
          · exact mul_nonneg (pow_nonneg hc k) (pow_nonneg (norm_nonneg R) k)
        _ = c ^ Nat.succ k * ‖R‖ ^ Nat.succ k * ‖f‖ := by
          rw [pow_succ, pow_succ]
          ring

/-- Generic operator-norm consequence of the preceding pointwise bound.  This
avoids requiring a `NormSMulClass` instance on the continuous-linear-map
algebra. -/
private theorem realHilbertTopEigenspaceOrthogonalRestriction_smul_pow_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (c : ℝ)
    (hc : 0 ≤ c)
    (k : ℕ) :
    ‖(c • realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ k‖ ≤
      c ^ k * ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ ^ k := by
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  change ‖(c • R) ^ k‖ ≤ c ^ k * ‖R‖ ^ k
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (pow_nonneg hc k) (pow_nonneg (norm_nonneg R) k)
  · intro f
    exact
      realHilbertTopEigenspaceOrthogonalRestriction_smul_pow_apply_norm_le
        S hS c hc k f

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
  simpa only [
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace] using
    (realHilbertTopEigenspaceOrthogonalRestriction_smul_pow
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H N hN beta hbeta)
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ^ 2)
      k)

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
  have h := congrArg
    (fun A => A f)
    (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_pow
      H N hN beta hbeta k)
  exact h

/-- The norm of the `k`th compressed power is bounded by the exact raw
pair-vacuum normalization power times the `k`th power of the normalized
physical excitation norm.  The zero-power case retains the general `‖id‖ ≤ 1`
bound, so no nontriviality assumption on the excitation space is introduced. -/
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
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let hS :
      (S :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsSymmetric := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H N hN beta hbeta
  change
    ‖(c • realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ k‖ ≤
      c ^ k * ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ ^ k
  exact
    realHilbertTopEigenspaceOrthogonalRestriction_smul_pow_norm_le
      S hS c (sq_nonneg _) k

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
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let hS :
      (S :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsSymmetric := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H N hN beta hbeta
  change
    ‖((c • realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ k) f‖ ≤
      c ^ k * ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ ^ k * ‖f‖
  exact
    realHilbertTopEigenspaceOrthogonalRestriction_smul_pow_apply_norm_le
      S hS c (sq_nonneg _) k f

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
  have hpos :
      0 <
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ ^ 2) ^ k :=
    pow_pos
      (pow_pos
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
          H N hN beta hbeta) 2) k
  refine (div_le_iff₀ hpos).2 ?_
  simpa only [mul_comm] using
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
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa only [q] using
      (norm_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta))
  · simpa only [q] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta)
  · intro k
    simpa only [q] using
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_relative_pow_norm_le
        H N hN beta hbeta k)

end

end MathlibAnalytic
end MGAP4D
