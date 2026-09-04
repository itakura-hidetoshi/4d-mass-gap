import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2PhysicalIntertwining
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance pairPhysicalCompressedTransferTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairPhysicalCompressedTransferCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairPhysicalCompressedTransferSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairPhysicalCompressedTransferMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairPhysicalCompressedTransferBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance pairPhysicalCompressedTransferSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pairPhysicalCompressedTransferSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Use the normed-space structure canonically induced by the already-present
inner-product structure on the physical top-eigenspace orthogonal subtype. -/
local instance pairPhysicalCompressedTransferOrthogonalNormedSpace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
  InnerProductSpace.toNormedSpace

/-- Exact real-scalar homogeneity of the operator norm, derived directly from
`ContinuousLinearMap.opNorm_smul_le`.  We keep this local instead of requiring
a `NormSMulClass` instance on the whole continuous-linear-map space. -/
private theorem realContinuousLinearMap_norm_smul
    {E F : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (c : ℝ)
    (A : E →L[ℝ] F) :
    ‖c • A‖ = |c| * ‖A‖ := by
  apply le_antisymm
  · simpa [Real.norm_eq_abs] using
      (ContinuousLinearMap.opNorm_smul_le c A)
  · by_cases hc : c = 0
    · simp [hc]
    · have hInv :=
        ContinuousLinearMap.opNorm_smul_le c⁻¹ (c • A)
      have hrecover : c⁻¹ • (c • A) = A := by
        ext x
        simp [smul_smul, hc]
      rw [hrecover] at hInv
      have hcabs : 0 < |c| := abs_pos.mpr hc
      have hInv' : ‖A‖ ≤ ‖c • A‖ / |c| := by
        simpa [Real.norm_eq_abs, abs_inv, div_eq_mul_inv, mul_comm] using hInv
      have hmul : ‖A‖ * |c| ≤ ‖c • A‖ :=
        (le_div_iff₀ hcabs).mp hInv'
      simpa [mul_comm] using hmul

/-- The bounded excitation-space operator represented by the literal raw
ordered-pair transfer on the one-sided physical embedding `J f = f ⊠ Ω_top`.

Its pointwise formula retains the exact raw pair-vacuum normalization
`‖T_phys‖²`.  The literal compression property is proved below by equality of
all physical ambient matrix coefficients; no invariance of the ambient
one-sided range is assumed. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta := by
  let R :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2
  exact
    (c • R :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta)

@[simp]
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
        H N hN beta hbeta f =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta f := by
  simp [periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator]

/-- Exact compression characterization: every physical ambient matrix
coefficient of the excitation-space operator is the corresponding coefficient
of the literal raw pair transfer between one-sided physical excitation vectors. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_inner_eq_pairTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
            H N hN beta hbeta f :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H N hN beta hbeta) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
        (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
            H N hN beta hbeta f))
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
          H N hN beta hbeta u) := by
  rw [periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_apply]
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  have hmatrix :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_oneSidedExcitation_matrixCoefficient_eq_sq_physicalNorm_mul
      H N hN beta hbeta f u
  change
    inner ℝ
        (c •
          (((R f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              H N hN beta hbeta) :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)))
        (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) = _
  calc
    inner ℝ
        (c •
          (((R f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              H N hN beta hbeta) :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)))
        (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
      c *
        inner ℝ
          (((R f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              H N hN beta hbeta) :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
          (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
        exact real_inner_smul_left
          (((R f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              H N hN beta hbeta) :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
          (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
          c
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
            H N hN beta hbeta f))
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
          H N hN beta hbeta u) := by
        simpa [c, R] using hmatrix.symm

/-- The represented raw compression norm factors exactly into the raw
pair-vacuum normalization squared and the normalized physical excitation norm. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_norm_eq_sq_physicalNorm_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ := by
  let R :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2
  change
    ‖(c • R :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta)‖ = c * ‖R‖
  rw [realContinuousLinearMap_norm_smul]
  rw [abs_of_nonneg]
  dsimp [c]
  exact sq_nonneg _

/-- Strict finite-volume contraction of the literal raw pair compression,
measured relative to the exact raw pair-vacuum normalization `‖T_phys‖²`.
This is not a scale-uniform or continuum statement. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_norm_lt_sq_physicalNorm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
        H N hN beta hbeta‖ <
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 := by
  rw [periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_norm_eq_sq_physicalNorm_mul]
  have hR :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta
  have hc :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ^ 2 :=
    pow_pos
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta) 2
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ <
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 * 1 :=
        mul_lt_mul_of_pos_left hR hc
    _ = ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 := by ring

end

end MathlibAnalytic
end MGAP4D
