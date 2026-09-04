import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2PhysicalIntertwining
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

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

@[reducible] local instance pairPhysicalCompressedTransferOrthogonalNormedSpace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
  Submodule.normedSpace
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

local instance pairPhysicalCompressedTransferOrthogonalCompleteSpace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta).isClosed_orthogonal.completeSpace_coe

/-- Compression of the literal raw ordered-pair transfer to the concrete
one-sided physical excitation embedding `J f = f ⊠ Ω_top`.

This is deliberately a compression `J† T_pair J`, not an assertion that the
whole one-sided range is invariant under the ambient pair operator. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta := by
  let J :=
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
      H N hN beta hbeta
  let Tpair :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
      H N hN beta hbeta
  exact
    (J.toContinuousLinearMap†).comp
      (Tpair.comp J.toContinuousLinearMap)

/- Exact operator-level upgrade of the matrix-coefficient intertwining seam.
The raw pair compression carries the square of the raw physical top
normalization and nothing is silently normalized away. -/
set_option maxHeartbeats 800000 in
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_eq_sq_physicalNorm_smul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
        H N hN beta hbeta =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta := by
  let J :=
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
      H N hN beta hbeta
  let Tpair :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
      H N hN beta hbeta
  let Tphys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  ext f
  exact ext_inner_right ℝ fun u => by
    calc
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
            H N hN beta hbeta f) u =
        inner ℝ (Tpair (J f)) (J u) := by
          change inner ℝ ((J.toContinuousLinearMap†) (Tpair (J f))) u = _
          exact ContinuousLinearMap.adjoint_inner_left
            J.toContinuousLinearMap u (Tpair (J f))
      _ = ‖Tphys‖ ^ 2 * inner ℝ (R f) u := by
        simpa [J, Tpair, Tphys, R] using
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_oneSidedExcitation_matrixCoefficient_eq_sq_physicalNorm_mul
            H N hN beta hbeta f u
      _ = inner ℝ ((‖Tphys‖ ^ 2 • R) f) u := by
        change
          ‖Tphys‖ ^ 2 * inner ℝ (R f) u =
            inner ℝ (‖Tphys‖ ^ 2 • R f) u
        exact (real_inner_smul_left (R f) u (‖Tphys‖ ^ 2)).symm

/-- The compressed raw norm factors exactly into the raw vacuum normalization
squared times the already-normalized physical excitation norm. -/
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
  rw [periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_eq_sq_physicalNorm_smul]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

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
  have hTpos :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  have hsq :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ^ 2 :=
    pow_pos hTpos 2
  have hprod :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ ^ 2 *
        (1 -
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta‖) :=
    mul_pos hsq (sub_pos.mpr hR)
  nlinarith

end

end MathlibAnalytic
end MGAP4D
