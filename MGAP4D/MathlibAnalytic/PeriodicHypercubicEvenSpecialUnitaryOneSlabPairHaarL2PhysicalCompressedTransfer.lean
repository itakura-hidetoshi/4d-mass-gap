import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2PhysicalIntertwining
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

/-- The bounded excitation-space operator represented by the literal raw
ordered-pair transfer on the one-sided physical embedding `J f = f ⊠ Ω_top`.

Its pointwise formula retains the exact raw pair-vacuum normalization
`‖T_phys‖²`.  The literal compression property is proved below by equality of
all matrix coefficients; no invariance of the ambient one-sided range is
assumed. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2
  let L :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta :=
    c • (R :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta)
  exact LinearMap.mkContinuous
    (𝕜 := ℝ)
    (𝕜₂ := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (σ := RingHom.id ℝ)
    L
    (c * ‖R‖)
    (by
      intro x
      change ‖c • R x‖ ≤ (c * ‖R‖) * ‖x‖
      have hc : 0 ≤ c := by
        dsimp [c]
        exact sq_nonneg _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      calc
        c * ‖R x‖ ≤ c * (‖R‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm R x) hc
        _ = (c * ‖R‖) * ‖x‖ := by ring)

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
  rfl

/-- Exact compression characterization: every matrix coefficient of the
excitation-space operator is the corresponding matrix coefficient of the
literal raw pair transfer between one-sided physical excitation vectors. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_inner_eq_pairTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta f) u =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
            H N hN beta hbeta f))
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
          H N hN beta hbeta u) := by
  rw [periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_apply]
  rw [real_inner_smul_left]
  symm
  simpa using
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_oneSidedExcitation_matrixCoefficient_eq_sq_physicalNorm_mul
      H N hN beta hbeta f u

/-- The represented compression is unique: any bounded excitation-space
operator with the literal pair-transfer matrix coefficients equals the operator
constructed above. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_unique
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta)
    (hA : ∀ f u :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
      inner ℝ (A f) u =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
              H N hN beta hbeta f))
          (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
            H N hN beta hbeta u)) :
    A =
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
        H N hN beta hbeta := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro u
  calc
    inner ℝ (A f) u =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
              H N hN beta hbeta f))
          (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
            H N hN beta hbeta u) := hA f u
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
          H N hN beta hbeta f) u :=
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_inner_eq_pairTransfer
        H N hN beta hbeta f u).symm

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
  let C :=
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator
      H N hN beta hbeta
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ ^ 2
  change ‖C‖ = c * ‖R‖
  have hc : 0 ≤ c := by
    dsimp [c]
    exact sq_nonneg _
  have hcpos : 0 < c := by
    dsimp [c]
    exact pow_pos
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta) 2
  have hCapply : ∀ x, C x = c • R x := by
    intro x
    simpa [C, R, c] using
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationCompressedPairTransferOperator_apply
        H N hN beta hbeta x
  have hupper : ‖C‖ ≤ c * ‖R‖ := by
    apply ContinuousLinearMap.opNorm_le_bound C (mul_nonneg hc (norm_nonneg R))
    intro x
    rw [hCapply x, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      c * ‖R x‖ ≤ c * (‖R‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm R x) hc
      _ = (c * ‖R‖) * ‖x‖ := by ring
  have hpoint : ∀ x, R x = c⁻¹ • C x := by
    intro x
    rw [hCapply x, smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
  have hRle : ‖R‖ ≤ c⁻¹ * ‖C‖ := by
    apply ContinuousLinearMap.opNorm_le_bound R
      (mul_nonneg (inv_nonneg.mpr hc) (norm_nonneg C))
    intro x
    rw [hpoint x, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
    calc
      c⁻¹ * ‖C x‖ ≤ c⁻¹ * (‖C‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.le_opNorm C x) (inv_nonneg.mpr hc)
      _ = (c⁻¹ * ‖C‖) * ‖x‖ := by ring
  have hlower : c * ‖R‖ ≤ ‖C‖ := by
    calc
      c * ‖R‖ ≤ c * (c⁻¹ * ‖C‖) :=
        mul_le_mul_of_nonneg_left hRle hc
      _ = ‖C‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  exact le_antisymm hupper hlower

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
