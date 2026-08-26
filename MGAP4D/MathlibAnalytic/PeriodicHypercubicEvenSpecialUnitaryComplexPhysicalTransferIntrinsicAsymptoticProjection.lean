import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferRieszAsymptoticProjection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set Filter Topology
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance periodicHypercubicEvenSpecialUnitaryComplexIntrinsicAsymptoticCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- The canonical Riesz circle lies strictly inside the exact excited-sector
spectral gap. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_lt_gap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
        H N hN beta hbeta <
      1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ := by
  have hq :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta
  dsimp [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius]
  linarith

/-- Positive powers of the genuine normalized complex Wilson transfer converge
in operator norm to the intrinsic full CFC top projection.  The contour radius
has disappeared from the conclusion. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_tendsto_cfcTopProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ^ (n + 1))
      atTop
      (𝓝
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta)) := by
  let r := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
    H N hN beta hbeta
  have hr : 0 < r := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_pos
        H N hN beta hbeta
  have hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_lt_gap
        H N hN beta hbeta
  have h :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_tendsto_rieszProjectorAtRadius
      H N hN beta hbeta r hr hrgap
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap] at h
  exact h

/-- The intrinsic CFC top projection is also the strong asymptotic projection
on every genuine complex physical vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_tendsto_cfcTopProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    Tendsto
      (fun n : ℕ =>
        ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ^ (n + 1)) f)
      atTop
      (𝓝
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta f)) := by
  let r := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
    H N hN beta hbeta
  have hr : 0 < r := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_pos
        H N hN beta hbeta
  have hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_lt_gap
        H N hN beta hbeta
  have h :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_tendsto_rieszProjectorAtRadius
      H N hN beta hbeta r hr hrgap f
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap] at h
  exact h

/-- Every complex Hilbert matrix element converges to the matrix element of the
intrinsic CFC top projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_tendsto_cfcTopProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    Tendsto
      (fun n : ℕ =>
        inner ℂ f
          (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1)) g))
      atTop
      (𝓝
        (inner ℂ f
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
            H N hN beta hbeta g))) := by
  let r := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
    H N hN beta hbeta
  have hr : 0 < r := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_pos
        H N hN beta hbeta
  have hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_lt_gap
        H N hN beta hbeta
  have h :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_tendsto_rieszProjectorAtRadius
      H N hN beta hbeta r hr hrgap f g
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjectorAtRadius_eq_cfcTopProjection
      H N hN beta hbeta r hr hrgap] at h
  exact h

/-- The CFC top projection is the unique operator-norm asymptotic projection of
positive normalized complex Wilson transfer powers. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_asymptoticProjection_unique
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (Q : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)
    (hQ :
      Tendsto
        (fun n : ℕ =>
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1))
        atTop (𝓝 Q)) :
    Q =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta := by
  exact tendsto_nhds_unique hQ
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_tendsto_cfcTopProjection
      H N hN beta hbeta)

/-- Even at the strong-operator level, a bounded operator receiving every
pointwise transfer-power limit must be the full CFC top projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_strongAsymptoticProjection_unique
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (Q : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)
    (hQ :
      ∀ f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
        Tendsto
          (fun n : ℕ =>
            ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) ^ (n + 1)) f)
          atTop (𝓝 (Q f))) :
    Q =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta := by
  apply ContinuousLinearMap.ext
  intro f
  exact tendsto_nhds_unique (hQ f)
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_tendsto_cfcTopProjection
      H N hN beta hbeta f)

/-- Audit-visible intrinsic asymptotic-projection package.  Its public limits
and uniqueness statements make no reference to a chosen contour radius. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferIntrinsicAsymptoticProjectionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  operatorNormLimit :
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ^ (n + 1))
      atTop
      (𝓝
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta))
  strongLimit :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      Tendsto
        (fun n : ℕ =>
          ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1)) f)
        atTop
        (𝓝
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
            H N hN beta hbeta f))
  matrixElementLimit :
    ∀ f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      Tendsto
        (fun n : ℕ =>
          inner ℂ f
            (((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) ^ (n + 1)) g))
        atTop
        (𝓝
          (inner ℂ f
            (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
              H N hN beta hbeta g)))
  operatorNormUnique :
    ∀ Q : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      Tendsto
        (fun n : ℕ =>
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1))
        atTop (𝓝 Q) →
      Q =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta
  strongUnique :
    ∀ Q : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      (∀ f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
        Tendsto
          (fun n : ℕ =>
            ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) ^ (n + 1)) f)
          atTop (𝓝 (Q f))) →
      Q =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta

/-- Construct the intrinsic asymptotic-projection package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferIntrinsicAsymptoticProjectionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferIntrinsicAsymptoticProjectionPackage
      H N hN beta hbeta :=
  { operatorNormLimit :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_tendsto_cfcTopProjection
        H N hN beta hbeta
    strongLimit :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_tendsto_cfcTopProjection
        H N hN beta hbeta
    matrixElementLimit :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_matrixElement_tendsto_cfcTopProjection
        H N hN beta hbeta
    operatorNormUnique :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_asymptoticProjection_unique
        H N hN beta hbeta
    strongUnique :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_strongAsymptoticProjection_unique
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
