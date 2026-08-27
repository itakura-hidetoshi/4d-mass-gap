import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedOperatorRealization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A nonzero real eigenvector of a continuous linear endomorphism can only
carry an eigenvalue whose norm is bounded by the operator norm.  Keeping this
lemma outside the dependent physical carriers avoids forcing elaboration of
the full finite-volume geometry during the elementary norm cancellation. -/
theorem continuousLinearMap_real_eigenvalue_norm_le_opNorm
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (T : E →L[ℝ] E)
    {u : E}
    {lambda : ℝ}
    (hu : u ≠ 0)
    (hEigen : T u = lambda • u) :
    ‖lambda‖ ≤ ContinuousLinearMap.opNorm T := by
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hOp : ‖T u‖ ≤ ContinuousLinearMap.opNorm T * ‖u‖ := T.le_opNorm u
  rw [hEigen, norm_smul] at hOp
  exact (mul_le_mul_right huNorm).mp hOp

/-- Every real eigenvalue carried by a nonzero completed excitation state after
`n > 0` Euclidean slabs lies inside the doubled finite-volume exponential
contraction radius.  This is an eigenvalue statement on the completed
pair-Hilbert carrier itself, so it does not require closedness or invertibility
of the subsequent Hilbert--Schmidt realization in bounded-operator norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_real_eigenvalue_norm_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    {lambda : ℝ}
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta)
    (hu : u ≠ 0)
    (hEigen :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n u = lambda • u) :
    ‖lambda‖ ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) := by
  calc
    ‖lambda‖ ≤
        ContinuousLinearMap.opNorm
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n) :=
      continuousLinearMap_real_eigenvalue_norm_le_opNorm
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n)
        hu hEigen
    _ ≤ Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_le_exp_of_pos
        H N hN beta hbeta n hn

/-- Equivalently, a real scalar strictly outside the doubled finite-volume
exponential disk cannot have a nonzero eigenvector in the completed excitation
sector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_no_real_eigenvector_above_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    {lambda : ℝ}
    (hlambda :
      Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) < ‖lambda‖)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta)
    (hEigen :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n u = lambda • u) :
    u = 0 := by
  by_contra hu
  have hBound :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_real_eigenvalue_norm_le_exp_of_pos
      H N hN beta hbeta n hn u hu hEigen
  exact (not_lt_of_ge hBound) hlambda

/-- One-slab specialization of the completed-sector real-eigenvalue exclusion. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_real_eigenvalue_norm_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    {lambda : ℝ}
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta)
    (hu : u ≠ 0)
    (hEigen :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1 u = lambda • u) :
    ‖lambda‖ ≤
      Real.exp
        (-2 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) := by
  simpa using
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_real_eigenvalue_norm_le_exp_of_pos
      H N hN beta hbeta 1 (by decide) u hu hEigen

end

end MathlibAnalytic
end MGAP4D
