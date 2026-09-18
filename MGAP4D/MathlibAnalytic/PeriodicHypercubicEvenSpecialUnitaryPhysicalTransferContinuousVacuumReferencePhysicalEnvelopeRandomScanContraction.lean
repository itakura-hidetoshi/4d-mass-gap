import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalResidualMaximumColumn
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceRestrictedRandomScanLocalResidualSweep
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalEnvelopeRandomScanSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Concrete finite-volume column coefficient for the physical SU(N) envelope
kernel.  The local part is volume-independent; the remote maximum is still the
exact finite-volume coefficient from the preceding theorem unit. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta +
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualMaximumColumn
      H N hN beta hbeta A

/-- The concrete finite-volume envelope column coefficient is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
        H N hN beta hbeta A := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
        beta hbeta))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualMaximumColumn_nonneg
      H N hN beta hbeta A)

/-- Every source column of the physical SU(N) envelope kernel is bounded by the
concrete finite-volume coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_columnSum_le_coefficient
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelColumnSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A)
        source ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
        H N hN beta hbeta A := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_columnSum_le_eighteen_mul_add_remoteMaximum
      H N hN beta hbeta A source

/-- The explicit sparse/local gate is exactly strictness of the concrete
finite-volume envelope column coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient_lt_one_of_gate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hGate :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualMaximumColumn
          H N hN beta hbeta A < 1) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
      H N hN beta hbeta A < 1 := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient] using
    hGate

/-- Under the concrete finite-volume sparse/local gate, the reciprocal
random-scan rate of the actual-law envelope kernel is strictly below one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_reciprocalRandomScanRate_lt_one_of_gate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hGate :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
        H N hN beta hbeta A < 1) :
    finiteInfluenceKernelReciprocalRandomScanRate
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
          H N hN beta hbeta A) < 1 := by
  exact finiteInfluenceKernelReciprocalRandomScanRate_lt_one
    (periodicHypercubicEvenSpatialSliceLink_card_pos H)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
      H N hN beta hbeta A)
    hGate

/-- Finite-step reciprocal random-scan contraction for the actual physical
SU(N) influence envelope kernel, conditional on the finite-volume gate.

The initial variation profile is arbitrary except for nonnegativity and a
uniform scalar bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_randomScanIterate_le_rate_pow_mul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ) (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (n : ℕ) (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A)
        variation n source ≤
      finiteInfluenceKernelReciprocalRandomScanRate
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
            H N hN beta hbeta A) ^ n * bound := by
  exact finiteInfluenceKernelRandomScanVariationIterate_le_rate_pow_mul
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A)
    (periodicHypercubicEvenSpatialSliceLink_card_pos H)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
      H N hN beta hbeta A)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient_nonneg
      H N hN beta hbeta A)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_columnSum_le_coefficient
      H N hN beta hbeta A)
    variation hVariationNonneg bound hBoundNonneg hVariationBound n source

/-- One full physical-link sweep has an exponential envelope whenever the
finite-volume sparse/local coefficient is strictly below one.

This is a finite-volume sweep theorem.  The exponent contains the exact
finite-volume remote maximum and is not asserted to be uniform in H. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_fullSweepIterate_le_exp
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ) (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (hGate :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
        H N hN beta hbeta A < 1)
    (sweeps : ℕ) (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A)
        variation
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
        source ≤
      Real.exp
          (-(1 -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
                H N hN beta hbeta A) * (sweeps : ℝ)) *
        bound := by
  have hIter :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_randomScanIterate_le_rate_pow_mul
      H N hN beta hbeta A variation hVariationNonneg
      bound hBoundNonneg hVariationBound
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
      source
  have hSweep :=
    periodicHypercubicEvenSpatialSlice_reciprocalRandomScanRate_pow_card_mul_le_expSweep
      H
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
        H N hN beta hbeta A)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient_nonneg
        H N hN beta hbeta A)
      hGate sweeps
  exact hIter.trans
    (mul_le_mul_of_nonneg_right hSweep hBoundNonneg)

end

end MathlibAnalytic
end MGAP4D
