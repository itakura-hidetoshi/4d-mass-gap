import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalEnvelopeRandomScanContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance uniformRemoteResidualCertificateSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance uniformRemoteResidualCertificateSpatialLinkNonempty
    (H : ℕ) : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

/-- A volume- and background-uniform bound on the exact remote residual
maximum column.  This predicate is the remaining analytic certificate needed
to turn the finite-volume physical envelope contraction into a genuinely
volume-uniform statement.

No existence of such a scalar is asserted here. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
    (N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (rho : ℝ) : Prop :=
  ∀ H : ℕ,
    ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualMaximumColumn
        H N hN beta hbeta A ≤ rho

/-- The source-independent envelope coefficient attached to a proposed
volume-uniform residual bound rho. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
    (beta rho : ℝ) : ℝ :=
  18 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta +
    rho

/-- A nonnegative uniform residual certificate gives a nonnegative uniform
physical envelope coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient_nonneg
    (beta rho : ℝ) (hbeta : 0 ≤ beta) (hRho : 0 ≤ rho) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
        beta rho := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
        beta hbeta))
    hRho

/-- A uniform remote residual certificate dominates every concrete
finite-volume physical envelope column coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient_le_uniform
    (N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (rho : ℝ)
    (hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
        N hN beta hbeta rho)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
        H N hN beta hbeta A ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
        beta rho := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
  exact add_le_add_right (hUniform H A) _

/-- Every finite-volume physical envelope source column is controlled by the
same uniform coefficient once a uniform remote residual certificate is
available. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_columnSum_le_uniform
    (N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (rho : ℝ)
    (hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
        N hN beta hbeta rho)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelColumnSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A)
        source ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
        beta rho := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_columnSum_le_coefficient
      H N hN beta hbeta A source).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeColumnCoefficient_le_uniform
        N hN beta hbeta rho hUniform H A)

/-- The exact maximum physical envelope column is bounded uniformly in volume
and background by the same coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_maximumColumn_le_uniform
    (N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (rho : ℝ)
    (hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
        N hN beta hbeta rho)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    finiteInfluenceKernelMaximumColumnSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
        beta rho := by
  apply finiteInfluenceKernelMaximumColumnSum_le_of_forall
  intro source
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_columnSum_le_uniform
      N hN beta hbeta rho hUniform H A source

/-- A single strict sparse/local gate together with a uniform remote residual
certificate gives strict maximum-column contraction for every finite volume and
background. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_maximumColumn_lt_one_of_uniformResidual
    (N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (rho : ℝ)
    (hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
        N hN beta hbeta rho)
    (hGate :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
        beta rho < 1)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    finiteInfluenceKernelMaximumColumnSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A) < 1 := by
  exact lt_of_le_of_lt
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_maximumColumn_le_uniform
      N hN beta hbeta rho hUniform H A)
    hGate

/-- Under one volume-uniform residual certificate and one strict uniform gate,
the physical SU(N) influence envelope contracts under reciprocal random scan
with a rate that is independent of H and A except for the standard reciprocal
single-site clock. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_uniformRandomScanIterate_le_rate_pow_mul
    (N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (rho : ℝ) (hRho : 0 ≤ rho)
    (hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
        N hN beta hbeta rho)
    (H : ℕ)
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
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
            beta rho) ^ n * bound := by
  exact finiteInfluenceKernelRandomScanVariationIterate_le_rate_pow_mul
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A)
    (periodicHypercubicEvenSpatialSliceLink_card_pos H)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
      beta rho)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient_nonneg
      beta rho hbeta hRho)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_columnSum_le_uniform
      N hN beta hbeta rho hUniform H A)
    variation hVariationNonneg bound hBoundNonneg hVariationBound n source

/-- Full-sweep exponential contraction with an exponent independent of the
finite volume H and background A, conditional only on the uniform remote
residual certificate and the strict uniform sparse/local gate.

This theorem does not prove the uniform residual certificate itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_uniformFullSweepIterate_le_exp
    (N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (rho : ℝ) (hRho : 0 ≤ rho)
    (hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemoteResidualUniformBound
        N hN beta hbeta rho)
    (hGate :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
        beta rho < 1)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ) (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (sweeps : ℕ) (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A)
        variation
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
        source ≤
      Real.exp
          (-(1 -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
                beta rho) * (sweeps : ℝ)) *
        bound := by
  have hIter :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_uniformRandomScanIterate_le_rate_pow_mul
      N hN beta hbeta rho hRho hUniform H A
      variation hVariationNonneg bound hBoundNonneg hVariationBound
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) * sweeps)
      source
  have hSweep :=
    periodicHypercubicEvenSpatialSlice_reciprocalRandomScanRate_pow_card_mul_le_expSweep
      H
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
        beta rho)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient_nonneg
        beta rho hbeta hRho)
      hGate sweeps
  exact hIter.trans
    (mul_le_mul_of_nonneg_right hSweep hBoundNonneg)

end

end MathlibAnalytic
end MGAP4D
