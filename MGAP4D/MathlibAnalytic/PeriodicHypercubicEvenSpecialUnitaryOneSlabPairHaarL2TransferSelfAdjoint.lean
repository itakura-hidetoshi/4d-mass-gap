import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveOperator
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TransferPowerContraction
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance oneSlabPairHaarL2TransferSelfAdjointTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance oneSlabPairHaarL2TransferSelfAdjointCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance oneSlabPairHaarL2TransferSelfAdjointSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance oneSlabPairHaarL2TransferSelfAdjointMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance oneSlabPairHaarL2TransferSelfAdjointBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance oneSlabPairHaarL2TransferSelfAdjointSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance oneSlabPairHaarL2TransferSelfAdjointPairHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- Symmetry of the literal endpoint-pair Wilson kernel descends to symmetry of
the canonical pair-Haar Hilbert--Schmidt transfer operator. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_isSymmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) →L[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) →ₗ[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)).IsSymmetric := by
  exact
    realL2HilbertSchmidtKernelOperator_isSymmetric_of_ae_symmetric_rep
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_representative_symmetric
        H N hN beta hbeta)

/-- The canonical ambient endpoint-pair transfer operator is self-adjoint on
pair-Haar `L²`. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_isSymmetric
      H N hN beta hbeta

/-- Every finite discrete-time iterate of the canonical pair transfer operator
remains self-adjoint. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_isSelfAdjoint
    (H k N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsSelfAdjoint
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta) ^ k) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_isSelfAdjoint
      H N hN beta hbeta).pow k

end

end MathlibAnalytic
end MGAP4D
