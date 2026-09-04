import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TransferContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance oneSlabPairHaarL2TransferPowerContractionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance oneSlabPairHaarL2TransferPowerContractionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance oneSlabPairHaarL2TransferPowerContractionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance oneSlabPairHaarL2TransferPowerContractionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance oneSlabPairHaarL2TransferPowerContractionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance oneSlabPairHaarL2TransferPowerContractionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every finite power of the ambient ordered-pair transfer operator is a
contraction on every pair-Haar `L²` vector. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_apply_norm_le
    (H k N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (psi : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
    ‖((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta) ^ k) psi‖ ≤ ‖psi‖ := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      calc
        ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta
          (((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
              H N hN beta hbeta) ^ k) psi)‖ ≤
          ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta‖ *
            ‖((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
                H N hN beta hbeta) ^ k) psi‖ :=
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta).le_opNorm _
        _ ≤ 1 *
            ‖((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
                H N hN beta hbeta) ^ k) psi‖ := by
          exact mul_le_mul_of_nonneg_right
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_norm_le_one
              H N hN beta hbeta)
            (norm_nonneg _)
        _ =
            ‖((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
                H N hN beta hbeta) ^ k) psi‖ := by
          simp
        _ ≤ ‖psi‖ := ih

/-- Every finite power of the ambient ordered-pair transfer operator remains a
contraction in operator norm. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_norm_le_one
    (H k N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta) ^ k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro psi
  simpa only [one_mul] using
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_apply_norm_le
      H k N hN beta hbeta psi

end

end MathlibAnalytic
end MGAP4D
