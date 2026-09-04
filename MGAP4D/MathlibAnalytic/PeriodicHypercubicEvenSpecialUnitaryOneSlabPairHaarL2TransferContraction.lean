import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2Transfer
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance oneSlabPairHaarL2TransferContractionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance oneSlabPairHaarL2TransferContractionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance oneSlabPairHaarL2TransferContractionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance oneSlabPairHaarL2TransferContractionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance oneSlabPairHaarL2TransferContractionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance oneSlabPairHaarL2TransferContractionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The literal ordered-pair one-step Wilson kernel has `L²` norm at most one
under the pair-Haar probability product measure. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_norm_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
        H N hN beta hbeta‖ ≤ 1 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let μ₂ := μ.prod μ
  letI : IsProbabilityMeasure μ₂ := by
    dsimp [μ₂, μ]
    infer_instance
  have hOne :
      MemLp
        (fun _ :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
          (1 : ℝ))
        2 μ₂ :=
    memLp_const 1
  have hKernelAE :
      (fun p =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
          H N hN beta hbeta p) =ᵐ[μ₂]
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta := by
    simpa [μ₂, μ] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn
        H N hN beta hbeta
  have hle :
      ∀ᵐ p ∂μ₂,
        ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
            H N hN beta hbeta p‖ ≤
          ‖hOne.toLp
              (fun _ :
                (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
                  (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
                (1 : ℝ)) p‖ := by
    filter_upwards [hKernelAE, hOne.coeFn_toLp] with p hp hOnep
    rw [hp, hOnep]
    simpa [Real.norm_eq_abs] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_abs_le_one
        H N hN beta hbeta p
  calc
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2
        H N hN beta hbeta‖ ≤
      ‖hOne.toLp
          (fun _ :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
              (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
            (1 : ℝ))‖ :=
      Lp.norm_le_norm_of_ae_le hle
    _ = 1 := by
      rw [MemLp.toLp_const]
      rw [Lp.norm_const' (by norm_num) (by norm_num)]
      simp

/-- The ambient ordered-pair one-step transfer operator is a contraction on
pair-Haar `L²`. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_norm_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta‖ ≤ 1 := by
  exact
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_norm_le
      H N hN beta hbeta).trans
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_norm_le_one
        H N hN beta hbeta)

end

end MathlibAnalytic
end MGAP4D
