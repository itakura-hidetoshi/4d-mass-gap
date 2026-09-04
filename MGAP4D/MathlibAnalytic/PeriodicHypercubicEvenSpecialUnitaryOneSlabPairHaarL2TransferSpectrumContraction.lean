import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TransferRayleighContraction
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance oneSlabPairHaarL2TransferSpectrumContractionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance oneSlabPairHaarL2TransferSpectrumContractionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance oneSlabPairHaarL2TransferSpectrumContractionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance oneSlabPairHaarL2TransferSpectrumContractionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance oneSlabPairHaarL2TransferSpectrumContractionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance oneSlabPairHaarL2TransferSpectrumContractionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every real spectral value of every finite discrete-time iterate of the
canonical endpoint-pair transfer operator lies in the closed unit interval.

The proof first embeds the ordinary spectrum into the quasispectrum and then
uses the non-unital Banach-algebra bound `quasispectrum.norm_le_norm_of_mem`.
This avoids introducing or searching for a `Nontrivial` instance on the
endomorphism algebra. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_spectrum_mem_Icc
    (H k N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : lambda ∈ spectrum ℝ
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta) ^ k)) :
    lambda ∈ Set.Icc (-1 : ℝ) 1 := by
  have hlambdaQuasi :
      lambda ∈ quasispectrum ℝ
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta) ^ k) :=
    spectrum_subset_quasispectrum ℝ _ hlambda
  have hlambdaNorm :
      ‖lambda‖ ≤
        ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta) ^ k‖ :=
    quasispectrum.norm_le_norm_of_mem hlambdaQuasi
  have hTPow :
      ‖(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta) ^ k‖ ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_norm_le_one
      H k N hN beta hbeta
  have hlambdaAbs : |lambda| ≤ 1 := by
    simpa [Real.norm_eq_abs] using hlambdaNorm.trans hTPow
  exact abs_le.mp hlambdaAbs

/-- The real spectrum of every finite pair-transfer iterate is contained in
`[-1,1]`. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_spectrum_subset_Icc
    (H k N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    spectrum ℝ
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta) ^ k) ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro lambda hlambda
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_spectrum_mem_Icc
      H k N hN beta hbeta lambda hlambda

/-- In particular, the one-step pair-transfer spectrum is contained in
`[-1,1]`. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_spectrum_subset_Icc
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    spectrum ℝ
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta) ⊆ Set.Icc (-1 : ℝ) 1 := by
  simpa using
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_spectrum_subset_Icc
      H 1 N hN beta hbeta)

end

end MathlibAnalytic
end MGAP4D
