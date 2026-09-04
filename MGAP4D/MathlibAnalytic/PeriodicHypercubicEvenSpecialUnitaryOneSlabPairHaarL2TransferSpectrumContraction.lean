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

The carrier is split explicitly into its subsingleton and nontrivial cases. In
the subsingleton case the ordinary spectrum is empty. In the nontrivial case,
the general Banach-algebra spectrum norm bound combines with the already
canonical power contraction and `ContinuousLinearMap.norm_id_le`. -/
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
  let E :=
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
  let T : E →L[ℝ] E :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
      H N hN beta hbeta
  have hlambdaT : lambda ∈ spectrum ℝ (T ^ k) := by
    simpa [T, E] using hlambda
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI : Subsingleton E := hE
    have hfalse : False := by
      simpa using hlambdaT
    exact hfalse.elim
  · letI : Nontrivial E := hE
    have hlambdaNorm :
        ‖lambda‖ ≤ ‖T ^ k‖ * ‖(1 : E →L[ℝ] E)‖ := by
      exact spectrum.norm_le_norm_mul_of_mem hlambdaT
    have hTPow : ‖T ^ k‖ ≤ 1 := by
      simpa [T, E] using
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_pow_norm_le_one
          H k N hN beta hbeta)
    have hOne : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := by
      rw [ContinuousLinearMap.one_def]
      exact ContinuousLinearMap.norm_id_le
    have hlambdaAbs : |lambda| ≤ 1 := by
      calc
        |lambda| = ‖lambda‖ := by simp [Real.norm_eq_abs]
        _ ≤ ‖T ^ k‖ * ‖(1 : E →L[ℝ] E)‖ := hlambdaNorm
        _ ≤ 1 * 1 := by
          exact mul_le_mul hTPow hOne (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num
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
