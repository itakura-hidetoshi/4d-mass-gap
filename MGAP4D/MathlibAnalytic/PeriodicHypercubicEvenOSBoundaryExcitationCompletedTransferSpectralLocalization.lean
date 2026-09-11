import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedTransferSelfAdjoint
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- The identity bounded endomorphism has operator norm at most one, without
assuming that the Hilbert carrier is nontrivial.  This zero-carrier-safe form
is convenient for real spectrum estimates below. -/
theorem realContinuousLinearMap_norm_one_le_one
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E] :
    ‖(1 : E →L[ℝ] E)‖ ≤ 1 := by
  change ContinuousLinearMap.opNorm (1 : E →L[ℝ] E) ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound
  · norm_num
  · intro x
    simp

/-- For a bounded real endomorphism of a Banach space, every real spectral
value has norm at most the operator norm.  Unlike
`spectrum.norm_le_norm_of_mem`, this formulation does not require a
`NormOneClass` and therefore remains valid if the carrier is trivial. -/
theorem realContinuousLinearMap_spectrum_norm_le_opNorm
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →L[ℝ] E)
    {lambda : ℝ}
    (hlambda : lambda ∈ spectrum ℝ A) :
    ‖lambda‖ ≤ ‖A‖ := by
  have hraw :
      ‖lambda‖ ≤ ‖A‖ * ‖(1 : E →L[ℝ] E)‖ :=
    spectrum.norm_le_norm_mul_of_mem hlambda
  calc
    ‖lambda‖ ≤ ‖A‖ * ‖(1 : E →L[ℝ] E)‖ := hraw
    _ ≤ ‖A‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (realContinuousLinearMap_norm_one_le_one (E := E))
        (norm_nonneg A)
    _ = ‖A‖ := by ring

/-- Any real scalar whose norm is strictly larger than the operator norm lies
in the real resolvent set.  The proof again avoids a nontriviality assumption
on the carrier by using the general `‖A‖ * ‖1‖` Neumann estimate. -/
theorem realContinuousLinearMap_mem_resolventSet_of_opNorm_lt_norm
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →L[ℝ] E)
    {lambda : ℝ}
    (h : ‖A‖ < ‖lambda‖) :
    lambda ∈ resolventSet ℝ A := by
  apply spectrum.mem_resolventSet_of_norm_lt_mul
  calc
    ‖A‖ * ‖(1 : E →L[ℝ] E)‖ ≤ ‖A‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (realContinuousLinearMap_norm_one_le_one (E := E))
        (norm_nonneg A)
    _ = ‖A‖ := by ring
    _ < ‖lambda‖ := h

local instance osBoundaryExcitationCompletedTransferSpectralLocalizationSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedTransferSpectralLocalizationSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedTransferSpectralLocalizationSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedTransferSpectralLocalizationSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedTransferSpectralLocalizationSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedTransferSpectralLocalizationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedTransferSpectralLocalizationSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedTransferSpectralLocalizationPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The explicit positive-time spectral radius bound carried by the completed
excitation transfer.  This is a finite-volume transfer radius, not a continuum
mass-gap value. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) : ℝ :=
  Real.exp
    (-2 * (n : ℝ) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta)

/-- The completed excitation decay radius is always positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
      H N hN beta hbeta n := by
  exact Real.exp_pos _

/-- At every positive integer Euclidean time, the completed excitation decay
radius is strictly below one because the finite-volume logarithmic decay rate
is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius_lt_one_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
        H N hN beta hbeta n < 1 := by
  have hr :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
      H N hN beta hbeta
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hneg :
      -2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta < 0 := by
    nlinarith
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
  calc
    Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) < Real.exp 0 :=
      Real.exp_lt_exp.mpr hneg
    _ = 1 := Real.exp_zero

/-- The completed pair-Hilbert excitation transfer obeys the explicit decay
radius bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_le_decayRadius_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
        H N hN beta hbeta n := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius] using
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_le_exp_of_pos
      H N hN beta hbeta n hn

/-- Hence every positive-time completed excitation transfer is a strict
contraction in operator norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_lt_one_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n‖ < 1 := by
  exact lt_of_le_of_lt
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_le_decayRadius_of_pos
      H N hN beta hbeta n hn)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius_lt_one_of_pos
      H N hN beta hbeta n hn)

/-- Every real spectral value of the positive-time completed transfer lies
inside the explicit finite-volume decay interval. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_spectrum_subset_decayInterval_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n) ⊆
      Icc
        (-periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
          H N hN beta hbeta n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
          H N hN beta hbeta n) := by
  intro lambda hlambda
  have hspectral :
      ‖lambda‖ ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n‖ :=
    realContinuousLinearMap_spectrum_norm_le_opNorm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n)
      hlambda
  have habs :
      |lambda| ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
          H N hN beta hbeta n := by
    simpa [Real.norm_eq_abs] using
      hspectral.trans
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_le_decayRadius_of_pos
          H N hN beta hbeta n hn)
  exact abs_le.mp habs

/-- In particular, all positive-time real spectral values lie strictly between
`-1` and `1`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_spectrum_subset_openUnitInterval_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n) ⊆ Ioo (-1 : ℝ) 1 := by
  intro lambda hlambda
  have hspectral :
      ‖lambda‖ ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n‖ :=
    realContinuousLinearMap_spectrum_norm_le_opNorm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n)
      hlambda
  have habs : |lambda| < 1 := by
    simpa [Real.norm_eq_abs] using
      lt_of_le_of_lt hspectral
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_lt_one_of_pos
          H N hN beta hbeta n hn)
  exact abs_lt.mp habs

/-- Every real scalar outside the explicit decay interval belongs to the
resolvent set of the positive-time completed excitation transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_mem_resolventSet_of_decayRadius_lt_abs
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (lambda : ℝ)
    (hlambda :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
          H N hN beta hbeta n < |lambda|) :
    lambda ∈ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n) := by
  apply realContinuousLinearMap_mem_resolventSet_of_opNorm_lt_norm
  have hnorm :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n‖ < |lambda| :=
    lt_of_le_of_lt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_le_decayRadius_of_pos
        H N hN beta hbeta n hn)
      hlambda
  simpa [Real.norm_eq_abs] using hnorm

/-- `+1` is in the resolvent set of every positive-time completed excitation
transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_mem_resolventSet_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    (1 : ℝ) ∈ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_mem_resolventSet_of_decayRadius_lt_abs
      H N hN beta hbeta n hn 1
  simpa using
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius_lt_one_of_pos
      H N hN beta hbeta n hn

/-- `-1` is also in the resolvent set of every positive-time completed
excitation transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_neg_one_mem_resolventSet_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    (-1 : ℝ) ∈ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_mem_resolventSet_of_decayRadius_lt_abs
      H N hN beta hbeta n hn (-1)
  simpa using
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius_lt_one_of_pos
      H N hN beta hbeta n hn

/-- Audit-visible completed finite-volume spectral-localization package. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedTransferSpectralLocalizationPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  transferSelfAdjoint :
    ∀ n : ℕ,
      IsSelfAdjoint
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n)
  positiveTimeStrictContraction :
    ∀ n : ℕ, 0 < n →
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n‖ < 1
  positiveTimeSpectrumInDecayInterval :
    ∀ n : ℕ, 0 < n →
      spectrum ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n) ⊆
        Icc
          (-periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
            H N hN beta hbeta n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
            H N hN beta hbeta n)
  positiveTimeSpectrumInOpenUnitInterval :
    ∀ n : ℕ, 0 < n →
      spectrum ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n) ⊆ Ioo (-1 : ℝ) 1
  positiveTimeExteriorResolvent :
    ∀ (n : ℕ), 0 < n → ∀ lambda : ℝ,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
          H N hN beta hbeta n < |lambda| →
        lambda ∈ resolventSet ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n)
  positiveTimeOneResolvent :
    ∀ n : ℕ, 0 < n →
      (1 : ℝ) ∈ resolventSet ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n)
  positiveTimeNegOneResolvent :
    ∀ n : ℕ, 0 < n →
      (-1 : ℝ) ∈ resolventSet ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n)

/-- Construct the completed finite-volume spectral-localization package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedTransferSpectralLocalizationPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedTransferSpectralLocalizationPackage
      H N hN beta hbeta :=
  { transferSelfAdjoint :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isSelfAdjoint
        H N hN beta hbeta
    positiveTimeStrictContraction :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_lt_one_of_pos
        H N hN beta hbeta
    positiveTimeSpectrumInDecayInterval :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_spectrum_subset_decayInterval_of_pos
        H N hN beta hbeta
    positiveTimeSpectrumInOpenUnitInterval :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_spectrum_subset_openUnitInterval_of_pos
        H N hN beta hbeta
    positiveTimeExteriorResolvent :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_mem_resolventSet_of_decayRadius_lt_abs
        H N hN beta hbeta
    positiveTimeOneResolvent :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_mem_resolventSet_of_pos
        H N hN beta hbeta
    positiveTimeNegOneResolvent :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_neg_one_mem_resolventSet_of_pos
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
