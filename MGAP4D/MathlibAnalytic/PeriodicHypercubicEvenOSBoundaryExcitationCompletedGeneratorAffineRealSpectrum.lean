import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventSpectralStieltjes
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- Real spectrum transforms exactly under the affine involution `T ↦ I - T`.
This is purely Banach-algebraic and does not use a spectral theorem. -/
theorem realContinuousLinearMap_one_sub_spectrum_mem_iff
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (T : E →L[ℝ] E)
    (lambda : ℝ) :
    lambda ∈ spectrum ℝ (1 - T) ↔
      1 - lambda ∈ spectrum ℝ T := by
  rw [spectrum.mem_iff, spectrum.mem_iff]
  simp only [Algebra.algebraMap_eq_smul_one]
  have hshift :
      lambda • (1 : E →L[ℝ] E) - (1 - T) =
        -((1 - lambda) • (1 : E →L[ℝ] E) - T) := by
    module
  rw [hshift, IsUnit.neg_iff]

/-- Set form of the exact affine real-spectrum correspondence. -/
theorem realContinuousLinearMap_spectrum_one_sub_eq_reflection_image
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (T : E →L[ℝ] E) :
    spectrum ℝ (1 - T) =
      (fun x : ℝ => 1 - x) '' spectrum ℝ T := by
  ext lambda
  constructor
  · intro hlambda
    refine ⟨1 - lambda,
      (realContinuousLinearMap_one_sub_spectrum_mem_iff T lambda).1 hlambda, ?_⟩
    ring
  · rintro ⟨mu, hmu, rfl⟩
    apply (realContinuousLinearMap_one_sub_spectrum_mem_iff T (1 - mu)).2
    convert hmu using 1 <;> ring

local instance osBoundaryExcitationCompletedGeneratorAffineSpectrumSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedGeneratorAffineSpectrumSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedGeneratorAffineSpectrumSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedGeneratorAffineSpectrumSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedGeneratorAffineSpectrumSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedGeneratorAffineSpectrumSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedGeneratorAffineSpectrumSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedGeneratorAffineSpectrumPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The completed one-step generator spectrum is exactly the reflection of the
completed one-step transfer spectrum across `1/2`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_eq_transfer_reflection
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta) =
      (fun x : ℝ => 1 - x) ''
        spectrum ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
  exact
    realContinuousLinearMap_spectrum_one_sub_eq_reflection_image
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)

/-- Pointwise exact transfer/generator real-spectrum correspondence. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_mem_iff_transfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ) :
    lambda ∈ spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta) ↔
      1 - lambda ∈ spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
  exact
    realContinuousLinearMap_one_sub_spectrum_mem_iff
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)
      lambda

@[simp]
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap_eq_one_sub_decayRadius
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
        H N hN beta hbeta =
      1 - periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
        H N hN beta hbeta 1 :=
  rfl

/-- The full unconditional real spectrum of the completed one-step generator
lies in the compact interval obtained by reflecting the transfer decay interval.
The lower endpoint is exactly the coercive gap from the independent resolvent
route of the previous layer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_subset_gap_to_one_add_decayRadius
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta) ⊆
      Icc
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
        (1 + periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
          H N hN beta hbeta 1) := by
  intro lambda hlambda
  have htransfer :
      1 - lambda ∈ spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_mem_iff_transfer
      H N hN beta hbeta lambda).1 hlambda
  have hinterval :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_spectrum_subset_decayInterval_of_pos
      H N hN beta hbeta 1 (by norm_num) htransfer
  rcases hinterval with ⟨hlower, hupper⟩
  constructor
  · unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
    linarith
  · linarith

/-- The lower spectral-support theorem from the affine transfer route agrees
with the coercive below-gap route. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_ge_gap_via_transfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ lambda ∈ spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
        H N hN beta hbeta ≤ lambda := by
  intro lambda hlambda
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_subset_gap_to_one_add_decayRadius
      H N hN beta hbeta hlambda).1

/-- Every real scalar strictly above the reflected transfer-radius endpoint is
in the generator resolvent set. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_one_add_decayRadius_lt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      1 + periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
          H N hN beta hbeta 1 < lambda) :
    lambda ∈ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta) := by
  by_contra hres
  have hspectrum :
      lambda ∈ spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta) := by
    change lambda ∉ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
    exact hres
  have hbounds :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_subset_gap_to_one_add_decayRadius
      H N hN beta hbeta hspectrum
  exact (not_le_of_gt hlambda) hbounds.2

/-- The whole exterior of the closed generator spectral interval belongs to
its real resolvent set. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_outside_spectralInterval
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hout :
      lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta ∨
        1 + periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
            H N hN beta hbeta 1 < lambda) :
    lambda ∈ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta) := by
  rcases hout with hlower | hupper
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_lt_gap
        H N hN beta hbeta lambda hlower
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_one_add_decayRadius_lt
        H N hN beta hbeta lambda hupper

/-- Audit-visible package collecting the exact affine transfer/generator
spectrum relation and the resulting two-sided real spectral enclosure. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorAffineRealSpectrumPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  exactAffineSpectrum :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta) =
      (fun x : ℝ => 1 - x) ''
        spectrum ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1)
  generatorSpectrumEnclosure :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta) ⊆
      Icc
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
        (1 + periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
          H N hN beta hbeta 1)
  belowGapResolvent :
    ∀ lambda,
      lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta →
        lambda ∈ resolventSet ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta)
  aboveUpperEndpointResolvent :
    ∀ lambda,
      1 + periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
          H N hN beta hbeta 1 < lambda →
        lambda ∈ resolventSet ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta)

/-- Construct the completed affine real-spectrum package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorAffineRealSpectrumPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorAffineRealSpectrumPackage
      H N hN beta hbeta :=
  { exactAffineSpectrum :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_eq_transfer_reflection
        H N hN beta hbeta
    generatorSpectrumEnclosure :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_subset_gap_to_one_add_decayRadius
        H N hN beta hbeta
    belowGapResolvent :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_lt_gap
        H N hN beta hbeta
    aboveUpperEndpointResolvent :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_one_add_decayRadius_lt
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
