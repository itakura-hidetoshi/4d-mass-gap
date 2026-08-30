import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportExactDerivativeRatioReconstructionConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

local instance turanSaturationReconstructionConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance turanSaturationReconstructionConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance turanSaturationReconstructionConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance turanSaturationReconstructionConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance turanSaturationReconstructionConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance turanSaturationReconstructionConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance turanSaturationReconstructionConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance turanSaturationReconstructionConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- A single saturation of the physical factorial-normalized Turán hierarchy is
already equivalent to the full exact transfer/generator spectral-pair locus,
together with numerical reconstruction of that pair from the saturated scalar
resolvent derivative ratio.

Thus one adjacent equality `R_n(lambda) = R_{n+1}(lambda)` determines a unique
positive one-step transfer eigenvalue and logarithmic-generator energy, with
`rho = lambda + R_n(lambda)⁻¹` and
`tau = exp (-(lambda + R_n(lambda)⁻¹))`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_exactSpectralPairReconstruction
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    (n : ℕ) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    let R := iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
    (R =
      iteratedDeriv (n + 2) q lambda /
        ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda)) ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniqueTransferGeneratorSpectralPair
          H N hN beta hbeta v ∧
        ∃ tau rho : ℝ,
          0 < tau ∧
          tau = Real.exp (-rho) ∧
          rho = -Real.log tau ∧
          R = (rho - lambda)⁻¹ ∧
          R ≠ 0 ∧
          rho = lambda + R⁻¹ ∧
          tau = Real.exp (-(lambda + R⁻¹)) := by
  dsimp only
  constructor
  · intro heq
    have hpair :
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniqueTransferGeneratorSpectralPair
          H N hN beta hbeta v :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_uniqueTransferGeneratorSpectralPair
        H N hN beta hbeta v hv n lambda hlambda).mp heq
    refine ⟨hpair, ?_⟩
    simpa only using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_exactSpectralPair_reconstructed_by_derivativeRatio
        H N hN beta hbeta v hv hpair n lambda hlambda)
  · rintro ⟨hpair, _⟩
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_uniqueTransferGeneratorSpectralPair
        H N hN beta hbeta v hv n lambda hlambda).mpr hpair

end

end MathlibAnalytic
end MGAP4D
