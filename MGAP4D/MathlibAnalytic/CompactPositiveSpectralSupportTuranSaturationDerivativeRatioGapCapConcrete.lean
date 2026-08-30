import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportTuranSaturationQuantitativeGapBoundConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

local instance turanRatioGapCapConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance turanRatioGapCapConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance turanRatioGapCapConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance turanRatioGapCapConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance turanRatioGapCapConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance turanRatioGapCapConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance turanRatioGapCapConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance turanRatioGapCapConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- On the Turán-rigidity locus, the directly observable normalized derivative
ratio is bounded by the inverse distance from the resolvent parameter to the
finite-volume coercive gap.  Writing
`c = 2 * finiteVolumeDecayRate` and `R = R_n(lambda)`, one has
`0 < R ≤ (c - lambda)⁻¹` whenever `|lambda| < c` and the adjacent Turán ratio
saturates. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_turanSaturation_derivativeRatio_le_gapResolventDistance
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    (n : ℕ) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)
    (hsaturation :
      let q :=
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
          H N hN beta hbeta v
      iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda) =
        iteratedDeriv (n + 2) q lambda /
          ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda)) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    let R := iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
    let c :=
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta
    0 < R ∧ R ≤ (c - lambda)⁻¹ := by
  dsimp only at hsaturation ⊢
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let R := iteratedDeriv (n + 1) q lambda /
    ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  have hquant :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_turanSaturation_quantitativeSpectralGap
      H N hN beta hbeta v hv n lambda hlambda hsaturation
  dsimp only at hquant
  rcases hquant with ⟨_, hcR, _, _, _⟩
  have hn :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
      H N hN beta hbeta v hv n lambda hlambda
  have hn1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
      H N hN beta hbeta v hv (n + 1) lambda hlambda
  have hRPos : 0 < R := by
    dsimp [R, q]
    positivity
  have hlambdaC : |lambda| < c := by
    simpa [c] using hlambda
  have hgapDistancePos : 0 < c - lambda := by
    have hlambdaLtC : lambda < c :=
      lt_of_le_of_lt (le_abs_self lambda) hlambdaC
    linarith
  have hgapDistance_le_invR : c - lambda ≤ R⁻¹ := by
    linarith
  have hmul : (c - lambda) * R ≤ 1 := by
    have h : c - lambda ≤ 1 / R := by
      simpa [one_div] using hgapDistance_le_invR
    exact (le_div_iff₀ hRPos).mp h
  have hRUpperDiv : R ≤ 1 / (c - lambda) := by
    apply (le_div_iff₀ hgapDistancePos).2
    simpa [mul_comm] using hmul
  have hRUpper : R ≤ (c - lambda)⁻¹ := by
    simpa [one_div] using hRUpperDiv
  exact ⟨hRPos, hRUpper⟩

end

end MathlibAnalytic
end MGAP4D
