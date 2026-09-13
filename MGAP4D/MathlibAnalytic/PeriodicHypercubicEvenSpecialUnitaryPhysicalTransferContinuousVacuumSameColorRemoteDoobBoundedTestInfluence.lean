import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumSameColorRemoteDoobMeasureComparison
import MGAP4D.MathlibAnalytic.ProbabilityMeasureMutualDominationBoundedTest
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumSameColorRemoteDoobBoundedTestInfluenceSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance continuousVacuumSameColorRemoteDoobBoundedTestInfluenceIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumSameColorRemoteDoobBoundedTestInfluenceCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumSameColorRemoteDoobBoundedTestInfluenceSecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumSameColorRemoteDoobBoundedTestInfluenceMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumSameColorRemoteDoobBoundedTestInfluenceBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumSameColorRemoteDoobBoundedTestInfluenceSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Remote replacement at a distinct same-color source link changes every
bounded measurable target-link test by at most the sharp mutual-domination
coefficient associated with `K = exp (16 * beta)`.

This is the Dobrushin-ready consequence of the normalized Doob-measure Harnack
comparison.  It does not assert exact same-color independence or commutation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColor_remoteDoob_boundedTest_influence
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H target =
      periodicHypercubicEvenSpatialSliceLinkColor H source)
    (hne : target ≠ source)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ g, |phi g| ≤ 1) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
    let Omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
        H N hN beta hbeta
    let targetEdge := periodicHypercubicEvenSpatialSliceLinkEmbedding H target
    let sourceEdge := periodicHypercubicEvenSpatialSliceLinkEmbedding H source
    let Ah := C.base.replaceLink A sourceEdge h
    let Ak := C.base.replaceLink A sourceEdge k
    |(∫ g, phi g ∂C.singleLinkDoobConditionalMeasure Omega Ah targetEdge) -
      (∫ g, phi g ∂C.singleLinkDoobConditionalMeasure Omega Ak targetEdge)| ≤
      2 * ((Real.exp (16 * beta) - 1) / (Real.exp (16 * beta) + 1)) := by
  dsimp only
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
      H N hN beta hbeta
  let targetEdge := periodicHypercubicEvenSpatialSliceLinkEmbedding H target
  let sourceEdge := periodicHypercubicEvenSpatialSliceLinkEmbedding H source
  let Ah := C.base.replaceLink A sourceEdge h
  let Ak := C.base.replaceLink A sourceEdge k
  let μh := C.singleLinkDoobConditionalMeasure Omega Ah targetEdge
  let μk := C.singleLinkDoobConditionalMeasure Omega Ak targetEdge
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
  have hRawProbH : IsProbabilityMeasure (C.singleLinkConditionalMeasure Ah targetEdge) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C Ah targetEdge
  have hRawProbK : IsProbabilityMeasure (C.singleLinkConditionalMeasure Ak targetEdge) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C Ak targetEdge
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure Ah targetEdge) := hRawProbH
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure Ak targetEdge) := hRawProbK
  have hProbH : IsProbabilityMeasure μh := by
    change IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure
        H N hN beta hbeta Ah target)
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure_eq]
    exact
      @periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure_isProbability
        H N hN beta hbeta
        (C.singleLinkConditionalMeasure Ah targetEdge) hRawProbH
        (periodicHypercubicEvenSpatialSliceRestriction Ah) target
  have hProbK : IsProbabilityMeasure μk := by
    change IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure
        H N hN beta hbeta Ak target)
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure_eq]
    exact
      @periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure_isProbability
        H N hN beta hbeta
        (C.singleLinkConditionalMeasure Ak targetEdge) hRawProbK
        (periodicHypercubicEvenSpatialSliceRestriction Ak) target
  letI : IsProbabilityMeasure μh := hProbH
  letI : IsProbabilityMeasure μk := hProbK
  have hCmpR :
      μh ≤ (R * R) • μk ∧ μk ≤ (R * R) • μh := by
    simpa [C, Omega, targetEdge, sourceEdge, Ah, Ak, μh, μk, R] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColor_remoteDoob_pairwise_measure_harnack
        H N hN beta hbeta hColor hne A h k)
  have hR2 : R * R = ENNReal.ofReal (Real.exp (16 * beta)) := by
    dsimp [R]
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    apply congrArg ENNReal.ofReal
    rw [← Real.exp_add]
    congr 1
    ring
  have hCmp :
      μh ≤ ENNReal.ofReal (Real.exp (16 * beta)) • μk ∧
        μk ≤ ENNReal.ofReal (Real.exp (16 * beta)) • μh := by
    simpa only [hR2] using hCmpR
  have hK : 1 ≤ Real.exp (16 * beta) := by
    apply Real.one_le_exp
    positivity
  change
    |(∫ g, phi g ∂μh) - (∫ g, phi g ∂μk)| ≤
      2 * ((Real.exp (16 * beta) - 1) / (Real.exp (16 * beta) + 1))
  exact
    probabilityMeasure_boundedTest_integral_difference_abs_le_of_pairwise_le_smul
      μh μk (Real.exp (16 * beta)) hK hCmp.1 hCmp.2 phi hphi hphiBound

end

end MathlibAnalytic
end MGAP4D
