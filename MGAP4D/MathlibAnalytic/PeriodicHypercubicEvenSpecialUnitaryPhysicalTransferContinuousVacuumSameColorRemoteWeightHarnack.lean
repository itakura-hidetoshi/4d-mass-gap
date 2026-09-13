import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFullSpatialOneLinkDoobBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSixColorDoobRemoteReplacementNormalForm
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumKernelHarnack
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumSameColorRemoteWeightHarnackSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance continuousVacuumSameColorRemoteWeightHarnackIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumSameColorRemoteWeightHarnackCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumSameColorRemoteWeightHarnackSecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumSameColorRemoteWeightHarnackMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumSameColorRemoteWeightHarnackBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumSameColorRemoteWeightHarnackSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The full-carrier continuous-vacuum weight has the same sharp one-link
pairwise Harnack distortion as the canonical continuous vacuum representative.
The coefficient is volume-independent and is exactly `exp (8 * beta)`.

This theorem is about the Doob weight only; no conditional-law factorization is
asserted. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight_replaceLink_pairwise_harnack
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
    let Omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
        H N hN beta hbeta
    let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
    Omega (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) g) ≤
        R * Omega (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) h) ∧
      Omega (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) h) ≤
        R * Omega (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) g) := by
  dsimp only
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let B := periodicHypercubicEvenSpatialSliceRestriction A
  have hRestrictG :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceRestriction_replaceLink_continuousVacuum
      H N hN beta hbeta A source g
  have hRestrictH :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceRestriction_replaceLink_continuousVacuum
      H N hN beta hbeta A source h
  have hVac :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_update_right_pairwise_harnack
      H N hN beta hbeta B source g h
  have hVacG :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N B source g) ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
              H N B source h) := by
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink]
      using hVac.1
  have hVacH :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N B source h) ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
              H N B source g) := by
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink]
      using hVac.2
  constructor
  · unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    apply ENNReal.ofReal_le_ofReal
    rw [hRestrictG, hRestrictH]
    exact hVacG
  · unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    apply ENNReal.ofReal_le_ofReal
    rw [hRestrictH, hRestrictG]
    exact hVacH

/-- After a target value has been fixed, changing any second spatial link still
changes the physical continuous-vacuum Doob weight by at most `exp (8 * beta)`
in either direction.  This is the exact two-link replacement-square estimate
needed by the same-color remote-replacement normal form. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight_twoLink_remote_pairwise_harnack
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
    let Omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
        H N hN beta hbeta
    let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
    Omega (C.base.replaceLink
          (C.base.replaceLink A
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) h) ≤
        R * Omega (C.base.replaceLink
          (C.base.replaceLink A
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) k) ∧
      Omega (C.base.replaceLink
          (C.base.replaceLink A
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) k) ≤
        R * Omega (C.base.replaceLink
          (C.base.replaceLink A
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) h) := by
  dsimp only
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  simpa [C] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight_replaceLink_pairwise_harnack
      H N hN beta hbeta
      (C.base.replaceLink A
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g)
      source h k

/-- For two distinct same-color spatial links, raw Wilson locality removes all
remote dependence except the continuous-vacuum weight.  The two surviving
weight families on the common raw target-link law are mutually pointwise
`exp (8 * beta)`-comparable.

This quantifies the exact obstruction exposed by the existing normal-form
theorem without asserting Doob independence or commutation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColor_remoteDoob_normalForm_weight_harnack
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
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
    let Omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
        H N hN beta hbeta
    let raw := C.singleLinkConditionalMeasure A
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
    let wh := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      Omega (C.base.replaceLink
        (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) h)
    let wk := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      Omega (C.base.replaceLink
        (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) k)
    let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
    C.singleLinkDoobConditionalMeasure Omega
        (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) h)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) =
        doobWeightedMeasure raw wh ∧
      C.singleLinkDoobConditionalMeasure Omega
        (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) k)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) =
        doobWeightedMeasure raw wk ∧
      (∀ g, wh g ≤ R * wk g ∧ wk g ≤ R * wh g) := by
  dsimp only
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
      H N hN beta hbeta
  refine ⟨?_, ?_, ?_⟩
  · simpa [C, Omega] using
      (periodicHypercubicEvenSpatialSliceLink_sameColor_singleLinkDoobConditionalMeasure_remote_replace_normal_form
        H N hN beta hbeta Omega hColor hne A h)
  · simpa [C, Omega] using
      (periodicHypercubicEvenSpatialSliceLink_sameColor_singleLinkDoobConditionalMeasure_remote_replace_normal_form
        H N hN beta hbeta Omega hColor hne A k)
  · intro g
    simpa [C, Omega] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight_twoLink_remote_pairwise_harnack
        H N hN beta hbeta A target source g h k)

end

end MathlibAnalytic
end MGAP4D
