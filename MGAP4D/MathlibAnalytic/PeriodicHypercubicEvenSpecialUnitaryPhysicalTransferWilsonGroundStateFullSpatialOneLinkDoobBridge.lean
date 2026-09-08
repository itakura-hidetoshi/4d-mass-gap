import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkDoobVariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateSpatialLinkFiberDistortion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Restricting a full four-dimensional one-link replacement to the canonical
spatial slice is exactly the intrinsic spatial-slice one-link replacement.

The proof uses only injectivity of the spatial-link embedding; no global
identification of the full and boundary configuration carriers is introduced. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceRestriction_replaceLink
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialSliceRestriction
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.replaceLink
            A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceReplaceLink H N
        (periodicHypercubicEvenSpatialSliceRestriction A) target g := by
  funext e
  by_cases he : e = target
  · subst e
    simp [periodicHypercubicEvenSpecialUnitarySpatialSliceReplaceLink,
      CompactOrientedGaugeWilsonSystem.replaceLink]
  · have hEmbedding :
        periodicHypercubicEvenSpatialSliceLinkEmbedding H e ≠
          periodicHypercubicEvenSpatialSliceLinkEmbedding H target := by
      intro hEq
      exact he (periodicHypercubicEvenSpatialSliceLinkEmbedding_injective H hEq)
    simp [periodicHypercubicEvenSpecialUnitarySpatialSliceReplaceLink,
      CompactOrientedGaugeWilsonSystem.replaceLink, he, hEmbedding]

/-- The physical top-vacuum amplitude pulled back from a full four-dimensional
configuration by spatial restriction. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumFullConfigurationWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1
      (periodicHypercubicEvenSpatialSliceRestriction A))

/-- On an embedded spatial link, the generic Wilson Doob fiber weight obtained
from the pulled-back physical vacuum is exactly the intrinsic physical vacuum
fiber weight introduced on the spatial-slice carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_singleLinkDoobWeight_eq_spatialFiberWeight
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkDoobWeight
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumFullConfigurationWeight
        H N hN beta hbeta)
      A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSpatialLinkFiberWeight
      H N hN beta hbeta
      (periodicHypercubicEvenSpatialSliceRestriction A) target g := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkDoobWeight
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumFullConfigurationWeight
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSpatialLinkFiberWeight
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceRestriction_replaceLink
    H N hN beta hbeta A target g]

/-- The actual physical ground-state one-link Doob law attached to an embedded
spatial link, written directly on the full periodic Wilson configuration
carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFullSpatialLinkDoobMeasure
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkDoobConditionalMeasure
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumFullConfigurationWeight
      H N hN beta hbeta)
    A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)

/-- The full-carrier Wilson Doob law is exactly the spatial-fiber physical Doob
law whose raw probability measure is the literal Wilson one-link conditional
law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFullSpatialLinkDoobMeasure_eq
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFullSpatialLinkDoobMeasure
        H N hN beta hbeta A target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkDoobMeasure
        H N hN beta hbeta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
            A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))
        (periodicHypercubicEvenSpatialSliceRestriction A) target := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFullSpatialLinkDoobMeasure
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkDoobConditionalMeasure
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkDoobMeasure
  congr 1
  funext g
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_singleLinkDoobWeight_eq_spatialFiberWeight
      H N hN beta hbeta A target g

/-- Concrete one-link variance transfer for the actual even-periodic `SU(N)`
Wilson conditional law and the actual physical top-vacuum Doob reweighting.

The only remaining model-side input is the explicit fiber distortion receipt
`D`; no same-color factorization or commutation of Doob-resampled links is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFullSpatialLinkDoob_evariance_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSpatialLinkFiberDistortionData
        H N hN beta hbeta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
            A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))
        (periodicHypercubicEvenSpatialSliceRestriction A) target)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : MemLp X 2
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
          A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))) :
    (D.m / D.M) *
        evariance X
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
              A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)) ≤
      evariance X
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFullSpatialLinkDoobMeasure
          H N hN beta hbeta A target) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let nu := C.singleLinkConditionalMeasure A
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
  letI : IsProbabilityMeasure nu :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkDoob_evariance_lower_bound
      H N hN beta hbeta nu
      (periodicHypercubicEvenSpatialSliceRestriction A) target D X hX
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFullSpatialLinkDoobMeasure_eq
    H N hN beta hbeta A target] at h
  exact h

end

end MathlibAnalytic
end MGAP4D
