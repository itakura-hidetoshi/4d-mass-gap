import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumDoobVariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateFullSpatialOneLinkDoobBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumFullDoobNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance continuousVacuumFullDoobSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumFullDoobSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumFullDoobSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumFullDoobSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumFullDoobSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Pull the canonical continuous physical vacuum back from the spatial slice
to the full four-dimensional periodic Wilson configuration carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
      (periodicHypercubicEvenSpatialSliceRestriction A))

/-- Restricting a full Wilson one-link replacement is also exactly the
continuous-vacuum one-link replacement.  This is the carrier-identification
step that avoids evaluating any `L²` quotient representative. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceRestriction_replaceLink_continuousVacuum
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
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N (periodicHypercubicEvenSpatialSliceRestriction A) target g := by
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceRestriction_replaceLink
    H N hN beta hbeta A target g]
  rfl

/-- The generic full Wilson one-link Doob fiber weight is literally the
continuous physical-vacuum fiber weight on the intrinsic spatial slice. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_singleLinkDoobWeight_eq_spatialFiberWeight
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
        H N hN beta hbeta)
      A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
      H N hN beta hbeta
      (periodicHypercubicEvenSpatialSliceRestriction A) target g := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkDoobWeight
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceRestriction_replaceLink_continuousVacuum
    H N hN beta hbeta A target g]

/-- Actual full-carrier ground-state one-link Doob law, now based on the
canonical continuous physical vacuum rather than an arbitrary `L²`
representative. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure
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
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
      H N hN beta hbeta)
    A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)

/-- The full-carrier continuous-vacuum Doob law is exactly the spatial-fiber
Doob law whose raw measure is the literal Wilson one-link conditional law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure_eq
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure
        H N hN beta hbeta A target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure
        H N hN beta hbeta
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
            A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))
        (periodicHypercubicEvenSpatialSliceRestriction A) target := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkDoobConditionalMeasure
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure
  congr 1
  funext g
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_singleLinkDoobWeight_eq_spatialFiberWeight
      H N hN beta hbeta A target g

/-- Volume-uniform one-link variance comparison for the literal even-periodic
`SU(N)` Wilson conditional law after physical ground-state Doob reweighting.

All former fiber-distortion hypotheses are now discharged by the canonical
continuous vacuum Harnack theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoob_evariance_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : MemLp X 2
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
          A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))) :
    let omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta
    let R : ℝ := Real.exp (8 * beta)
    let m : ℝ≥0∞ :=
      ENNReal.ofReal (omega (periodicHypercubicEvenSpatialSliceRestriction A) / R)
    let M : ℝ≥0∞ :=
      ENNReal.ofReal (R * omega (periodicHypercubicEvenSpatialSliceRestriction A))
    (m / M) *
        evariance X
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
              A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)) ≤
      evariance X
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure
          H N hN beta hbeta A target) := by
  dsimp only
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoob_evariance_lower_bound
      H N hN beta hbeta
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
          A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))
      (periodicHypercubicEvenSpatialSliceRestriction A) target X hX
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure_eq]
  exact h

end

end MathlibAnalytic
end MGAP4D
