import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageProfileOscillationMajorant
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Tactic

/-!
# Bounded-continuous dense-core closure for the genuine sweep-stage profile

The current Dobrushin/Feller machinery is naturally formulated on bounded
continuous observables.  The previous ground-state sweep-stage closure used
the larger dense bounded-strongly-measurable concrete core.

This file records the more directly usable dense-core theorem on
`BoundedContinuousFunction` itself.

Mathlib's canonical map

  BoundedContinuousFunction.toLp

has dense range in real L2.  Since the genuine six-spatial sweep-stage profile
energy is continuous on the full ground-state joint L2 carrier, any continuous
scalar upper majorant proved for every bounded-continuous representative
extends to every joint-L2 vector without loss.

A second theorem combines this directly with the #5144 stagewise concrete
oscillation-energy estimate.  The pointwise oscillation profile need not be
continuous in L2; only the final scalar majorant does.

This is the density bridge needed to keep the Dobrushin/Feller analysis on its
native bounded-continuous carrier.  No transfer identification, Euclidean-time
interpretation, or H1-D5 exact descent is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

local instance groundStateProfileBCFClosureTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateProfileBCFClosureCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateProfileBCFClosureSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateProfileBCFClosureMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateProfileBCFClosureBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateProfileBCFClosureSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance groundStateProfileBCFClosureAmbientMatrixPseudoMetrizableSpace
    (N : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin N) (Fin N) ℂ) := by
  change TopologicalSpace.PseudoMetrizableSpace (Fin N → Fin N → ℂ)
  infer_instance

local instance groundStateProfileBCFClosureGaugePseudoMetrizableSpace
    (N : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace
      (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  change TopologicalSpace.PseudoMetrizableSpace
    {U : Matrix (Fin N) (Fin N) ℂ |
      U ∈ Matrix.specialUnitaryGroup (Fin N) ℂ}
  infer_instance

local instance groundStateProfileBCFClosureSpatialConfigurationPseudoMetrizableSpace
    (H N : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) := by
  change TopologicalSpace.PseudoMetrizableSpace
    (PeriodicHypercubicEvenSpatialSliceLink H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
  infer_instance

local instance groundStateProfileBCFClosureJointPseudoMetrizableSpace
    (H N : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) := by
  infer_instance

local instance groundStateProfileBCFClosureProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

local instance groundStateProfileBCFClosureWeaklyRegular
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta).WeaklyRegular := by
  infer_instance

/-- The bounded-continuous joint observable carrier at one finite
ground-state scale. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryGroundStateJointBCF
    (H N : ℕ) : Type :=
  BoundedContinuousFunction
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    ℝ

/-- Canonical L2 representative of a bounded-continuous joint observable under
the genuine ground-state joint probability law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (O : PeriodicHypercubicEvenSpecialUnitaryGroundStateJointBCF H N) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  BoundedContinuousFunction.toLp 2
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta)
    ℝ O

/-- Bounded-continuous representatives are dense in the genuine ground-state
joint real L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF_denseRange
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    DenseRange
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
        H N hN beta hbeta) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
  ] using
    (BoundedContinuousFunction.toLp_denseRange
      ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)
      ℝ
      (p := (2 : ℝ≥0∞))
      (by norm_num))

/-- Any continuous scalar majorant proved on every bounded-continuous
representative controls the genuine normalized sweep-stage profile energy on
the whole joint L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_of_boundedContinuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (majorant :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta → ℝ)
    (hMajorant : Continuous majorant)
    (hBCF :
      ∀ O : PeriodicHypercubicEvenSpecialUnitaryGroundStateJointBCF H N,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
              H N hN beta hbeta O) ≤
          majorant
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
              H N hN beta hbeta O)) :
    ∀ f,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
          H N hN beta hbeta f ≤
        majorant f := by
  let p :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta → Prop :=
    fun f =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
          H N hN beta hbeta f ≤
        majorant f
  intro f
  apply DenseRange.induction_on
    (p := p)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF_denseRange
      H N hN beta hbeta)
    f
  · simpa [p] using
      isClosed_le
        (continuous_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
          H N hN beta hbeta)
        hMajorant
  · intro O
    simpa [p] using hBCF O

/-- Bounded-continuous stagewise pointwise oscillation witnesses may remain
entirely pointwise.  If only their final normalized oscillation energy is
bounded by a continuous scalar majorant, that majorant controls the profile
energy on the full joint L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_of_boundedContinuous_oscillationEnergyMajorant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (majorant :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta → ℝ)
    (hMajorant : Continuous majorant)
    (hBCFOsc :
      ∀ O : PeriodicHypercubicEvenSpecialUnitaryGroundStateJointBCF H N,
        ∃ delta : PeriodicHypercubicEvenSpatialSliceLink H → ℝ,
          (∀ e, 0 ≤ delta e) ∧
          PeriodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageConcreteOscillationProfileBoundedBy
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
              H N hN beta hbeta O)
            delta ∧
          periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy
              H delta ≤
            majorant
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
                H N hN beta hbeta O)) :
    ∀ f,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
          H N hN beta hbeta f ≤
        majorant f := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_of_boundedContinuous
      H N hN beta hbeta majorant hMajorant
  intro O
  rcases hBCFOsc O with ⟨delta, hdelta, hOsc, hEnergy⟩
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_oscillationEnergy
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
        H N hN beta hbeta O)
      delta hdelta hOsc).trans hEnergy

end

end MathlibAnalytic
end MGAP4D
