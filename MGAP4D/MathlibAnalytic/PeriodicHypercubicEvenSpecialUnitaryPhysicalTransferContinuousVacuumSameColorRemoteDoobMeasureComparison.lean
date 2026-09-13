import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumSameColorRemoteWeightHarnack
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumSameColorRemoteDoobMeasureComparisonSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance continuousVacuumSameColorRemoteDoobMeasureComparisonIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumSameColorRemoteDoobMeasureComparisonCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumSameColorRemoteDoobMeasureComparisonSecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumSameColorRemoteDoobMeasureComparisonMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumSameColorRemoteDoobMeasureComparisonBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumSameColorRemoteDoobMeasureComparisonSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Replacing one remote same-color spatial link changes the normalized
continuous-vacuum one-link Doob law at the target by at most the square of the
sharp weight-level Harnack factor `R = exp (8 * beta)`, in either direction.

The loss from `R` to `R^2` is exactly the normalization loss: one factor controls
the pointwise numerator and the second controls the relative normalizing mass.
No Doob independence, commutation, factorization, or color-block aggregation is
asserted here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColor_remoteDoob_pairwise_measure_harnack
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
    let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
    C.singleLinkDoobConditionalMeasure Omega
        (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) h)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) ≤
      (R * R) •
        C.singleLinkDoobConditionalMeasure Omega
          (C.base.replaceLink A
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) k)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) ∧
    C.singleLinkDoobConditionalMeasure Omega
        (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) k)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) ≤
      (R * R) •
        C.singleLinkDoobConditionalMeasure Omega
          (C.base.replaceLink A
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) h)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) := by
  dsimp only
  exact doobWeightedMeasure_pairwise_le_mul_sq_of_pointwise_le_mul

end

end MathlibAnalytic
end MGAP4D
