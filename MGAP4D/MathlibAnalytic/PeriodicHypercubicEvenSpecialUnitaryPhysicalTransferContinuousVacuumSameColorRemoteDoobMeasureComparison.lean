import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumSameColorRemoteWeightHarnack
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasurePairwiseComparison
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
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
      H N hN beta hbeta
  let targetEdge := periodicHypercubicEvenSpatialSliceLinkEmbedding H target
  let sourceEdge := periodicHypercubicEvenSpatialSliceLinkEmbedding H source
  let raw := C.singleLinkConditionalMeasure A targetEdge
  let wh := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
    Omega (C.base.replaceLink (C.base.replaceLink A targetEdge g) sourceEdge h)
  let wk := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
    Omega (C.base.replaceLink (C.base.replaceLink A targetEdge g) sourceEdge k)
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
  have hNormal :
      C.singleLinkDoobConditionalMeasure Omega
          (C.base.replaceLink A sourceEdge h) targetEdge =
          doobWeightedMeasure raw wh ∧
        C.singleLinkDoobConditionalMeasure Omega
          (C.base.replaceLink A sourceEdge k) targetEdge =
          doobWeightedMeasure raw wk ∧
        (∀ g, wh g ≤ R * wk g ∧ wk g ≤ R * wh g) := by
    simpa [C, Omega, targetEdge, sourceEdge, raw, wh, wk, R] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColor_remoteDoob_normalForm_weight_harnack
        H N hN beta hbeta hColor hne A h k)
  have hR0 : R ≠ 0 := by
    apply ne_of_gt
    dsimp [R]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hRtop : R ≠ ∞ := by
    dsimp [R]
    exact ENNReal.ofReal_ne_top
  have hCmp :=
    doobWeightedMeasure_pairwise_le_mul_sq_of_pointwise_le_mul
      raw wh wk R hR0 hRtop
      (fun g => (hNormal.2.2 g).1)
      (fun g => (hNormal.2.2 g).2)
  change
    C.singleLinkDoobConditionalMeasure Omega
        (C.base.replaceLink A sourceEdge h) targetEdge ≤
      (R * R) •
        C.singleLinkDoobConditionalMeasure Omega
          (C.base.replaceLink A sourceEdge k) targetEdge ∧
    C.singleLinkDoobConditionalMeasure Omega
        (C.base.replaceLink A sourceEdge k) targetEdge ≤
      (R * R) •
        C.singleLinkDoobConditionalMeasure Omega
          (C.base.replaceLink A sourceEdge h) targetEdge
  constructor
  · calc
      C.singleLinkDoobConditionalMeasure Omega
          (C.base.replaceLink A sourceEdge h) targetEdge =
          doobWeightedMeasure raw wh := hNormal.1
      _ ≤ (R * R) • doobWeightedMeasure raw wk := hCmp.1
      _ = (R * R) •
          C.singleLinkDoobConditionalMeasure Omega
            (C.base.replaceLink A sourceEdge k) targetEdge := by
        exact congrArg (fun μ => (R * R) • μ) hNormal.2.1.symm
  · calc
      C.singleLinkDoobConditionalMeasure Omega
          (C.base.replaceLink A sourceEdge k) targetEdge =
          doobWeightedMeasure raw wk := hNormal.2.1
      _ ≤ (R * R) • doobWeightedMeasure raw wh := hCmp.2
      _ = (R * R) •
          C.singleLinkDoobConditionalMeasure Omega
            (C.base.replaceLink A sourceEdge h) targetEdge := by
        exact congrArg (fun μ => (R * R) • μ) hNormal.1.symm

end

end MathlibAnalytic
end MGAP4D
