import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCurrentValueFixedBackgroundFiberL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateBackwardDirectMeanSplit
import Mathlib.Tactic

/-!
# Current-value localPart on the fixed-background source-pair fiber

PR #4822 puts the concrete target-law responses and final second-mean RMS
amplitudes in a source-specific L2 carrier at each fixed outer background A.

The exact source-only local term was already isolated much earlier by PR #4736:

  localMean_source(A).

For the dependent response assembler, this scalar must live in the same
source carrier as every target response for that source.  Since the
fixed-background source-pair law is a probability measure, the canonical lift
is simply the constant L2 vector with value localMean_source(A).

This file performs only that carrier lift and proves its norm exactly:

  ||localPart_A,source|| = |localMean_source(A)|.

Thus no localPart estimate is rebuilt.  The outer A-integration can later be
identified with the existing PR #4748/#4767 diagonal localMean energy chain.

No response coefficient, comparison constant, factor two, or finite-cardinality
factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

local instance currentValueSourcePairLocalPartSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance currentValueSourcePairLocalPartSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance currentValueSourcePairLocalPartSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance currentValueSourcePairLocalPartSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance currentValueSourcePairLocalPartSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance currentValueSourcePairLocalPartSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Current-value diagonal local mean at the outer background A.

This is only a short name for the PR #4736 source-only local term with the
reference parameters specialized to the current values of C. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
    H N hN beta hbeta source F C C distinguishedSource
    (C distinguishedSource) (C source) A

/-- Lift the current-value diagonal local mean to the same fixed-background
source-pair L2 carrier used by all target responses from that source. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCurrentValueFixedBackgroundSourcePairL2
      H N hN beta hbeta C A distinguishedSource source := by
  let μ :=
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
      H N hN beta hbeta C A distinguishedSource source
      (C distinguishedSource) (C source)
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
      H N hN beta hbeta C A distinguishedSource source F
  letI : IsProbabilityMeasure μ := by
    dsimp [μ,
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure]
    infer_instance
  exact
    (memLp_const q).toLp
      (fun _ :
        Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ => q)

/-- The localPart L2 vector is represented by the constant diagonal local mean
on the source-pair fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2_coeFn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    (fun uv =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source F uv) =ᵐ[
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
        H N hN beta hbeta C A distinguishedSource source
        (C distinguishedSource) (C source)]
      (fun _ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
          H N hN beta hbeta C A distinguishedSource source F) := by
  let μ :=
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
      H N hN beta hbeta C A distinguishedSource source
      (C distinguishedSource) (C source)
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
      H N hN beta hbeta C A distinguishedSource source F
  letI : IsProbabilityMeasure μ := by
    dsimp [μ,
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure]
    infer_instance
  change
    (fun uv =>
      ((memLp_const q).toLp
        (fun _ :
          Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ => q)) uv) =ᵐ[μ]
      (fun _ => q)
  exact (memLp_const q).coeFn_toLp

/-- Exact norm of the lifted localPart.  Probability normalization means no
fiber-mass factor appears. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2_norm_eq_abs
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source F‖ =
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
        H N hN beta hbeta C A distinguishedSource source F| := by
  let μ :=
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
      H N hN beta hbeta C A distinguishedSource source
      (C distinguishedSource) (C source)
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
      H N hN beta hbeta C A distinguishedSource source F
  letI : IsProbabilityMeasure μ := by
    dsimp [μ,
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure]
    infer_instance
  change
    ‖(memLp_const q).toLp
      (fun _ :
        Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ => q)‖ = |q|
  rw [MemLp.toLp_const]
  have hConst :=
    Lp.norm_const'
      (μ := μ)
      (p := (2 : ENNReal))
      (c := q)
      (by norm_num)
      (by norm_num)
  simpa [Real.norm_eq_abs] using hConst

/-- Squared form used by the outer localPart energy glue. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2_norm_sq_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source F‖ ^ 2 =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
        H N hN beta hbeta C A distinguishedSource source F) ^ 2 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2_norm_eq_abs]
  exact sq_abs _

end

end MGAP4D.MathlibAnalytic
