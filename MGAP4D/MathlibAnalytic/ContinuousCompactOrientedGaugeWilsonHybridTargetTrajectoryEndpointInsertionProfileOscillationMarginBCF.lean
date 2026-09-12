import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointInsertionProfileOscillationBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- The absolute mismatch between the rank-zero and full-rank endpoint
insertion-profile oscillations. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  abs
    (C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
        target O z -
      C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
        target O z)

/-- The endpoint insertion-profile oscillation margin is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    0 ≤
      C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
  exact abs_nonneg _

/-- The oscillation margin is positive exactly when the two endpoint
insertion-profile oscillations are unequal. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_pos_iff_oscillation_ne
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    0 <
        C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
          target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
          target O z ≠
        C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
          target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
  rw [abs_pos, sub_ne_zero]

/-- The oscillation margin vanishes exactly when the two endpoint insertion
oscillations agree. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_eq_zero_iff_oscillation_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        target O z = 0 ↔
      C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
          target O z =
        C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
          target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
  rw [abs_eq_zero, sub_eq_zero]

/-- Endpoint insertion-profile separation is exactly positivity of the absolute
oscillation margin. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_oscillationMargin_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF
        target O z ↔
      0 <
        C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
          target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_oscillation_ne
      C target O z).trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_pos_iff_oscillation_ne
        C target O z).symm

/-- Equivalently, the original generic coordinate-update witness is exactly
positivity of the endpoint insertion-profile oscillation margin. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_iff_oscillationMargin_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target O z ↔
      0 <
        C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
          target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_iff_insertion_profile_witness
      C target O z).trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_oscillationMargin_pos
        C target O z)

/-- Positive endpoint insertion-profile oscillation margin produces nonempty
open innovation regions. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_pos_implies_open_region_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hMargin :
      0 <
        C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
          target O z) :
    C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_implies_open_region_witness
      C target O z
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_oscillationMargin_pos
        C target O z).mpr hMargin)

/-- Positive endpoint insertion-profile oscillation margin forces positive
fixed-fiber conditional variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_pos_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hMargin :
      0 <
        C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
          target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_implies_gap_pos
      C target O z
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_oscillationMargin_pos
        C target O z).mpr hMargin)

/-- A non-null Gibbs-pair family on which the endpoint insertion-profile
oscillation margin is positive. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∃ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    0 <
      C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        target O z

/-- Positivity of the oscillation margin on a non-null Gibbs-pair family is
exactly the previously defined non-null oscillation-inequality condition. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_iff_oscillationNe
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF
        target O ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF
        target O := by
  constructor
  · intro hMargin
    exact hMargin.mono fun z hz =>
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_pos_iff_oscillation_ne
        C target O z).mp hz
  · intro hOsc
    exact hOsc.mono fun z hz =>
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_pos_iff_oscillation_ne
        C target O z).mpr hz

/-- A non-null positive-margin family is exactly a non-null family carrying
endpoint insertion-profile separation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_iff_fiberwise_separation_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF
        target O ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF
        target O := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_iff_oscillationNe
      C target O).trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF_iff_fiberwise_separation_witness
        C target O)

/-- An explicit positive lower bound for the oscillation margin on a non-null
Gibbs-pair family.  At this level the lower bound may still depend on the finite
volume, target link, and observable. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧
      ∃ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
        δ ≤
          C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
            target O z

/-- A positive lower-bound witness implies positivity of the oscillation margin
on a non-null Gibbs-pair family. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF_implies_margin_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hLower :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF
      target O := by
  rcases hLower with ⟨δ, hδ, hFamily⟩
  exact hFamily.mono fun _ hz => lt_of_lt_of_le hδ hz

/-- A non-null positive-margin family forces a positive global
conditional-variance gap. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hMargin :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_gap_pos
      C target O
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_iff_fiberwise_separation_witness
        C target O).mp hMargin)

/-- An explicit positive oscillation-margin lower bound on a non-null family
forces a positive global conditional-variance gap. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hLower :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_implies_gap_pos
      C target O
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF_implies_margin_pos
        C target O hLower)

/-- With positive native one-link energy, a non-null positive-margin family
forces the exact endpoint correlation ratio below one. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_implies_correlationRatio_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hMargin :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O < 1 := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_correlationRatio_lt_one
      C target O hNative
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_iff_fiberwise_separation_witness
        C target O).mp hMargin)

/-- With positive native one-link energy, an explicit positive oscillation-margin
lower bound on a non-null family forces the exact endpoint correlation ratio
below one. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF_implies_correlationRatio_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hLower :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O < 1 := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_implies_correlationRatio_lt_one
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF_implies_margin_pos
        C target O hLower)

/-- With positive native one-link energy, a non-null positive-margin family
produces a strict endpoint correlation factor. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_implies_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hMargin :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF
        target O) :
    ∃ ρ : ℝ, ρ < 1 ∧
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_exists_strict_correlation_factor
      C target O hNative
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_iff_fiberwise_separation_witness
        C target O).mp hMargin)

/-- With positive native one-link energy, an explicit positive oscillation-margin
lower bound on a non-null family produces a strict endpoint correlation factor. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF_implies_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hLower :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF
        target O) :
    ∃ ρ : ℝ, ρ < 1 ∧
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_implies_exists_strict_correlation_factor
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF_implies_margin_pos
        C target O hLower)

end

end MathlibAnalytic
end MGAP4D
