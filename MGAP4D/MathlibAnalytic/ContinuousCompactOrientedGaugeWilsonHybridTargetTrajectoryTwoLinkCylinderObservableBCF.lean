import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- A concrete bounded continuous two-link cylinder observable.  It reads the
value at a distinguished target link together with the value at a distinct
source link and applies a bounded continuous kernel on the compact Gauge
square. -/
def ContinuousCompactOrientedGaugeWilsonSystem.twoLinkCylinderObservableBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ) :
    BoundedContinuousFunction C.base.Configuration ℝ := by
  let f : C.base.Configuration → ℝ :=
    fun A => Φ (A target, A source)
  have hf : Continuous f := by
    exact Φ.continuous.comp
      ((continuous_apply target).prodMk (continuous_apply source))
  exact BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩

@[simp]
theorem continuous_compact_oriented_twoLinkCylinderObservableBCF_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ)
    (A : C.base.Configuration) :
    C.twoLinkCylinderObservableBCF target source Φ A =
      Φ (A target, A source) := by
  rfl

/-- Target-section oscillation of the concrete two-link kernel after freezing
the source-link value. -/
def ContinuousCompactOrientedGaugeWilsonSystem.twoLinkCylinderTargetSectionOscillationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ)
    (s : C.base.Gauge) : ℝ :=
  sSup (Set.range (fun g : C.base.Gauge => Φ (g, s))) -
    sInf (Set.range (fun g : C.base.Gauge => Φ (g, s)))

/-- For a source link distinct from the updated target link, the rank-zero
insertion profile of the concrete cylinder observable is exactly the target
section of the kernel frozen at the rank-zero source background. -/
theorem continuous_compact_oriented_twoLinkCylinderObservableBCF_initialInsertionProfile_eq_section
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
        target (C.twoLinkCylinderObservableBCF target source Φ) z =
      fun g : C.base.Gauge =>
        Φ (g,
          (C.independentPairHybridConfiguration z.1 z.2 0) source) := by
  funext g
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
  simp [ContinuousCompactOrientedGaugeWilsonSystem.twoLinkCylinderObservableBCF,
    hSource]

/-- For a source link distinct from the updated target link, the full-rank
insertion profile of the concrete cylinder observable is exactly the target
section of the kernel frozen at the full-rank source background. -/
theorem continuous_compact_oriented_twoLinkCylinderObservableBCF_finalInsertionProfile_eq_section
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
        target (C.twoLinkCylinderObservableBCF target source Φ) z =
      fun g : C.base.Gauge =>
        Φ (g,
          (C.independentPairHybridConfiguration z.1 z.2
            (Fintype.card C.base.geometry.Edge)) source) := by
  funext g
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
  simp [ContinuousCompactOrientedGaugeWilsonSystem.twoLinkCylinderObservableBCF,
    hSource]

/-- The rank-zero insertion oscillation of the concrete two-link cylinder is
the target-section oscillation at the rank-zero source background. -/
theorem continuous_compact_oriented_twoLinkCylinderObservableBCF_initialInsertionOscillation_eq_sectionOscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
        target (C.twoLinkCylinderObservableBCF target source Φ) z =
      C.twoLinkCylinderTargetSectionOscillationBCF Φ
        ((C.independentPairHybridConfiguration z.1 z.2 0) source) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
    ContinuousCompactOrientedGaugeWilsonSystem.twoLinkCylinderTargetSectionOscillationBCF
  dsimp only
  rw [continuous_compact_oriented_twoLinkCylinderObservableBCF_initialInsertionProfile_eq_section
    C target source hSource Φ z]

/-- The full-rank insertion oscillation of the concrete two-link cylinder is
the target-section oscillation at the full-rank source background. -/
theorem continuous_compact_oriented_twoLinkCylinderObservableBCF_finalInsertionOscillation_eq_sectionOscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
        target (C.twoLinkCylinderObservableBCF target source Φ) z =
      C.twoLinkCylinderTargetSectionOscillationBCF Φ
        ((C.independentPairHybridConfiguration z.1 z.2
          (Fintype.card C.base.geometry.Edge)) source) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
    ContinuousCompactOrientedGaugeWilsonSystem.twoLinkCylinderTargetSectionOscillationBCF
  dsimp only
  rw [continuous_compact_oriented_twoLinkCylinderObservableBCF_finalInsertionProfile_eq_section
    C target source hSource Φ z]

/-- The endpoint oscillation margin of the concrete two-link cylinder is the
absolute mismatch between the two frozen target-section oscillations. -/
theorem continuous_compact_oriented_twoLinkCylinderObservableBCF_oscillationMargin_eq_sectionOscillationMismatch
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        target (C.twoLinkCylinderObservableBCF target source Φ) z =
      abs
        (C.twoLinkCylinderTargetSectionOscillationBCF Φ
            ((C.independentPairHybridConfiguration z.1 z.2 0) source) -
          C.twoLinkCylinderTargetSectionOscillationBCF Φ
            ((C.independentPairHybridConfiguration z.1 z.2
              (Fintype.card C.base.geometry.Edge)) source)) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
  rw [continuous_compact_oriented_twoLinkCylinderObservableBCF_initialInsertionOscillation_eq_sectionOscillation
      C target source hSource Φ z,
    continuous_compact_oriented_twoLinkCylinderObservableBCF_finalInsertionOscillation_eq_sectionOscillation
      C target source hSource Φ z]

/-- The original generic coordinate-update witness for the concrete two-link
cylinder is exactly inequality of the two frozen target-section oscillations. -/
theorem continuous_compact_oriented_twoLinkCylinderObservableBCF_coordinateUpdateWitness_iff_sectionOscillation_ne
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target (C.twoLinkCylinderObservableBCF target source Φ) z ↔
      C.twoLinkCylinderTargetSectionOscillationBCF Φ
          ((C.independentPairHybridConfiguration z.1 z.2 0) source) ≠
        C.twoLinkCylinderTargetSectionOscillationBCF Φ
          ((C.independentPairHybridConfiguration z.1 z.2
            (Fintype.card C.base.geometry.Edge)) source) := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_iff_oscillationMargin_pos]
  rw [continuous_compact_oriented_twoLinkCylinderObservableBCF_oscillationMargin_eq_sectionOscillationMismatch
    C target source hSource Φ z]
  rw [abs_pos, sub_ne_zero]

/-- Unequal frozen target-section oscillations force positive fixed-fiber
conditional variance for the concrete two-link cylinder observable. -/
theorem continuous_compact_oriented_twoLinkCylinderObservableBCF_sectionOscillation_ne_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hOsc :
      C.twoLinkCylinderTargetSectionOscillationBCF Φ
          ((C.independentPairHybridConfiguration z.1 z.2 0) source) ≠
        C.twoLinkCylinderTargetSectionOscillationBCF Φ
          ((C.independentPairHybridConfiguration z.1 z.2
            (Fintype.card C.base.geometry.Edge)) source)) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
      target (C.twoLinkCylinderObservableBCF target source Φ) z := by
  apply
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_pos_implies_gap_pos
      C target (C.twoLinkCylinderObservableBCF target source Φ) z
  rw [continuous_compact_oriented_twoLinkCylinderObservableBCF_oscillationMargin_eq_sectionOscillationMismatch
    C target source hSource Φ z]
  exact abs_pos.mpr (sub_ne_zero.mpr hOsc)

/-- A non-null Gibbs-pair family on which the concrete two-link cylinder has
unequal frozen target-section oscillations. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryTwoLinkCylinderSectionOscillationMismatchBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ) : Prop :=
  ∃ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    C.twoLinkCylinderTargetSectionOscillationBCF Φ
        ((C.independentPairHybridConfiguration z.1 z.2 0) source) ≠
      C.twoLinkCylinderTargetSectionOscillationBCF Φ
        ((C.independentPairHybridConfiguration z.1 z.2
          (Fintype.card C.base.geometry.Edge)) source)

/-- The concrete two-link section-mismatch family is exactly the abstract
positive oscillation-margin family for its associated configuration
observable. -/
theorem continuous_compact_oriented_twoLinkCylinderSectionOscillationMismatchBCF_iff_marginPos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ) :
    C.independentPairHybridTargetTrajectoryTwoLinkCylinderSectionOscillationMismatchBCF
        target source Φ ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF
        target (C.twoLinkCylinderObservableBCF target source Φ) := by
  constructor
  · intro hMismatch
    exact hMismatch.mono fun z hz => by
      rw [continuous_compact_oriented_twoLinkCylinderObservableBCF_oscillationMargin_eq_sectionOscillationMismatch
        C target source hSource Φ z]
      exact abs_pos.mpr (sub_ne_zero.mpr hz)
  · intro hMargin
    exact hMargin.mono fun z hz => by
      rw [continuous_compact_oriented_twoLinkCylinderObservableBCF_oscillationMargin_eq_sectionOscillationMismatch
        C target source hSource Φ z] at hz
      exact sub_ne_zero.mp (abs_pos.mp hz)

/-- A non-null concrete two-link section-mismatch family forces a positive
global conditional-variance gap. -/
theorem continuous_compact_oriented_twoLinkCylinderSectionOscillationMismatchBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ)
    (hMismatch :
      C.independentPairHybridTargetTrajectoryTwoLinkCylinderSectionOscillationMismatchBCF
        target source Φ) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target (C.twoLinkCylinderObservableBCF target source Φ) := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_implies_gap_pos
      C target (C.twoLinkCylinderObservableBCF target source Φ)
      ((continuous_compact_oriented_twoLinkCylinderSectionOscillationMismatchBCF_iff_marginPos
        C target source hSource Φ).mp hMismatch)

/-- With positive native one-link energy, a non-null concrete two-link
section-mismatch family forces the exact endpoint correlation ratio below one. -/
theorem continuous_compact_oriented_twoLinkCylinderSectionOscillationMismatchBCF_implies_correlationRatio_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target
        (C.twoLinkCylinderObservableBCF target source Φ))
    (hMismatch :
      C.independentPairHybridTargetTrajectoryTwoLinkCylinderSectionOscillationMismatchBCF
        target source Φ) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target
        (C.twoLinkCylinderObservableBCF target source Φ) < 1 := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_implies_correlationRatio_lt_one
      C target (C.twoLinkCylinderObservableBCF target source Φ) hNative
      ((continuous_compact_oriented_twoLinkCylinderSectionOscillationMismatchBCF_iff_marginPos
        C target source hSource Φ).mp hMismatch)

/-- With positive native one-link energy, a non-null concrete two-link
section-mismatch family produces a strict endpoint correlation factor. -/
theorem continuous_compact_oriented_twoLinkCylinderSectionOscillationMismatchBCF_implies_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (Φ : BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target
        (C.twoLinkCylinderObservableBCF target source Φ))
    (hMismatch :
      C.independentPairHybridTargetTrajectoryTwoLinkCylinderSectionOscillationMismatchBCF
        target source Φ) :
    ∃ ρ : ℝ, ρ < 1 ∧
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target (C.twoLinkCylinderObservableBCF target source Φ) ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target
          (C.twoLinkCylinderObservableBCF target source Φ) := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_implies_exists_strict_correlation_factor
      C target (C.twoLinkCylinderObservableBCF target source Φ) hNative
      ((continuous_compact_oriented_twoLinkCylinderSectionOscillationMismatchBCF_iff_marginPos
        C target source hSource Φ).mp hMismatch)

end

end MathlibAnalytic
end MGAP4D
