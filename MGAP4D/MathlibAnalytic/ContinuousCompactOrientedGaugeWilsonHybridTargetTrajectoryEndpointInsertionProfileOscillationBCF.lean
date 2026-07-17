import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointInsertionProfileSeparationBCF
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- A continuous real-valued function on a nonempty compact space realizes both
ends of its range.  The equalities are stated using `sInf` and `sSup`, while the
last two fields give the corresponding pointwise bounds. -/
private theorem compact_continuous_real_range_extrema
    {α : Type*}
    [TopologicalSpace α]
    [CompactSpace α]
    [Nonempty α]
    (f : α → ℝ)
    (hf : Continuous f) :
    ∃ xmin xmax : α,
      sInf (Set.range f) = f xmin ∧
      sSup (Set.range f) = f xmax ∧
      (∀ x : α, f xmin ≤ f x) ∧
      (∀ x : α, f x ≤ f xmax) := by
  rcases isCompact_univ.exists_sInf_image_eq_and_le
      Set.univ_nonempty hf.continuousOn with
    ⟨xmin, -, hminEq, hmin⟩
  rcases isCompact_univ.exists_sSup_image_eq_and_ge
      Set.univ_nonempty hf.continuousOn with
    ⟨xmax, -, hmaxEq, hmax⟩
  refine ⟨xmin, xmax, ?_, ?_, ?_, ?_⟩
  · simpa only [Set.image_univ] using hminEq
  · simpa only [Set.image_univ] using hmaxEq
  · intro x
    exact hmin x (Set.mem_univ x)
  · intro x
    exact hmax x (Set.mem_univ x)

/-- For two continuous real profiles on the same nonempty compact carrier,
uniform separation obtained by fixing two values of the first profile is
exactly strict domination of the second range oscillation by the first. -/
private theorem compact_continuous_initial_profile_separation_iff_range_oscillation_lt
    {α : Type*}
    [TopologicalSpace α]
    [CompactSpace α]
    [Nonempty α]
    (I F : α → ℝ)
    (hI : Continuous I)
    (hF : Continuous F) :
    (∃ gLower gUpper : α,
      ∃ a b : ℝ,
        a < b ∧
        (∀ h : α, I gLower - F h ≤ a) ∧
        (∀ h : α, b ≤ I gUpper - F h)) ↔
      sSup (Set.range F) - sInf (Set.range F) <
        sSup (Set.range I) - sInf (Set.range I) := by
  rcases compact_continuous_real_range_extrema I hI with
    ⟨iMin, iMax, hIMinEq, hIMaxEq, hIMin, hIMax⟩
  rcases compact_continuous_real_range_extrema F hF with
    ⟨fMin, fMax, hFMinEq, hFMaxEq, hFMin, hFMax⟩
  constructor
  · rintro ⟨gLower, gUpper, a, b, hab, hLower, hUpper⟩
    have hLowerAtMin := hLower fMin
    have hUpperAtMax := hUpper fMax
    have hIMinLower := hIMin gLower
    have hIUpperMax := hIMax gUpper
    rw [hFMaxEq, hFMinEq, hIMaxEq, hIMinEq]
    linarith
  · intro hOsc
    rw [hFMaxEq, hFMinEq, hIMaxEq, hIMinEq] at hOsc
    refine ⟨iMin, iMax, I iMin - F fMin, I iMax - F fMax, ?_, ?_, ?_⟩
    · linarith
    · intro h
      have hh := hFMin h
      linarith
    · intro h
      have hh := hFMax h
      linarith

/-- For two continuous real profiles on the same nonempty compact carrier,
uniform separation obtained by fixing two values of the second profile is
exactly strict domination of the first range oscillation by the second. -/
private theorem compact_continuous_final_profile_separation_iff_range_oscillation_lt
    {α : Type*}
    [TopologicalSpace α]
    [CompactSpace α]
    [Nonempty α]
    (I F : α → ℝ)
    (hI : Continuous I)
    (hF : Continuous F) :
    (∃ gLower gUpper : α,
      ∃ a b : ℝ,
        a < b ∧
        (∀ h : α, I h - F gLower ≤ a) ∧
        (∀ h : α, b ≤ I h - F gUpper)) ↔
      sSup (Set.range I) - sInf (Set.range I) <
        sSup (Set.range F) - sInf (Set.range F) := by
  rcases compact_continuous_real_range_extrema I hI with
    ⟨iMin, iMax, hIMinEq, hIMaxEq, hIMin, hIMax⟩
  rcases compact_continuous_real_range_extrema F hF with
    ⟨fMin, fMax, hFMinEq, hFMaxEq, hFMin, hFMax⟩
  constructor
  · rintro ⟨gLower, gUpper, a, b, hab, hLower, hUpper⟩
    have hLowerAtMax := hLower iMax
    have hUpperAtMin := hUpper iMin
    have hFLowerMax := hFMax gLower
    have hFMinUpper := hFMin gUpper
    rw [hIMaxEq, hIMinEq, hFMaxEq, hFMinEq]
    linarith
  · intro hOsc
    rw [hIMaxEq, hIMinEq, hFMaxEq, hFMinEq] at hOsc
    refine ⟨fMax, fMin, I iMax - F fMax, I iMin - F fMin, ?_, ?_, ?_⟩
    · linarith
    · intro h
      have hh := hIMax h
      linarith
    · intro h
      have hh := hIMin h
      linarith

/-- Global range oscillation of the rank-zero endpoint insertion profile. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  let I :=
    C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
      target O z
  sSup (Set.range I) - sInf (Set.range I)

/-- Global range oscillation of the full-rank endpoint insertion profile. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  let F :=
    C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
      target O z
  sSup (Set.range F) - sInf (Set.range F)

/-- Initial insertion-profile separation is equivalent to strict domination of
the final insertion oscillation by the initial insertion oscillation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileSeparationWitnessBCF_iff_finalOscillation_lt_initialOscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileSeparationWitnessBCF
        target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
          target O z <
        C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
          target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileSeparationWitnessBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
  dsimp only
  exact compact_continuous_initial_profile_separation_iff_range_oscillation_lt
    _ _
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF_continuous
      C target O z)
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF_continuous
      C target O z)

/-- Final insertion-profile separation is equivalent to strict domination of
the initial insertion oscillation by the final insertion oscillation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileSeparationWitnessBCF_iff_initialOscillation_lt_finalOscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileSeparationWitnessBCF
        target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
          target O z <
        C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
          target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileSeparationWitnessBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
  dsimp only
  exact compact_continuous_final_profile_separation_iff_range_oscillation_lt
    _ _
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF_continuous
      C target O z)
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF_continuous
      C target O z)

/-- Endpoint insertion-profile separation is exactly inequality of the two
endpoint insertion oscillations. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_oscillation_ne
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF
        target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
          target O z ≠
        C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
          target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileSeparationWitnessBCF_iff_finalOscillation_lt_initialOscillation,
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileSeparationWitnessBCF_iff_initialOscillation_lt_finalOscillation]
  constructor
  · intro h
    rcases h with h | h
    · exact ne_of_gt h
    · exact ne_of_lt h
  · intro h
    rcases lt_or_gt_of_ne h with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- Unequal endpoint insertion oscillations produce nonempty open innovation
regions. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillation_ne_implies_open_region_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hOsc :
      C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
          target O z ≠
        C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
          target O z) :
    C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_implies_open_region_witness
      C target O z
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_oscillation_ne
        C target O z).mpr hOsc)

/-- Unequal endpoint insertion oscillations force positive fixed-fiber
conditional variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillation_ne_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hOsc :
      C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
          target O z ≠
        C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
          target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_implies_gap_pos
      C target O z
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_oscillation_ne
        C target O z).mpr hOsc)

/-- A non-null Gibbs-pair family on which the two endpoint insertion
oscillations are unequal. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∃ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
        target O z ≠
      C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
        target O z

/-- A non-null family with unequal endpoint insertion oscillations is exactly a
non-null family carrying insertion-profile separation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF_iff_fiberwise_separation_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF
        target O ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF
        target O := by
  constructor
  · intro hOsc
    exact hOsc.mono fun z hz =>
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_oscillation_ne
        C target O z).mpr hz
  · intro hWitness
    exact hWitness.mono fun z hz =>
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_oscillation_ne
        C target O z).mp hz

/-- A non-null family with unequal endpoint insertion oscillations forces a
positive global conditional-variance gap. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hOsc :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_gap_pos
      C target O
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF_iff_fiberwise_separation_witness
        C target O).mp hOsc)

/-- With positive native one-link energy, a non-null family with unequal
endpoint insertion oscillations forces the exact endpoint correlation ratio
below one. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF_implies_correlationRatio_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hOsc :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O < 1 := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_correlationRatio_lt_one
      C target O hNative
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF_iff_fiberwise_separation_witness
        C target O).mp hOsc)

/-- With positive native one-link energy, a non-null family with unequal
endpoint insertion oscillations produces a strict endpoint correlation factor. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF_implies_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hOsc :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF
        target O) :
    ∃ ρ : ℝ, ρ < 1 ∧
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_exists_strict_correlation_factor
      C target O hNative
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationNeBCF_iff_fiberwise_separation_witness
        C target O).mp hOsc)

end

end MathlibAnalytic
end MGAP4D
