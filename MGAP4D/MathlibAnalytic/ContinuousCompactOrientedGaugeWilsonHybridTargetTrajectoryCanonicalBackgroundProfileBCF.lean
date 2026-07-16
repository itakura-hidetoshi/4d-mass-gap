import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryBackgroundChangeEnergyBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinVariationPropagation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridCenteredStepBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- The physical source link at canonical hybrid rank `k`.  The target fallback
only totalizes ranks beyond the finite edge set; all theorems below use valid
ranks. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.hybridTargetTrajectorySourceAtRank
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (k : ℕ) : C.base.geometry.Edge :=
  if h : k < Fintype.card C.base.geometry.Edge then
    C.canonicalEdgeOrder.symm ⟨k, h⟩
  else target

@[simp]
theorem continuous_compact_oriented_canonicalEdgeOrder_hybridTargetTrajectorySourceAtRank_val_of_lt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (k : ℕ)
    (hk : k < Fintype.card C.base.geometry.Edge) :
    (C.canonicalEdgeOrder
      (C.hybridTargetTrajectorySourceAtRank target k)).val = k := by
  simp [
    ContinuousCompactOrientedGaugeWilsonSystem.hybridTargetTrajectorySourceAtRank,
    hk]

/-- Consecutive canonical hybrid backgrounds agree away from the physical source
link whose canonical rank is `k`. -/
theorem continuous_compact_oriented_independentPairHybridCanonicalBackground_succ_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (k : ℕ)
    (hk : k < Fintype.card C.base.geometry.Edge) :
    C.base.AgreeOffLink
      (C.independentPairHybridConfiguration A B (k + 1))
      (C.independentPairHybridConfiguration A B k)
      (C.hybridTargetTrajectorySourceAtRank target k) := by
  simpa [
    ContinuousCompactOrientedGaugeWilsonSystem.hybridTargetTrajectorySourceAtRank,
    hk] using
    (continuous_compact_oriented_independentPairHybridConfiguration_rank_agreeOffLink
      C A B (C.hybridTargetTrajectorySourceAtRank target k))

/-- On canonical hybrid backgrounds, the explicit target-frozen background
change is bounded by the observable's variation at the corresponding physical
source link. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalBackgroundChangeBCF_abs_le_variation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (m k : ℕ)
    (hkm : k + 1 ≤ m)
    (hk : k < Fintype.card C.base.geometry.Edge)
    (x : (i : Finset.Iic m) → C.base.Gauge) :
    |C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
        (fun r => C.independentPairHybridConfiguration A B r)
        target O m k x| ≤
      P.variation (C.hybridTargetTrajectorySourceAtRank target k) := by
  let source := C.hybridTargetTrajectorySourceAtRank target k
  have hBackground : C.base.AgreeOffLink
      (C.independentPairHybridConfiguration A B (k + 1))
      (C.independentPairHybridConfiguration A B k)
      source := by
    simpa [source] using
      continuous_compact_oriented_independentPairHybridCanonicalBackground_succ_agreeOffLink
        C A B target k hk
  have hReplaced : C.base.AgreeOffLink
      (C.base.replaceLink
        (C.independentPairHybridConfiguration A B (k + 1)) target
        (x ⟨k + 1, Finset.mem_Iic.2 hkm⟩))
      (C.base.replaceLink
        (C.independentPairHybridConfiguration A B k) target
        (x ⟨k + 1, Finset.mem_Iic.2 hkm⟩))
      source :=
    compact_oriented_replaceLink_agreeOffLink
      C.base
      (C.independentPairHybridConfiguration A B (k + 1))
      (C.independentPairHybridConfiguration A B k)
      target source
      (x ⟨k + 1, Finset.mem_Iic.2 hkm⟩)
      hBackground
  have hVariation := P.variation_bound source
    (C.base.replaceLink
      (C.independentPairHybridConfiguration A B (k + 1)) target
      (x ⟨k + 1, Finset.mem_Iic.2 hkm⟩))
    (C.base.replaceLink
      (C.independentPairHybridConfiguration A B k) target
      (x ⟨k + 1, Finset.mem_Iic.2 hkm⟩))
    hReplaced
  simpa [source,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF,
    hkm, abs_sub_comm] using hVariation

/-- The canonical background-change square energy at one genuine source step is
bounded by the square of the corresponding observable variation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalBackgroundChangeEnergyBCF_le_variation_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (m k : ℕ)
    (hkm : k + 1 ≤ m)
    (hk : k < Fintype.card C.base.geometry.Edge) :
    C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF
        A B (fun r => C.independentPairHybridConfiguration A B r)
        target O m k ≤
      (P.variation (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2 := by
  let source := C.hybridTargetTrajectorySourceAtRank target k
  let μ := C.independentPairHybridTargetTrajectoryMeasure A B target m
  have hSquare : Integrable
      (fun x : (i : Finset.Iic m) → C.base.Gauge =>
        (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
          (fun r => C.independentPairHybridConfiguration A B r)
          target O m k x) ^ 2) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF_sq_integrable
        C A B (fun r => C.independentPairHybridConfiguration A B r)
        target O m k
  have hConst : Integrable
      (fun _ : (i : Finset.Iic m) → C.base.Gauge =>
        (P.variation source) ^ 2) μ :=
    integrable_const _
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF
  change (∫ x,
      (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
        (fun r => C.independentPairHybridConfiguration A B r)
        target O m k x) ^ 2 ∂μ) ≤ (P.variation source) ^ 2
  calc
    (∫ x,
        (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
          (fun r => C.independentPairHybridConfiguration A B r)
          target O m k x) ^ 2 ∂μ) ≤
      ∫ _x : (i : Finset.Iic m) → C.base.Gauge,
        (P.variation source) ^ 2 ∂μ := by
          apply integral_mono hSquare hConst
          intro x
          have hAbs :=
            continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalBackgroundChangeBCF_abs_le_variation
              C A B target O P m k hkm hk x
          have hBounds := abs_le.mp hAbs
          nlinarith [P.variation_nonneg source]
    _ = (P.variation source) ^ 2 := by simp

/-- Summing all canonical background-change energies along a finite prefix is
bounded by the corresponding finite source-variation square profile. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalBackgroundChangeEnergyBCF_sum_le_variation_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (m : ℕ)
    (hm : m ≤ Fintype.card C.base.geometry.Edge) :
    (∑ k ∈ Finset.range m,
      C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF
        A B (fun r => C.independentPairHybridConfiguration A B r)
        target O m k) ≤
      ∑ k ∈ Finset.range m,
        (P.variation (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2 := by
  apply Finset.sum_le_sum
  intro k hkRange
  have hkm : k + 1 ≤ m :=
    Nat.succ_le_iff.mpr (Finset.mem_range.mp hkRange)
  have hkCard : k < Fintype.card C.base.geometry.Edge :=
    lt_of_lt_of_le (Finset.mem_range.mp hkRange) hm
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalBackgroundChangeEnergyBCF_le_variation_sq
      C A B target O P m k hkm hkCard

/-- The canonical source-background endpoint trajectory energy is bounded by the
exact fixed-left overlap energies plus the observable-specific source variation
squares.  This is still a conditional fixed-pair trajectory statement, not the
hybrid boundary endpoint residual inequality. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalBackgroundEndpointTransportEnergyBCF_le_sum_overlap_add_variation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (m : ℕ)
    (hm : m ≤ Fintype.card C.base.geometry.Edge) :
    C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF
        A B (fun r => C.independentPairHybridConfiguration A B r)
        target O m ≤
      (m : ℝ) *
        ∑ k ∈ Finset.range m,
          (2 *
              C.singleLinkConditionalOverlapObservableTransportEnergyBCF
                (C.independentPairHybridConfiguration A B k)
                (C.independentPairHybridConfiguration A B (k + 1))
                (C.independentPairHybridConfiguration A B k)
                target O +
            2 *
              (P.variation
                (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2) := by
  calc
    C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF
        A B (fun r => C.independentPairHybridConfiguration A B r)
        target O m ≤
      (m : ℝ) *
        ∑ k ∈ Finset.range m,
          (2 *
              C.singleLinkConditionalOverlapObservableTransportEnergyBCF
                (C.independentPairHybridConfiguration A B k)
                (C.independentPairHybridConfiguration A B (k + 1))
                (C.independentPairHybridConfiguration A B k)
                target O +
            2 *
              C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF
                A B (fun r => C.independentPairHybridConfiguration A B r)
                target O m k) :=
      continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF_le_sum_overlap_add_backgroundChange
        C A B (fun r => C.independentPairHybridConfiguration A B r)
        target O m
    _ ≤ (m : ℝ) *
        ∑ k ∈ Finset.range m,
          (2 *
              C.singleLinkConditionalOverlapObservableTransportEnergyBCF
                (C.independentPairHybridConfiguration A B k)
                (C.independentPairHybridConfiguration A B (k + 1))
                (C.independentPairHybridConfiguration A B k)
                target O +
            2 *
              (P.variation
                (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro k hkRange
        have hkm : k + 1 ≤ m :=
          Nat.succ_le_iff.mpr (Finset.mem_range.mp hkRange)
        have hkCard : k < Fintype.card C.base.geometry.Edge :=
          lt_of_lt_of_le (Finset.mem_range.mp hkRange) hm
        have hBackground :=
          continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalBackgroundChangeEnergyBCF_le_variation_sq
            C A B target O P m k hkm hkCard
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left hBackground (by norm_num)) _
      · positivity

end

end MathlibAnalytic
end MGAP4D
