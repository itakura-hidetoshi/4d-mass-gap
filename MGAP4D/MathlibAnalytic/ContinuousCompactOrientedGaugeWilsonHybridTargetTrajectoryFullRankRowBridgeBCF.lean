import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryCanonicalOverlapGibbsBridgeBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridBoundaryResidualSourceOverlapPathEnergyBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- The physical source selected at the canonical rank of `target` is exactly
`target`. -/
@[simp]
theorem continuous_compact_oriented_hybridTargetTrajectorySourceAtRank_targetRank
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.hybridTargetTrajectorySourceAtRank target
        (C.canonicalEdgeOrder target).val = target := by
  simp [
    ContinuousCompactOrientedGaugeWilsonSystem.hybridTargetTrajectorySourceAtRank]

/-- At the target's own canonical hybrid step, changing the observable background
while reinserting the same target value creates no residual at all. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalBackgroundChangeBCF_targetRank_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (hm : (C.canonicalEdgeOrder target).val + 1 ≤ m)
    (x : (i : Finset.Iic m) → C.base.Gauge) :
    C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
        (fun r => C.independentPairHybridConfiguration A B r)
        target O m (C.canonicalEdgeOrder target).val x = 0 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
  simp [hm,
    continuous_compact_oriented_independentPairHybridConfiguration_rank_succ_eq_replaceLink]

/-- Consequently, the target-rank background-change square energy vanishes
exactly. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalBackgroundChangeEnergyBCF_targetRank_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (hm : (C.canonicalEdgeOrder target).val + 1 ≤ m) :
    C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF
        A B (fun r => C.independentPairHybridConfiguration A B r)
        target O m (C.canonicalEdgeOrder target).val = 0 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun x => by
    change
      (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
        (fun r => C.independentPairHybridConfiguration A B r)
        target O m (C.canonicalEdgeOrder target).val x) ^ 2 = (0 : ℝ)
    rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalBackgroundChangeBCF_targetRank_eq_zero
      C A B target O m hm x]
    simp

/-- Enumerating every valid canonical rank is exactly the same as summing the
source-overlap transport energy over every physical source link. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_sum_fullRank_eq_row
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
      C.independentPairHybridSourceOverlapTransportEnergyBCF
        target (C.hybridTargetTrajectorySourceAtRank target k) O) =
      C.independentPairHybridSourceOverlapTransportRowEnergyBCF target O := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportRowEnergyBCF
  rw [← Fin.sum_univ_eq_sum_range]
  simpa [
    ContinuousCompactOrientedGaugeWilsonSystem.hybridTargetTrajectorySourceAtRank]
    using
      (C.canonicalEdgeOrder.symm.bijective.sum_comp
        (fun source : C.base.geometry.Edge =>
          C.independentPairHybridSourceOverlapTransportEnergyBCF
            target source O))

/-- The target-rank summand in the full canonical source row vanishes exactly. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_targetRank_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridSourceOverlapTransportEnergyBCF
        target
        (C.hybridTargetTrajectorySourceAtRank target
          (C.canonicalEdgeOrder target).val)
        O = 0 := by
  simpa using
    continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_diagonal_zero
      C target O

/-- At full canonical length, the Gibbs-pair integrals of all fixed-left overlap
fibers sum exactly to the established all-source overlap row energy. -/
theorem continuous_compact_oriented_independentPairHybridCanonicalFixedLeftOverlapFiber_integral_sum_fullRank_eq_row
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
      ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
          target O k z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure)) =
      C.independentPairHybridSourceOverlapTransportRowEnergyBCF target O := by
  calc
    (∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
      ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
          target O k z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure)) =
      ∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
        C.independentPairHybridSourceOverlapTransportEnergyBCF
          target (C.hybridTargetTrajectorySourceAtRank target k) O := by
            symm
            exact
              continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_sum_eq_sum_integral_canonicalFixedLeftOverlapFiber
                C target O (Fintype.card C.base.geometry.Edge) le_rfl
    _ = C.independentPairHybridSourceOverlapTransportRowEnergyBCF target O :=
      continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_sum_fullRank_eq_row
        C target O

/-- The target-rank fixed-left overlap fiber has zero Gibbs-pair integral. -/
theorem continuous_compact_oriented_independentPairHybridCanonicalFixedLeftOverlapFiber_integral_targetRank_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ z : C.base.Configuration × C.base.Configuration,
      C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
        target O (C.canonicalEdgeOrder target).val z
      ∂(C.gibbsMeasure.prod C.gibbsMeasure)) = 0 := by
  have hPullback :=
    continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_eq_integral_canonicalFixedLeftOverlapFiber
      C target O (C.canonicalEdgeOrder target).val
      (C.canonicalEdgeOrder target).isLt
  rw [continuous_compact_oriented_hybridTargetTrajectorySourceAtRank_targetRank,
    continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_diagonal_zero]
    at hPullback
  exact hPullback.symm

/-- The complete canonical-rank source-overlap sum is exactly the already defined
left/right hybrid boundary residual source path energy. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_sum_fullRank_eq_boundaryResidualPath
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
      C.independentPairHybridSourceOverlapTransportEnergyBCF
        target (C.hybridTargetTrajectorySourceAtRank target k) O) =
      C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O := by
  calc
    (∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
      C.independentPairHybridSourceOverlapTransportEnergyBCF
        target (C.hybridTargetTrajectorySourceAtRank target k) O) =
      C.independentPairHybridSourceOverlapTransportRowEnergyBCF target O :=
        continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_sum_fullRank_eq_row
          C target O
    _ = C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O :=
      (continuous_compact_oriented_hybridBoundaryResidualSourceOverlapPathEnergyBCF_eq_row
        C target O).symm

/-- Therefore the full Gibbs-averaged fixed-left fiber budget is exactly the
hybrid boundary residual source-overlap path energy. -/
theorem continuous_compact_oriented_independentPairHybridCanonicalFixedLeftOverlapFiber_integral_sum_fullRank_eq_boundaryResidualPath
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
      ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
          target O k z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure)) =
      C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O := by
  calc
    (∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
      ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
          target O k z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure)) =
      C.independentPairHybridSourceOverlapTransportRowEnergyBCF target O :=
        continuous_compact_oriented_independentPairHybridCanonicalFixedLeftOverlapFiber_integral_sum_fullRank_eq_row
          C target O
    _ = C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O :=
      (continuous_compact_oriented_hybridBoundaryResidualSourceOverlapPathEnergyBCF_eq_row
        C target O).symm

end

end MathlibAnalytic
end MGAP4D
