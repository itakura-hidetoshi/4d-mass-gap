import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridPairProfileEnergyBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalVarianceBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteHybridPath

/-- At the rank of one coordinate, the next hybrid configuration is exactly the
current configuration with that one coordinate updated from the right endpoint. -/
theorem configuration_rank_succ_eq_update
    {ι X : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (order : ι ≃ Fin (Fintype.card ι))
    (A B : ι → X)
    (target : ι) :
    configuration order A B ((order target).val + 1) =
      Function.update
        (configuration order A B (order target).val)
        target (B target) := by
  funext i
  by_cases hi : i = target
  · subst i
    simp [configuration]
  · have hValNe : (order i).val ≠ (order target).val := by
      intro hVal
      apply hi
      exact order.injective (Fin.ext hVal)
    have hStep :
        (order i).val < (order target).val + 1 ↔
          (order i).val < (order target).val := by
      omega
    simp [configuration, hi, hStep]

/-- Before its canonical hybrid step, a coordinate still has its left-endpoint
value. -/
@[simp]
theorem configuration_rank_apply
    {ι X : Type*}
    [Fintype ι]
    (order : ι ≃ Fin (Fintype.card ι))
    (A B : ι → X)
    (target : ι) :
    configuration order A B (order target).val target = A target := by
  simp [configuration]

/-- After its canonical hybrid step, a coordinate has its right-endpoint value. -/
@[simp]
theorem configuration_rank_succ_apply
    {ι X : Type*}
    [Fintype ι]
    (order : ι ≃ Fin (Fintype.card ι))
    (A B : ι → X)
    (target : ι) :
    configuration order A B ((order target).val + 1) target = B target := by
  simp [configuration]

end FiniteHybridPath

/-- One canonical compact-Haar hybrid step is exactly one physical-link
replacement. -/
theorem continuous_compact_oriented_independentPairHybridConfiguration_rank_succ_eq_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridConfiguration A B
        ((C.canonicalEdgeOrder target).val + 1) =
      C.base.replaceLink
        (C.independentPairHybridConfiguration A B
          (C.canonicalEdgeOrder target).val)
        target (B target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridConfiguration
  simpa [CompactOrientedGaugeWilsonSystem.replaceLink] using
    (FiniteHybridPath.configuration_rank_succ_eq_update
      C.canonicalEdgeOrder A B target)

/-- The two endpoint configurations of one canonical hybrid step agree away
from the step's target link. -/
theorem continuous_compact_oriented_independentPairHybridConfiguration_rank_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.base.AgreeOffLink
      (C.independentPairHybridConfiguration A B
        ((C.canonicalEdgeOrder target).val + 1))
      (C.independentPairHybridConfiguration A B
        (C.canonicalEdgeOrder target).val)
      target := by
  intro source hSource
  rw [continuous_compact_oriented_independentPairHybridConfiguration_rank_succ_eq_replaceLink]
  simp [CompactOrientedGaugeWilsonSystem.replaceLink, hSource]

/-- The exact heat-bath projection is unchanged across one canonical hybrid
step, because the two configurations have the same off-target boundary. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_independentPairHybrid_rank_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjection target O
        (C.independentPairHybridConfiguration A B
          ((C.canonicalEdgeOrder target).val + 1)) =
      C.singleLinkHeatBathProjection target O
        (C.independentPairHybridConfiguration A B
          (C.canonicalEdgeOrder target).val) := by
  rw [continuous_compact_oriented_independentPairHybridConfiguration_rank_succ_eq_replaceLink]
  change C.singleLinkConditionalExpectation O
      (C.base.replaceLink
        (C.independentPairHybridConfiguration A B
          (C.canonicalEdgeOrder target).val)
        target (B target)) target =
    C.singleLinkConditionalExpectation O
      (C.independentPairHybridConfiguration A B
        (C.canonicalEdgeOrder target).val) target
  exact continuous_compact_oriented_singleLinkConditionalExpectation_replaceLink
    C O
    (C.independentPairHybridConfiguration A B
      (C.canonicalEdgeOrder target).val)
    target (B target)

/-- A canonical hybrid observable increment is exactly the observable change
under the corresponding physical-link replacement. -/
theorem continuous_compact_oriented_independentPairHybridIncrementBCF_eq_replaceLink_sub
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A B : C.base.Configuration) :
    C.independentPairHybridIncrementBCF target O (A, B) =
      O (C.base.replaceLink
          (C.independentPairHybridConfiguration A B
            (C.canonicalEdgeOrder target).val)
          target (B target)) -
        O (C.independentPairHybridConfiguration A B
          (C.canonicalEdgeOrder target).val) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridIncrementBCF
  dsimp
  rw [continuous_compact_oriented_independentPairHybridConfiguration_rank_succ_eq_replaceLink]

/-- Exact conditional-centering identity for one hybrid step: the increment is
the difference of two heat-bath fluctuations on the same off-target fiber. -/
theorem continuous_compact_oriented_independentPairHybridIncrementBCF_eq_fluctuation_sub
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A B : C.base.Configuration) :
    C.independentPairHybridIncrementBCF target O (A, B) =
      C.singleLinkHeatBathFluctuation target O
        (C.independentPairHybridConfiguration A B
          ((C.canonicalEdgeOrder target).val + 1)) -
      C.singleLinkHeatBathFluctuation target O
        (C.independentPairHybridConfiguration A B
          (C.canonicalEdgeOrder target).val) := by
  have hProjection :=
    continuous_compact_oriented_singleLinkHeatBathProjection_independentPairHybrid_rank_eq
      C A B target O
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridIncrementBCF
  dsimp
  simp only
    [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuation,
      Pi.sub_apply]
  rw [hProjection]
  ring

/-- Pointwise quadratic cost of one hybrid increment is bounded by the two
conditional-centered endpoint costs on its common off-target fiber. -/
theorem continuous_compact_oriented_independentPairHybridIncrementBCF_sq_le_two_centered_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A B : C.base.Configuration) :
    (C.independentPairHybridIncrementBCF target O (A, B)) ^ 2 ≤
      2 * (C.singleLinkHeatBathFluctuation target O
        (C.independentPairHybridConfiguration A B
          ((C.canonicalEdgeOrder target).val + 1))) ^ 2 +
      2 * (C.singleLinkHeatBathFluctuation target O
        (C.independentPairHybridConfiguration A B
          (C.canonicalEdgeOrder target).val)) ^ 2 := by
  rw [continuous_compact_oriented_independentPairHybridIncrementBCF_eq_fluctuation_sub]
  nlinarith [sq_nonneg
    (C.singleLinkHeatBathFluctuation target O
        (C.independentPairHybridConfiguration A B
          ((C.canonicalEdgeOrder target).val + 1)) +
      C.singleLinkHeatBathFluctuation target O
        (C.independentPairHybridConfiguration A B
          (C.canonicalEdgeOrder target).val))]

end

end MathlibAnalytic
end MGAP4D
