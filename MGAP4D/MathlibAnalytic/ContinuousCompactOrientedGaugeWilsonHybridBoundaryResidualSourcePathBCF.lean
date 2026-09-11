import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridBoundaryResamplingDiagonalSupportBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridSourceOverlapTransportEnergyBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace FiniteHybridPath

/-- Exact telescoping identity for an initial segment of a finite-coordinate
hybrid path.  No square or Cauchy estimate is taken at this layer. -/
theorem observable_configuration_sub_eq_sum_range_increment
    {ι X : Type*}
    [Fintype ι]
    (order : ι ≃ Fin (Fintype.card ι))
    (observable : (ι → X) → ℝ)
    (A B : ι → X)
    (m : ℕ) :
    observable (configuration order A B m) - observable A =
      ∑ k ∈ Finset.range m,
        (observable (configuration order A B (k + 1)) -
          observable (configuration order A B k)) := by
  let path : ℕ → ℝ := fun k => observable (configuration order A B k)
  have h := Finset.sum_range_sub path m
  simpa [path] using h.symm

end FiniteHybridPath

/-- The source link of left-path rank `k`, where `k` is strictly before the
canonical rank of `target`. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualLeftSourceAtRank
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (k : Fin (C.canonicalEdgeOrder target).val) :
    C.base.geometry.Edge :=
  C.canonicalEdgeOrder.symm
    ⟨k.val, lt_trans k.isLt (C.canonicalEdgeOrder target).isLt⟩

/-- The source link of right-path offset `j`, where the corresponding rank is
strictly after the canonical rank of `target`. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualRightSourceAtOffset
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (j : Fin
      (Fintype.card C.base.geometry.Edge -
        ((C.canonicalEdgeOrder target).val + 1))) :
    C.base.geometry.Edge :=
  C.canonicalEdgeOrder.symm
    ⟨(C.canonicalEdgeOrder target).val + 1 + j.val, by
      have ht := (C.canonicalEdgeOrder target).isLt
      have hj := j.isLt
      omega⟩

@[simp]
theorem continuous_compact_oriented_canonicalEdgeOrder_hybridBoundaryResidualLeftSourceAtRank_val
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (k : Fin (C.canonicalEdgeOrder target).val) :
    (C.canonicalEdgeOrder
      (C.hybridBoundaryResidualLeftSourceAtRank target k)).val = k.val := by
  simp [ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualLeftSourceAtRank]

@[simp]
theorem continuous_compact_oriented_canonicalEdgeOrder_hybridBoundaryResidualRightSourceAtOffset_val
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (j : Fin
      (Fintype.card C.base.geometry.Edge -
        ((C.canonicalEdgeOrder target).val + 1))) :
    (C.canonicalEdgeOrder
      (C.hybridBoundaryResidualRightSourceAtOffset target j)).val =
        (C.canonicalEdgeOrder target).val + 1 + j.val := by
  simp [ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualRightSourceAtOffset]

/-- Every left-path source is strictly before the target and hence is not the
target link. -/
theorem continuous_compact_oriented_hybridBoundaryResidualLeftSourceAtRank_rank_lt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (k : Fin (C.canonicalEdgeOrder target).val) :
    (C.canonicalEdgeOrder
      (C.hybridBoundaryResidualLeftSourceAtRank target k)).val <
        (C.canonicalEdgeOrder target).val := by
  simpa using k.isLt

/-- Every right-path source is strictly after the target and hence is not the
target link. -/
theorem continuous_compact_oriented_hybridBoundaryResidualRightSourceAtOffset_rank_gt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (j : Fin
      (Fintype.card C.base.geometry.Edge -
        ((C.canonicalEdgeOrder target).val + 1))) :
    (C.canonicalEdgeOrder target).val <
      (C.canonicalEdgeOrder
        (C.hybridBoundaryResidualRightSourceAtOffset target j)).val := by
  rw [continuous_compact_oriented_canonicalEdgeOrder_hybridBoundaryResidualRightSourceAtOffset_val]
  omega

/-- A left source-rank step is exactly the canonical hybrid endpoint pair used
by the source-overlap transport law. -/
theorem continuous_compact_oriented_independentPairHybridEndpointPairMap_leftSourceAtRank
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (k : Fin (C.canonicalEdgeOrder target).val)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridEndpointPairMap
        (C.hybridBoundaryResidualLeftSourceAtRank target k) z =
      (C.independentPairHybridConfiguration z.1 z.2 k.val,
        C.independentPairHybridConfiguration z.1 z.2 (k.val + 1)) := by
  simp
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMap]

/-- A right source-offset step is exactly the canonical hybrid endpoint pair
used by the source-overlap transport law. -/
theorem continuous_compact_oriented_independentPairHybridEndpointPairMap_rightSourceAtOffset
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (j : Fin
      (Fintype.card C.base.geometry.Edge -
        ((C.canonicalEdgeOrder target).val + 1)))
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridEndpointPairMap
        (C.hybridBoundaryResidualRightSourceAtOffset target j) z =
      (C.independentPairHybridConfiguration z.1 z.2
          ((C.canonicalEdgeOrder target).val + 1 + j.val),
        C.independentPairHybridConfiguration z.1 z.2
          (((C.canonicalEdgeOrder target).val + 1 + j.val) + 1)) := by
  simp
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMap]

/-- Exact left source-path representation from the first genuine Gibbs endpoint
to the actual hybrid pre-endpoint.  Only source ranks strictly below `target`
appear, and no square estimate is used. -/
theorem continuous_compact_oriented_independentPairHybridPreEndpoint_sub_first_eq_sum_leftSourceIncrements
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    O (C.independentPairHybridPreEndpointMap target z) - O z.1 =
      ∑ k : Fin (C.canonicalEdgeOrder target).val,
        C.independentPairHybridIncrementBCF
          (C.hybridBoundaryResidualLeftSourceAtRank target k) O z := by
  let r := (C.canonicalEdgeOrder target).val
  have hPath :=
    FiniteHybridPath.observable_configuration_sub_eq_sum_range_increment
      C.canonicalEdgeOrder O z.1 z.2 r
  have hReindex :
      (∑ k : Fin r,
        C.independentPairHybridIncrementBCF
          (C.hybridBoundaryResidualLeftSourceAtRank target k) O z) =
        ∑ k ∈ Finset.range r,
          (O (C.independentPairHybridConfiguration z.1 z.2 (k + 1)) -
            O (C.independentPairHybridConfiguration z.1 z.2 k)) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp
      [r,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridIncrementBCF,
        ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualLeftSourceAtRank,
        Finset.mem_range.mp hk]
  rw [hReindex]
  simpa
    [r,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMap]
    using hPath

/-- Exact right source-path representation from the actual hybrid post-endpoint
to the second genuine Gibbs endpoint.  Only source ranks strictly above
`target` appear, and no square estimate is used. -/
theorem continuous_compact_oriented_second_sub_independentPairHybridPostEndpoint_eq_sum_rightSourceIncrements
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    O z.2 - O (C.independentPairHybridPostEndpointMap target z) =
      ∑ j : Fin
        (Fintype.card C.base.geometry.Edge -
          ((C.canonicalEdgeOrder target).val + 1)),
        C.independentPairHybridIncrementBCF
          (C.hybridBoundaryResidualRightSourceAtOffset target j) O z := by
  let r := (C.canonicalEdgeOrder target).val
  let n := Fintype.card C.base.geometry.Edge - (r + 1)
  have ht := (C.canonicalEdgeOrder target).isLt
  have hEnd : r + 1 + n = Fintype.card C.base.geometry.Edge := by
    dsimp [n]
    omega
  let path : ℕ → ℝ := fun j =>
    O (C.independentPairHybridConfiguration z.1 z.2 (r + 1 + j))
  have hTel := Finset.sum_range_sub path n
  have hRange :
      (∑ j ∈ Finset.range n,
        (O (C.independentPairHybridConfiguration z.1 z.2
            ((r + 1 + j) + 1)) -
          O (C.independentPairHybridConfiguration z.1 z.2
            (r + 1 + j)))) =
        O z.2 - O (C.independentPairHybridPostEndpointMap target z) := by
    dsimp [path] at hTel
    rw [hEnd,
      continuous_compact_oriented_independentPairHybridConfiguration_card] at hTel
    simpa
      [r,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMap,
        Nat.add_assoc]
      using hTel
  have hReindex :
      (∑ j : Fin n,
        C.independentPairHybridIncrementBCF
          (C.hybridBoundaryResidualRightSourceAtOffset target j) O z) =
        ∑ j ∈ Finset.range n,
          (O (C.independentPairHybridConfiguration z.1 z.2
              ((r + 1 + j) + 1)) -
            O (C.independentPairHybridConfiguration z.1 z.2
              (r + 1 + j))) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp
      [r, n,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridIncrementBCF,
        ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualRightSourceAtOffset,
        Finset.mem_range.mp hj,
        Nat.add_assoc]
  rw [hReindex]
  exact hRange.symm

end

end MathlibAnalytic
end MGAP4D
