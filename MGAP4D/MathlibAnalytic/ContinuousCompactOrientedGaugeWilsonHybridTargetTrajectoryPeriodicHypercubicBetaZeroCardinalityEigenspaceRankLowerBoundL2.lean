import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityMultiplicityLowerBoundL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityProjectorRangeL2
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The cardinality projector also acts on the left of the full coordinate sum
with eigenvalue `k`.  This is the reverse-order companion to the previously
proved `H * E_k = k E_k` identity. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_mul_univ_sum_eq_natCast_smul
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (hk : k ≤ Fintype.card ι) :
    continuousLinearMapCardinalitySectorProjectorL2 Q k hComm *
        (∑ i : ι, Q i) =
      (k : ℝ) • continuousLinearMapCardinalitySectorProjectorL2 Q k hComm := by
  classical
  rw [continuousLinearMap_univ_sum_eq_weighted_cardinalitySectorProjectorsL2
    Q hIdempotent hComm]
  rw [Finset.mul_sum]
  calc
    (∑ j ∈ Finset.range (Fintype.card ι + 1),
        continuousLinearMapCardinalitySectorProjectorL2 Q k hComm *
          ((j : ℝ) • continuousLinearMapCardinalitySectorProjectorL2 Q j hComm)) =
      ∑ j ∈ Finset.range (Fintype.card ι + 1),
        (j : ℝ) •
          (if k = j then
            continuousLinearMapCardinalitySectorProjectorL2 Q k hComm
          else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_smul_comm]
      rw [continuousLinearMap_cardinalitySectorProjectorL2_mul_eq_ite
        Q k j hIdempotent hComm]
    _ = (k : ℝ) • continuousLinearMapCardinalitySectorProjectorL2 Q k hComm := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro j hj hjk
        simp [Ne.symm hjk]
      · intro hkNot
        exact
          (hkNot
            (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))).elim

/-- For a finite commuting idempotent family, the range of `E_k` is exactly the
ordinary eigenspace of the coordinate sum at eigenvalue `k`. -/
theorem continuousLinearMap_range_cardinalitySectorProjectorL2_eq_eigenspace
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (hk : k ≤ Fintype.card ι) :
    LinearMap.range
        (continuousLinearMapCardinalitySectorProjectorL2 Q k hComm).toLinearMap =
      Module.End.genEigenspace ((∑ i : ι, Q i).toLinearMap) (k : ℝ) 1 := by
  classical
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨g, rfl⟩
    rw [Module.End.mem_genEigenspace_one]
    have hOperator :=
      continuousLinearMap_univ_sum_mul_cardinalitySectorProjectorL2_eq_natCast_smul
        Q k hIdempotent hComm
    have hApply := congrArg
      (fun T : V →L[ℝ] V => T g) hOperator
    change
      (∑ i : ι, Q i)
          (continuousLinearMapCardinalitySectorProjectorL2 Q k hComm g) =
        (k : ℝ) •
          continuousLinearMapCardinalitySectorProjectorL2 Q k hComm g at hApply
    exact hApply
  · intro f hf
    rw [Module.End.mem_genEigenspace_one] at hf
    refine ⟨f, ?_⟩
    have hDecomp :
        (∑ j ∈ Finset.range (Fintype.card ι + 1),
          continuousLinearMapCardinalitySectorProjectorL2 Q j hComm f) = f := by
      have hOperator :=
        continuousLinearMap_sum_range_cardinalitySectorProjectorL2_eq_one
          Q hComm
      have hApply := congrArg
        (fun T : V →L[ℝ] V => T f) hOperator
      simpa using hApply
    have hOther :
        ∀ j ∈ Finset.range (Fintype.card ι + 1), j ≠ k →
          continuousLinearMapCardinalitySectorProjectorL2 Q j hComm f = 0 := by
      intro j hj hjk
      have hjle : j ≤ Fintype.card ι :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hReverseOperator :=
        continuousLinearMap_cardinalitySectorProjectorL2_mul_univ_sum_eq_natCast_smul
          Q j hIdempotent hComm hjle
      have hReverseApply := congrArg
        (fun T : V →L[ℝ] V => T f) hReverseOperator
      change
        continuousLinearMapCardinalitySectorProjectorL2 Q j hComm
            ((∑ i : ι, Q i) f) =
          (j : ℝ) •
            continuousLinearMapCardinalitySectorProjectorL2 Q j hComm f at hReverseApply
      have hMapEigen := congrArg
        (fun x : V =>
          continuousLinearMapCardinalitySectorProjectorL2 Q j hComm x) hf
      have hMapEigen' :
          continuousLinearMapCardinalitySectorProjectorL2 Q j hComm
              ((∑ i : ι, Q i) f) =
            (k : ℝ) •
              continuousLinearMapCardinalitySectorProjectorL2 Q j hComm f := by
        simpa using hMapEigen
      have hScalarEquality :
          (j : ℝ) •
              continuousLinearMapCardinalitySectorProjectorL2 Q j hComm f =
            (k : ℝ) •
              continuousLinearMapCardinalitySectorProjectorL2 Q j hComm f :=
        hReverseApply.symm.trans hMapEigen'
      have hCast : (j : ℝ) ≠ (k : ℝ) := by
        exact_mod_cast hjk
      have hSmulZero :
          ((j : ℝ) - (k : ℝ)) •
              continuousLinearMapCardinalitySectorProjectorL2 Q j hComm f = 0 := by
        rw [sub_smul, hScalarEquality, sub_self]
      exact
        (smul_eq_zero.mp hSmulZero).resolve_left
          (sub_ne_zero.mpr hCast)
    calc
      continuousLinearMapCardinalitySectorProjectorL2 Q k hComm f =
          ∑ j ∈ Finset.range (Fintype.card ι + 1),
            continuousLinearMapCardinalitySectorProjectorL2 Q j hComm f := by
        symm
        rw [Finset.sum_eq_single k]
        · exact hOther
        · intro hkNot
          exact
            (hkNot
              (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))).elim
      _ = f := hDecomp

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityEigenspaceRankEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityRangeEdgeDecidableEq

/-- The actual heat-bath eigenspace at the integer cardinality `k`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
    (k : ℕ) :
    Submodule ℝ
      (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
  Module.End.genEigenspace
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2.toLinearMap
    (k : ℝ) 1

/-- In the actual 324-link beta-zero system, the range of `E_k` is exactly the
heat-bath eigenspace at eigenvalue `k`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
    (k : ℕ)
    (hk : k ≤ 324) :
    LinearMap.range
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k).toLinearMap =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
        k := by
  classical
  have hkGeneric :
      k ≤ Fintype.card
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge := by
    simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
      using hk
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2]
    using
      (continuousLinearMap_range_cardinalitySectorProjectorL2_eq_eigenspace
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        k
        (fun edge f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
            edge f)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f)
        hkGeneric)

/-- The actual cardinality joint-sector sum is exactly the heat-bath eigenspace
at the matching integer eigenvalue. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_heatBathCardinalityEigenspaceL2
    (k : ℕ)
    (hk : k ≤ 324) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        k =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
        k := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_cardinalityJointSectorSumSubmoduleL2
      k).symm.trans
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
        k hk)

/-- The cardinality-`k` product mode bundled as a vector in the actual
cardinality joint-sector sum. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeInJointSectorSumL2
    (k : ℕ)
    (s : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex k) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      k := by
  refine ⟨
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s,
    ?_⟩
  have hRange :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s ∈
        LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k).toLinearMap := by
    exact ⟨
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_cardinalityProductMode_eq
        k s⟩
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_cardinalityJointSectorSumSubmoduleL2
    k] at hRange
  exact hRange

/-- The explicit cardinality-`k` product modes remain linearly independent when
bundled inside the actual cardinality joint-sector sum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeInJointSectorSumL2_linearIndependent
    (k : ℕ) :
    LinearIndependent ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeInJointSectorSumL2
        k) := by
  apply LinearIndependent.of_comp
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      k).subtype
  simpa [Function.comp_def,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeInJointSectorSumL2]
    using
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2_linearIndependent
        k

/-- The actual cardinality joint-sector sum has Cardinal rank at least
`choose 324 k`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_choose_324_le_rank_fluctuationCardinalityJointSectorSumSubmoduleL2
    (k : ℕ) :
    (Nat.choose 324 k : Cardinal) ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          k) := by
  have hRank :=
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeInJointSectorSumL2_linearIndependent
      k).cardinal_le_rank
  simpa [Cardinal.mk_fintype,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex_card_eq_choose_324]
    using hRank

/-- The range of the actual cardinality projector has Cardinal rank at least
`choose 324 k`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_choose_324_le_rank_range_fluctuationCardinalityProjectorL2
    (k : ℕ) :
    (Nat.choose 324 k : Cardinal) ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k).toLinearMap) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_cardinalityJointSectorSumSubmoduleL2
    k]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_choose_324_le_rank_fluctuationCardinalityJointSectorSumSubmoduleL2
      k

/-- For every `k ≤ 324`, the actual heat-bath eigenspace at eigenvalue `k` has
Cardinal rank at least `choose 324 k`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_choose_324_le_rank_heatBathCardinalityEigenspaceL2
    (k : ℕ)
    (hk : k ≤ 324) :
    (Nat.choose 324 k : Cardinal) ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          k) := by
  rw [← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_heatBathCardinalityEigenspaceL2
    k hk]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_choose_324_le_rank_fluctuationCardinalityJointSectorSumSubmoduleL2
      k

/-- Compact receipt for exact cardinality-eigenspace identification and the
binomial Cardinal-rank lower bound. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityEigenspaceRankLowerBoundL2Receipt :
    Prop :=
  ∀ k : ℕ, k ≤ 324 →
    LinearMap.range
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k).toLinearMap =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
        k ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        k =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
        k ∧
    (Nat.choose 324 k : Cardinal) ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          k) ∧
    (Nat.choose 324 k : Cardinal) ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k).toLinearMap) ∧
    (Nat.choose 324 k : Cardinal) ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          k)

/-- The exact eigenspace identification and binomial rank lower-bound receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityEigenspaceRankLowerBoundL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityEigenspaceRankLowerBoundL2Receipt := by
  intro k hk
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
      k hk,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_heatBathCardinalityEigenspaceL2
      k hk,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_choose_324_le_rank_fluctuationCardinalityJointSectorSumSubmoduleL2
      k,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_choose_324_le_rank_range_fluctuationCardinalityProjectorL2
      k,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_choose_324_le_rank_heatBathCardinalityEigenspaceL2
      k hk⟩

end

end MathlibAnalytic
end MGAP4D
