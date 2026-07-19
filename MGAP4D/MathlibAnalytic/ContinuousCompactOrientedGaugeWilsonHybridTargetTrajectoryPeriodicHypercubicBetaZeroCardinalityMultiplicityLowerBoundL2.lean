import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroFiniteSetProductModeL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroJointSectorProjectorIdempotentOrthogonalL2
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Nonzero vectors lying in pairwise distinct exact joint sectors of a finite
commuting family are linearly independent.  The canonical projector with label
`s` extracts exactly the `s`-coefficient from any finite linear combination. -/
theorem continuousLinearMap_jointSectorProfileFamily_linearIndependent
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (v : Finset ι → V)
    (hMem : ∀ s : Finset ι,
      v s ∈ continuousLinearMapJointSectorSubmoduleL2 Q s)
    (hNe : ∀ s : Finset ι, v s ≠ 0) :
    LinearIndependent ℝ v := by
  classical
  rw [Fintype.linearIndependent_iffₛ]
  intro c d hSum s
  let P : V →L[ℝ] V :=
    continuousLinearMapJointSectorProjectorL2 Q s hComm
  have hApply :
      P (∑ t, c t • v t) = P (∑ t, d t • v t) := by
    exact congrArg (fun f : V => P f) hSum
  have hLeft :
      P (∑ t, c t • v t) = c s • v s := by
    rw [map_sum]
    calc
      (∑ t, P (c t • v t)) = P (c s • v s) := by
        refine Fintype.sum_eq_single s ?_
        intro t hts
        rw [map_smul]
        have hZero : P (v t) = 0 := by
          dsimp [P]
          exact
            continuousLinearMap_jointSectorProjectorL2_apply_eq_zero_of_mem_jointSectorSubmoduleL2_of_ne
              Q s t hComm (Ne.symm hts) (hMem t)
        rw [hZero, smul_zero]
      _ = c s • v s := by
        rw [map_smul]
        have hSelf : P (v s) = v s := by
          dsimp [P]
          exact
            continuousLinearMap_jointSectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
              Q s hComm (hMem s)
        rw [hSelf]
  have hRight :
      P (∑ t, d t • v t) = d s • v s := by
    rw [map_sum]
    calc
      (∑ t, P (d t • v t)) = P (d s • v s) := by
        refine Fintype.sum_eq_single s ?_
        intro t hts
        rw [map_smul]
        have hZero : P (v t) = 0 := by
          dsimp [P]
          exact
            continuousLinearMap_jointSectorProjectorL2_apply_eq_zero_of_mem_jointSectorSubmoduleL2_of_ne
              Q s t hComm (Ne.symm hts) (hMem t)
        rw [hZero, smul_zero]
      _ = d s • v s := by
        rw [map_smul]
        have hSelf : P (v s) = v s := by
          dsimp [P]
          exact
            continuousLinearMap_jointSectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
              Q s hComm (hMem s)
        rw [hSelf]
  have hCoeff : c s • v s = d s • v s := by
    calc
      c s • v s = P (∑ t, c t • v t) := hLeft.symm
      _ = P (∑ t, d t • v t) := hApply
      _ = d s • v s := hRight
  exact smul_left_injective ℝ (hNe s) hCoeff

/-- The actual finite-set centered-product modes, indexed by all subsets of the
324 physical links, are linearly independent. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2_linearIndependent :
    LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 := by
  classical
  exact
    continuousLinearMap_jointSectorProfileFamily_linearIndependent
      (Q := fun edge :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
            edge)
      (fun target source f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
          target source f)
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_finiteSetProductModeL2_mem_fluctuationJointSector
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2_ne_zero

/-- Index type of all selected physical-link sets with cardinality exactly `k`. -/
abbrev periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex
    (k : ℕ) :=
  {s : Finset
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge //
    s.card = k}

/-- The centered-product mode family restricted to cardinality `k`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2
    (k : ℕ)
    (s : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex k) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s.1

/-- The cardinality-`k` product-mode index has exactly `choose 324 k` elements. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex_card_eq_choose_324
    (k : ℕ) :
    Fintype.card
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex k) =
      Nat.choose 324 k := by
  classical
  simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
    using
      (Fintype.card_finset_len
        (α :=
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
        k)

/-- For every `k`, the `choose 324 k` actual centered-product modes of
cardinality `k` are linearly independent. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2_linearIndependent
    (k : ℕ) :
    LinearIndependent ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k) := by
  classical
  have hAll :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2_linearIndependent
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2,
    Function.comp_def]
    using
      hAll.comp
        (fun s :
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex k =>
            s.1)
        Subtype.val_injective

/-- Every member of the cardinality-`k` product-mode family is nonzero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2_ne_zero
    (k : ℕ)
    (s : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex k) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s ≠ 0 := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2_ne_zero
      s.1

/-- The actual cardinality projector `E_k` fixes every member of the
cardinality-`k` independent product-mode family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_cardinalityProductMode_eq
    (k : ℕ)
    (s : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex k) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        k
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s := by
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2,
    s.2]
    using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_card_apply_finiteSetProductMode_eq
        s.1

/-- Every cardinality-`k` product mode is an actual heat-bath Hamiltonian
eigenvector with eigenvalue `k`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_cardinalityProductMode_eq
    (k : ℕ)
    (s : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex k) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s) =
      (k : ℝ) •
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s := by
  have hSector :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_finiteSetProductModeL2_mem_fluctuationJointSector
      s.1
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2,
    s.2]
    using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_eq_card_smul_of_mem_fluctuationJointSector
        s.1 hSector

/-- Compact receipt: the actual eigenvalue-`k` sector contains a linearly
independent family of `choose 324 k` nonzero vectors, all fixed by `E_k`. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityMultiplicityLowerBoundL2Receipt :
    Prop :=
  ∀ k : ℕ,
    Fintype.card
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex k) =
      Nat.choose 324 k ∧
    LinearIndependent ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k) ∧
    ∀ s : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex k,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          k
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s) =
        (k : ℝ) •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2 k s

/-- The binomial multiplicity lower-bound receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityMultiplicityLowerBoundL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityMultiplicityLowerBoundL2Receipt := by
  intro k
  refine ⟨
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeIndex_card_eq_choose_324
      k,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2_linearIndependent
      k,
    ?_⟩
  intro s
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityProductModeL2_ne_zero
      k s,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_cardinalityProductMode_eq
      k s,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_cardinalityProductMode_eq
      k s⟩

end

end MathlibAnalytic
end MGAP4D
