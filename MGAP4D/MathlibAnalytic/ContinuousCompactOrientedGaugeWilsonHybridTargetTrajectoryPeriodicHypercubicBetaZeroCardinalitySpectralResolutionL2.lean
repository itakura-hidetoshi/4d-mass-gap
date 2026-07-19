import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroJointSectorProjectorCompletenessL2
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The projector obtained by summing all canonical joint-sector projectors whose
labels have cardinality `k`. -/
noncomputable def continuousLinearMapCardinalitySectorProjectorL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    V →L[ℝ] V :=
  ∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
    continuousLinearMapJointSectorProjectorL2 Q s hComm

/-- Cardinality-sector projectors satisfy the Kronecker multiplication law. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_mul_eq_ite
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k l : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    continuousLinearMapCardinalitySectorProjectorL2 Q k hComm *
        continuousLinearMapCardinalitySectorProjectorL2 Q l hComm =
      if k = l then continuousLinearMapCardinalitySectorProjectorL2 Q k hComm else 0 := by
  classical
  by_cases hkl : k = l
  · subst l
    rw [if_pos rfl]
    unfold continuousLinearMapCardinalitySectorProjectorL2
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    calc
      (∑ t ∈ (Finset.univ : Finset ι).powersetCard k,
          continuousLinearMapJointSectorProjectorL2 Q s hComm *
            continuousLinearMapJointSectorProjectorL2 Q t hComm) =
          ∑ t ∈ (Finset.univ : Finset ι).powersetCard k,
            if s = t then continuousLinearMapJointSectorProjectorL2 Q s hComm else 0 := by
              apply Finset.sum_congr rfl
              intro t ht
              exact
                continuousLinearMap_jointSectorProjectorL2_mul_eq_ite
                  Q s t hIdempotent hComm
      _ = continuousLinearMapJointSectorProjectorL2 Q s hComm := by
        simp [hs]
  · rw [if_neg hkl]
    unfold continuousLinearMapCardinalitySectorProjectorL2
    rw [Finset.sum_mul_sum]
    apply Finset.sum_eq_zero
    intro s hs
    apply Finset.sum_eq_zero
    intro t ht
    apply
      continuousLinearMap_jointSectorProjectorL2_mul_eq_zero_of_ne
        Q s t hIdempotent hComm
    intro hst
    subst t
    have hscard : s.card = k :=
      (Finset.mem_powersetCard.mp hs).2
    have htcard : s.card = l :=
      (Finset.mem_powersetCard.mp ht).2
    exact hkl (hscard.symm.trans htcard)

/-- Every cardinality-sector projector is idempotent. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_mul_self
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    continuousLinearMapCardinalitySectorProjectorL2 Q k hComm *
        continuousLinearMapCardinalitySectorProjectorL2 Q k hComm =
      continuousLinearMapCardinalitySectorProjectorL2 Q k hComm := by
  simpa using
    continuousLinearMap_cardinalitySectorProjectorL2_mul_eq_ite
      Q k k hIdempotent hComm

/-- Distinct cardinality-sector projectors have zero product. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_mul_eq_zero_of_ne
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k l : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (hkl : k ≠ l) :
    continuousLinearMapCardinalitySectorProjectorL2 Q k hComm *
        continuousLinearMapCardinalitySectorProjectorL2 Q l hComm = 0 := by
  simpa [hkl] using
    continuousLinearMap_cardinalitySectorProjectorL2_mul_eq_ite
      Q k l hIdempotent hComm

/-- Summing the cardinality-sector projectors over all possible weights gives the
identity. -/
theorem continuousLinearMap_sum_range_cardinalitySectorProjectorL2_eq_one
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    (∑ k ∈ Finset.range (Fintype.card ι + 1),
      continuousLinearMapCardinalitySectorProjectorL2 Q k hComm) = 1 := by
  classical
  calc
    (∑ k ∈ Finset.range (Fintype.card ι + 1),
      continuousLinearMapCardinalitySectorProjectorL2 Q k hComm) =
        ∑ s ∈ (Finset.univ : Finset ι).powerset,
          continuousLinearMapJointSectorProjectorL2 Q s hComm := by
            simpa [continuousLinearMapCardinalitySectorProjectorL2] using
              (Finset.sum_powerset
                (Finset.univ : Finset ι)
                (fun s : Finset ι =>
                  continuousLinearMapJointSectorProjectorL2 Q s hComm)).symm
    _ = 1 :=
      continuousLinearMap_sum_powerset_jointSectorProjectorL2_eq_one Q hComm

/-- The full coordinate sum acts on the weight-`k` projector by the scalar `k`. -/
theorem continuousLinearMap_univ_sum_mul_cardinalitySectorProjectorL2_eq_natCast_smul
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (k : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    (∑ i : ι, Q i) *
        continuousLinearMapCardinalitySectorProjectorL2 Q k hComm =
      (k : ℝ) • continuousLinearMapCardinalitySectorProjectorL2 Q k hComm := by
  classical
  unfold continuousLinearMapCardinalitySectorProjectorL2
  rw [Finset.mul_sum, smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hscard : s.card = k :=
    (Finset.mem_powersetCard.mp hs).2
  apply ContinuousLinearMap.ext
  intro f
  change
    (∑ i : ι, Q i)
        (continuousLinearMapJointSectorProjectorL2 Q s hComm f) =
      (k : ℝ) • continuousLinearMapJointSectorProjectorL2 Q s hComm f
  have hSector :=
    continuousLinearMap_jointSectorProjectorL2_apply_mem_jointSectorSubmoduleL2
      Q s hIdempotent hComm f
  have hEigen :=
    continuousLinearMap_univ_sum_apply_eq_card_smul_of_mem_jointSectorSubmoduleL2
      Q s hSector
  simpa [hscard] using hEigen

/-- The full coordinate sum has the finite spectral resolution indexed by sector
cardinality. -/
theorem continuousLinearMap_univ_sum_eq_weighted_cardinalitySectorProjectorsL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    (∑ i : ι, Q i) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        (k : ℝ) • continuousLinearMapCardinalitySectorProjectorL2 Q k hComm := by
  classical
  let H : V →L[ℝ] V := ∑ i : ι, Q i
  calc
    (∑ i : ι, Q i) = H := rfl
    _ = H * 1 := (mul_one H).symm
    _ = H *
        (∑ k ∈ Finset.range (Fintype.card ι + 1),
          continuousLinearMapCardinalitySectorProjectorL2 Q k hComm) := by
            rw [continuousLinearMap_sum_range_cardinalitySectorProjectorL2_eq_one
              Q hComm]
    _ = ∑ k ∈ Finset.range (Fintype.card ι + 1),
          H * continuousLinearMapCardinalitySectorProjectorL2 Q k hComm := by
            rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (Fintype.card ι + 1),
          (k : ℝ) • continuousLinearMapCardinalitySectorProjectorL2 Q k hComm := by
            apply Finset.sum_congr rfl
            intro k hk
            exact
              continuousLinearMap_univ_sum_mul_cardinalitySectorProjectorL2_eq_natCast_smul
                Q k hIdempotent hComm

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- The actual beta-zero projector obtained by aggregating all joint sectors of
cardinality `k`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
    (k : ℕ) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  continuousLinearMapCardinalitySectorProjectorL2
    (fun edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          edge)
    k
    (fun target source f =>
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
        target source f)

/-- The actual heat-bath Hamiltonian is the operator sum of the 324 commuting
one-link fluctuation projectors. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2 :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 =
      ∑ edge :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          edge := by
  apply ContinuousLinearMap.ext
  intro f
  simpa only [ContinuousLinearMap.sum_apply] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_heatBathHamiltonianL2_eq_sum_commuting_fluctuation_family
      f

/-- Actual cardinality-sector projectors satisfy the Kronecker multiplication
law. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_mul_eq_ite
    (k l : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 l =
      if k = l then
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k
      else 0 := by
  classical
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2]
    using
      (continuousLinearMap_cardinalitySectorProjectorL2_mul_eq_ite
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        k l
        (fun edge f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
            edge f)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f))

/-- The actual cardinality-sector projectors resolve the identity over weights
`0, ..., 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_range_fluctuationCardinalityProjectorL2_eq_one :
    (∑ k ∈ Finset.range 325,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k) = 1 := by
  classical
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324] using
      (continuousLinearMap_sum_range_cardinalitySectorProjectorL2_eq_one
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f))

/-- The actual heat-bath Hamiltonian acts on the weight-`k` projector by the
scalar `k`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_mul_fluctuationCardinalityProjectorL2_eq_natCast_smul
    (k : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k =
      (k : ℝ) •
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k := by
  classical
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2]
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2]
    using
      (continuousLinearMap_univ_sum_mul_cardinalitySectorProjectorL2_eq_natCast_smul
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
            target source f))

/-- Finite spectral resolution of the actual beta-zero heat-bath Hamiltonian. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_weighted_fluctuationCardinalityProjectorsL2 :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 =
      ∑ k ∈ Finset.range 325,
        (k : ℝ) •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k := by
  classical
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2]
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324] using
      (continuousLinearMap_univ_sum_eq_weighted_cardinalitySectorProjectorsL2
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        (fun edge f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
            edge f)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f))

/-- Every actual beta-zero Gibbs `L²` vector is the sum of its cardinality-sector
components. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_range_fluctuationCardinalityProjectorL2_apply_eq
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    (∑ k ∈ Finset.range 325,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k f) = f := by
  have hOperator :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_range_fluctuationCardinalityProjectorL2_eq_one
  have hApply := congrArg
    (fun T :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =>
      T f)
    hOperator
  simpa using hApply

/-- Pointwise form of the finite beta-zero heat-bath spectral resolution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_apply_eq_weighted_fluctuationCardinalityProjectorsL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
      ∑ k ∈ Finset.range 325,
        (k : ℝ) •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k f := by
  have hOperator :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_weighted_fluctuationCardinalityProjectorsL2
  have hApply := congrArg
    (fun T :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =>
      T f)
    hOperator
  simpa using hApply

/-- Compact receipt for the actual cardinality-indexed finite beta-zero spectral
resolution. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalitySpectralResolutionL2Receipt :
    Prop :=
  (∀ k l : ℕ,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 l =
      if k = l then
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k
      else 0) ∧
  (∑ k ∈ Finset.range 325,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k) = 1 ∧
  (∀ k : ℕ,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k =
      (k : ℝ) •
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k) ∧
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 =
    ∑ k ∈ Finset.range 325,
      (k : ℝ) •
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k

/-- The actual cardinality-indexed finite beta-zero spectral-resolution receipt
is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalitySpectralResolutionL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalitySpectralResolutionL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_mul_eq_ite,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_range_fluctuationCardinalityProjectorL2_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_mul_fluctuationCardinalityProjectorL2_eq_natCast_smul,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_weighted_fluctuationCardinalityProjectorsL2⟩

end

end MathlibAnalytic
end MGAP4D
