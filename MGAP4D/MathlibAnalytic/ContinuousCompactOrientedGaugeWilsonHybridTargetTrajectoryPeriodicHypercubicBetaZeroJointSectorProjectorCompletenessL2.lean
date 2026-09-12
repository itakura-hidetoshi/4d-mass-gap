import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroJointSectorProjectorIdempotentOrthogonalL2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Pairwise commuting selected/complement factors remain pairwise commuting
when the product is restricted to an arbitrary finite coordinate set. -/
theorem continuousLinearMapJointSectorFactorL2_pairwise_comm_on
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (u s : Finset ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    (u : Set ι).Pairwise
      (Commute on continuousLinearMapJointSectorFactorL2 Q s) := by
  apply
    (continuousLinearMapJointSectorFactorL2_pairwise_comm Q s hComm).mono
  intro i hi
  exact Finset.mem_univ i

/-- The partial joint-sector projector over a finite coordinate set `u`.
The full canonical projector is the specialization `u = Finset.univ`. -/
noncomputable def continuousLinearMapJointSectorPartialProjectorL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (u s : Finset ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    V →L[ℝ] V :=
  u.noncommProd
    (continuousLinearMapJointSectorFactorL2 Q s)
    (continuousLinearMapJointSectorFactorL2_pairwise_comm_on Q u s hComm)

/-- Adding a fresh coordinate extracts its selected/complement factor on the
left of the partial projector. -/
theorem continuousLinearMapJointSectorPartialProjectorL2_insert
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (u s : Finset ι)
    (a : ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (ha : a ∉ u) :
    continuousLinearMapJointSectorPartialProjectorL2 Q (insert a u) s hComm =
      continuousLinearMapJointSectorFactorL2 Q s a *
        continuousLinearMapJointSectorPartialProjectorL2 Q u s hComm := by
  simpa [continuousLinearMapJointSectorPartialProjectorL2] using
    (Finset.noncommProd_insert_of_notMem
      u a
      (continuousLinearMapJointSectorFactorL2 Q s)
      (continuousLinearMapJointSectorFactorL2_pairwise_comm_on
        Q (insert a u) s hComm)
      ha)

/-- Inserting a coordinate outside the product support into the sector label
does not change the partial projector. -/
theorem continuousLinearMapJointSectorPartialProjectorL2_label_insert
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (u s : Finset ι)
    (a : ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (ha : a ∉ u) :
    continuousLinearMapJointSectorPartialProjectorL2 Q u (insert a s) hComm =
      continuousLinearMapJointSectorPartialProjectorL2 Q u s hComm := by
  unfold continuousLinearMapJointSectorPartialProjectorL2
  apply Finset.noncommProd_congr rfl
  intro i hi
  have hia : i ≠ a := by
    intro hia
    subst i
    exact ha hi
  simp [continuousLinearMapJointSectorFactorL2, hia]

/-- The selected/complement partial projectors over all subsets of `u` sum to
the identity.  This is the finite Boolean partition identity, proved without a
finite-dimensional hypothesis. -/
theorem continuousLinearMap_sum_powerset_partialJointSectorProjectorL2_eq_one
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (u : Finset ι)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    (∑ s ∈ u.powerset,
      continuousLinearMapJointSectorPartialProjectorL2 Q u s hComm) = 1 := by
  classical
  induction u using Finset.induction with
  | empty =>
      simp [continuousLinearMapJointSectorPartialProjectorL2]
  | @insert a u ha ih =>
      have hDisjoint :
          Disjoint u.powerset (u.powerset.image (insert a)) := by
        refine Finset.disjoint_left.2 ?_
        intro s hs hsi
        rcases Finset.mem_image.mp hsi with ⟨t, ht, rfl⟩
        exact
          (Finset.notMem_of_mem_powerset_of_notMem hs ha)
            (Finset.mem_insert_self a t)
      have hInsertInj :
          Set.InjOn (insert a) (u.powerset : Set (Finset ι)) := by
        intro s hs t ht hst
        have has : a ∉ s :=
          Finset.notMem_of_mem_powerset_of_notMem hs ha
        have hat : a ∉ t :=
          Finset.notMem_of_mem_powerset_of_notMem ht ha
        have hErase := congrArg (fun r : Finset ι => r.erase a) hst
        simpa [has, hat] using hErase
      have hWithoutA :
          (∑ s ∈ u.powerset,
            continuousLinearMapJointSectorPartialProjectorL2
              Q (insert a u) s hComm) =
            (1 - Q a) *
              ∑ s ∈ u.powerset,
                continuousLinearMapJointSectorPartialProjectorL2
                  Q u s hComm := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro s hs
        have has : a ∉ s :=
          Finset.notMem_of_mem_powerset_of_notMem hs ha
        rw [continuousLinearMapJointSectorPartialProjectorL2_insert
          Q u s a hComm ha]
        simp [continuousLinearMapJointSectorFactorL2, has]
      have hWithA :
          (∑ s ∈ u.powerset.image (insert a),
            continuousLinearMapJointSectorPartialProjectorL2
              Q (insert a u) s hComm) =
            Q a *
              ∑ s ∈ u.powerset,
                continuousLinearMapJointSectorPartialProjectorL2
                  Q u s hComm := by
        rw [Finset.mul_sum, Finset.sum_image hInsertInj]
        refine Finset.sum_congr rfl ?_
        intro s hs
        rw [continuousLinearMapJointSectorPartialProjectorL2_insert
          Q u (insert a s) a hComm ha]
        rw [continuousLinearMapJointSectorPartialProjectorL2_label_insert
          Q u s a hComm ha]
        simp [continuousLinearMapJointSectorFactorL2]
      rw [Finset.powerset_insert, Finset.sum_union hDisjoint,
        hWithoutA, hWithA, ih]
      simpa using
        (sub_add_cancel (1 : V →L[ℝ] V) (Q a))

/-- The full canonical joint-sector projectors form a resolution of the
identity. -/
theorem continuousLinearMap_sum_powerset_jointSectorProjectorL2_eq_one
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    (∑ s ∈ (Finset.univ : Finset ι).powerset,
      continuousLinearMapJointSectorProjectorL2 Q s hComm) = 1 := by
  change
    (∑ s ∈ (Finset.univ : Finset ι).powerset,
      continuousLinearMapJointSectorPartialProjectorL2
        Q Finset.univ s hComm) = 1
  exact
    continuousLinearMap_sum_powerset_partialJointSectorProjectorL2_eq_one
      Q Finset.univ hComm

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_completenessEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- The actual 324-link beta-zero canonical projectors sum to the identity. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_powerset_fluctuationJointSectorProjectorL2_eq_one :
    (∑ s ∈
      (Finset.univ : Finset
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).powerset,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
        s) = 1 := by
  classical
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2]
    using
      (continuousLinearMap_sum_powerset_jointSectorProjectorL2_eq_one
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f))

/-- Every actual beta-zero `L²` vector is the sum of its canonical joint-sector
components. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_powerset_fluctuationJointSectorProjectorL2_apply_eq
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    (∑ s ∈
      (Finset.univ : Finset
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).powerset,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
        s f) = f := by
  have hOperator :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_powerset_fluctuationJointSectorProjectorL2_eq_one
  have hApply := congrArg
    (fun T :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =>
      T f)
    hOperator
  simpa using hApply

/-- Compact receipt for the actual exhaustive beta-zero joint-sector
resolution of the identity. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroJointSectorProjectorCompletenessL2Receipt :
    Prop :=
  (∑ s ∈
    (Finset.univ : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).powerset,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
      s) = 1 ∧
  ∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    (∑ s ∈
      (Finset.univ : Finset
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).powerset,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
        s f) = f

/-- The actual exhaustive beta-zero joint-sector resolution receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroJointSectorProjectorCompletenessL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroJointSectorProjectorCompletenessL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_powerset_fluctuationJointSectorProjectorL2_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_powerset_fluctuationJointSectorProjectorL2_apply_eq⟩

end

end MathlibAnalytic
end MGAP4D
