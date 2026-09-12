import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityProjectorNonzeroCriterionL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicHamiltonianKernelIntersectionBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A vector killed by every member of a finite family belongs to the empty joint
sector. -/
theorem continuousLinearMap_mem_empty_jointSectorSubmoduleL2_of_all_eq_zero
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    {f : V}
    (hKilled : ∀ i : ι, Q i f = 0) :
    f ∈ continuousLinearMapJointSectorSubmoduleL2 Q ∅ := by
  rw [continuousLinearMapJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro i hi
    simp at hi
  · intro i hi
    exact hKilled i

/-- The cardinality-zero projector fixes every vector killed by all coordinate
operators. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_zero_apply_eq_self_of_all_eq_zero
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hKilled : ∀ i : ι, Q i f = 0) :
    continuousLinearMapCardinalitySectorProjectorL2 Q 0 hComm f = f := by
  exact
    continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
      Q 0 ∅ hComm (by simp)
      (continuousLinearMap_mem_empty_jointSectorSubmoduleL2_of_all_eq_zero
        Q hKilled)

/-- A nonzero vector killed by every coordinate operator witnesses nonvanishing
of the cardinality-zero projector. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_zero_ne_zero_of_exists_nonzero_killed_by_all
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hfNonzero : f ≠ 0)
    (hKilled : ∀ i : ι, Q i f = 0) :
    continuousLinearMapCardinalitySectorProjectorL2 Q 0 hComm ≠ 0 := by
  apply
    (continuousLinearMap_cardinalitySectorProjectorL2_ne_zero_iff_exists_nonzero_mem_jointSectorSubmoduleL2
      Q 0 hIdempotent hComm).2
  exact ⟨
    ∅,
    f,
    by simp,
    continuousLinearMap_mem_empty_jointSectorSubmoduleL2_of_all_eq_zero Q hKilled,
    hfNonzero⟩

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityZeroVacuumEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- The normalized Gibbs vacuum of the actual side-three periodic `SU(2)` system
is nonzero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_gibbsVacuumL2_ne_zero :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 ≠ 0 := by
  intro hZero
  have hNorm :=
    continuous_compact_oriented_gibbsVacuumL2_norm
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
  rw [hZero, norm_zero] at hNorm
  norm_num at hNorm

/-- Every actual one-link beta-zero fluctuation projection annihilates the Gibbs
vacuum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_singleLinkHeatBathFluctuationL2_gibbsVacuum_eq_zero
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 = 0 := by
  have hAll :=
    (continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_all_fluctuations_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2).1
      (continuous_compact_oriented_heatBathHamiltonianL2_vacuum
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem)
  exact hAll edge

/-- The actual Gibbs vacuum belongs to the empty fluctuation joint sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsVacuumL2_mem_empty_fluctuationJointSector :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        ∅ := by
  classical
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.fluctuationJointSectorSubmoduleL2]
    using
      (continuousLinearMap_mem_empty_jointSectorSubmoduleL2_of_all_eq_zero
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_singleLinkHeatBathFluctuationL2_gibbsVacuum_eq_zero)

/-- The actual cardinality-zero projector fixes the normalized Gibbs vacuum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_gibbsVacuum_eq :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_eq_self_of_mem_jointSector
      0 ∅ (by simp)
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsVacuumL2_mem_empty_fluctuationJointSector

/-- The actual cardinality-zero projector is nonzero, witnessed by the normalized
Gibbs vacuum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_ne_zero :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      0 ≠ 0 := by
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_exists_nonzero_mem_fluctuationJointSector
      0).2
  exact ⟨
    ∅,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2,
    by simp,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsVacuumL2_mem_empty_fluctuationJointSector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_gibbsVacuumL2_ne_zero⟩

/-- The actual cardinality-zero joint-sector sum is non-bottom. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_zero_ne_bot :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      0 ≠ ⊥ := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_cardinalityJointSectorSumSubmoduleL2_ne_bot
      0).1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_ne_zero

/-- The nonzero cardinality-zero projector realizes the zero heat-bath
point-spectrum value through the cardinality-sector criterion. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_zero_mem_heatBathPointSpectrumL2_of_cardinalityZeroProjector :
    (0 : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 := by
  simpa using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_mem_heatBathPointSpectrumL2_of_fluctuationCardinalityProjectorL2_ne_zero
      0
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_ne_zero

/-- Compact receipt for the actual beta-zero cardinality-zero Gibbs-vacuum
witness. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityZeroVacuumWitnessL2Receipt :
    Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 ≠ 0 ∧
  (∀ edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 = 0) ∧
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 ∈
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
      ∅ ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      0 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 =
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      0 ≠ 0 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      0 ≠ ⊥ ∧
  (0 : ℝ) ∈
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2

/-- The actual beta-zero cardinality-zero Gibbs-vacuum witness receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityZeroVacuumWitnessL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityZeroVacuumWitnessL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_gibbsVacuumL2_ne_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_singleLinkHeatBathFluctuationL2_gibbsVacuum_eq_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_gibbsVacuumL2_mem_empty_fluctuationJointSector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_gibbsVacuum_eq,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_ne_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_zero_ne_bot,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_zero_mem_heatBathPointSpectrumL2_of_cardinalityZeroProjector⟩

end

end MathlibAnalytic
end MGAP4D
