import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroPointSpectrumAffineCorrespondenceL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators

noncomputable section

set_option maxRecDepth 8192

/-- At zero Wilson coupling, the complementary one-link heat-bath fluctuation
projections commute pairwise on the full Gibbs `L²` space. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target source : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.singleLinkHeatBathFluctuationL2 target
        (C.singleLinkHeatBathFluctuationL2 source f) =
      C.singleLinkHeatBathFluctuationL2 source
        (C.singleLinkHeatBathFluctuationL2 target f) := by
  have hProjectionComm :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_pairwise_comm_of_beta_eq_zero
      C hBeta target source f
  simp only [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply,
    map_sub]
  rw [hProjectionComm]
  abel

/-- Every one-link heat-bath fluctuation operator is idempotent. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.singleLinkHeatBathFluctuationL2 target
        (C.singleLinkHeatBathFluctuationL2 target f) =
      C.singleLinkHeatBathFluctuationL2 target f := by
  exact
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply_fluctuation
      C target f

/-- The actual side-three periodic `SU(2)` beta-zero system has a pairwise
commuting family of one-link fluctuation projections. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        target
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          source f) =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        source
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          target f) := by
  exact
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      target source f

/-- Every actual one-link fluctuation projection is idempotent. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
    (target :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        target
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          target f) =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        target f := by
  exact
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem target f

/-- The actual native heat-bath Hamiltonian is the finite sum of the complete
commuting idempotent one-link fluctuation family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_heatBathHamiltonianL2_eq_sum_commuting_fluctuation_family
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
      ∑ edge :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          edge f := by
  exact continuous_compact_oriented_heatBathHamiltonianL2_apply
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem f

/-- Compact receipt exposing the actual beta-zero Hamiltonian as a sum of `324`
pairwise commuting idempotent fluctuation projections.  This is the direct
algebraic input for the later annihilating-polynomial and full-spectrum steps. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCommutingFluctuationProjectionFamilyL2Receipt :
    Prop :=
  (Fintype.card
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge = 324) ∧
    (∀ (target :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          target
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
            target f) =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          target f) ∧
    (∀ (target source :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          target
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
            source f) =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          source
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
            target f)) ∧
    (∀ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
        ∑ edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
            edge f)

/-- The actual beta-zero commuting-fluctuation-family receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCommutingFluctuationProjectionFamilyL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCommutingFluctuationProjectionFamilyL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_heatBathHamiltonianL2_eq_sum_commuting_fluctuation_family⟩

end

end MathlibAnalytic
end MGAP4D
