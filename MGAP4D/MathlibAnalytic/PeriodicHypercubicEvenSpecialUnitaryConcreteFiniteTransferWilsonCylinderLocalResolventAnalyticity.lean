import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderRealAnalyticity
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set
open scoped InnerProductSpace Topology Ring

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000

local instance wilsonCylinderLocalResolventPhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- Local real analyticity, on the genuine physical coupling half-line, of the
shifted Wilson transfer inverse at every coupling where the shifted transfer
operator is a unit.  This is the operator-norm resolvent input needed before
passing to isolated spectral sectors. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shiftedInverse_analyticWithinAt
    (H N : ℕ) (hN : 0 < N) (z beta : ℝ) (hbeta : 0 ≤ beta)
    (hunit : IsUnit
      (z • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta)) :
    AnalyticWithinAt ℝ
      (fun gamma : ℝ =>
        Ring.inverse
          (z • (1 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
                PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
              H N hN gamma))
      (Set.Ici (0 : ℝ)) beta := by
  with_reducible_and_instances
    let PH := PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N
    letI : IsBoundedSMul ℝ (PH →L[ℝ] PH) :=
      IsBoundedSMul.of_norm_smul_le fun r A =>
        ContinuousLinearMap.opNorm_smul_le r A
    let T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN
    have hT : AnalyticWithinAt ℝ T (Set.Ici (0 : ℝ)) beta := by
      simpa [T] using
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_analyticWithinAt
          H N hN beta hbeta
    have hconst :
        AnalyticWithinAt ℝ
          (fun _ : ℝ => z • (1 : PH →L[ℝ] PH))
          (Set.Ici (0 : ℝ)) beta :=
      analyticWithinAt_const
    have hshift :
        AnalyticWithinAt ℝ
          (fun gamma : ℝ => z • (1 : PH →L[ℝ] PH) - T gamma)
          (Set.Ici (0 : ℝ)) beta :=
      hconst.sub hT
    have houter :
        AnalyticAt ℝ
          (fun A : PH →L[ℝ] PH => Ring.inverse A)
          (z • (1 : PH →L[ℝ] PH) - T beta) := by
      exact analyticAt_inverse (𝕜 := ℝ) (IsUnit.unit hunit)
    simpa [PH, T, Function.comp_def] using
      houter.comp_analyticWithinAt hshift

/-- Packaged resolvent regularity statement: native Wilson transfer
analyticity together with local analyticity of every real shifted inverse at a
unit point. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonLocalResolventAnalyticity_package
    (H N : ℕ) (hN : 0 < N) :
    (∀ beta : ℝ, 0 ≤ beta →
      AnalyticWithinAt ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN)
        (Set.Ici (0 : ℝ)) beta) ∧
    (∀ z beta : ℝ, 0 ≤ beta →
      IsUnit
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta) →
      AnalyticWithinAt ℝ
        (fun gamma : ℝ =>
          Ring.inverse
            (z • (1 :
                PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
                  PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
              periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
                H N hN gamma))
        (Set.Ici (0 : ℝ)) beta) := by
  constructor
  · intro beta hbeta
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_analyticWithinAt
        H N hN beta hbeta
  · intro z beta hbeta hunit
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shiftedInverse_analyticWithinAt
        H N hN z beta hbeta hunit

end
end MathlibAnalytic
end MGAP4D
