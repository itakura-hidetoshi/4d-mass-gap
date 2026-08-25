import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderLocalResolventAnalyticity
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set
open scoped InnerProductSpace Topology Ring

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

local instance wilsonCylinderLocalResolventStabilityPhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- The exact physical Wilson transfer family is globally Lipschitz on the
physical coupling half-line, in operator norm, with the same beta-independent
path-action bound that controls all higher Taylor coefficients.  This is the
zeroth-order specialization of the already-proved absolute Taylor remainder. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_norm_sub_le_abs
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N * |gamma - beta| := by
  have hO0 :
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN 0 beta hbeta =
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_zero_eq_transferOperator
        H N hN beta hbeta).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_eq_physicalTransfer
        H N hN beta hbeta).symm
  have hterm0 :
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
          H N hN beta hbeta gamma 0 =
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonTaylorTerm
    simpa [hO0]
  have hrem :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonTaylor_remainder_norm_le_abs
      H N hN 0 beta gamma hbeta hgamma
  simpa [hterm0] using hrem

/-- A real shifted-transfer unit remains a unit for all sufficiently nearby
physical couplings.  Thus the real resolvent set is locally stable in beta,
not merely the totalized inverse map analytic at the base point. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_eventuallyWithin
    (H N : ℕ) (hN : 0 < N) (z beta : ℝ) (hbeta : 0 ≤ beta)
    (hunit : IsUnit
      (z • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta)) :
    ∀ᶠ gamma in 𝓝[Set.Ici (0 : ℝ)] beta,
      IsUnit
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN gamma) := by
  rcases hunit with ⟨u, hu⟩
  with_reducible_and_instances
    let PH := PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N
    let T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN
    let A := fun gamma : ℝ => z • (1 : PH →L[ℝ] PH) - T gamma
    have hT : AnalyticWithinAt ℝ T (Set.Ici (0 : ℝ)) beta := by
      simpa [T] using
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_analyticWithinAt
          H N hN beta hbeta
    have hA : AnalyticWithinAt ℝ A (Set.Ici (0 : ℝ)) beta := by
      have hconst :
          AnalyticWithinAt ℝ
            (fun _ : ℝ => z • (1 : PH →L[ℝ] PH))
            (Set.Ici (0 : ℝ)) beta :=
        analyticWithinAt_const
      simpa [A] using hconst.sub hT
    have hub : (↑u : PH →L[ℝ] PH) = A beta := by
      simpa [A, T] using hu
    let e : PH ≃L[ℝ] PH := ContinuousLinearEquiv.ofUnit u
    have he : (e : PH →L[ℝ] PH) = A beta := by
      simpa [e] using hub
    have hopen :
        Set.range ((↑) : (PH ≃L[ℝ] PH) → PH →L[ℝ] PH) ∈ 𝓝 (A beta) := by
      rw [← he]
      exact ContinuousLinearEquiv.nhds e
    have hnear :
        ∀ᶠ gamma in 𝓝[Set.Ici (0 : ℝ)] beta,
          A gamma ∈ Set.range ((↑) : (PH ≃L[ℝ] PH) → PH →L[ℝ] PH) := by
      exact hA.continuousWithinAt hopen
    filter_upwards [hnear] with gamma hgamma
    rcases hgamma with ⟨egamma, hegamma⟩
    rw [← hegamma]
    exact (ContinuousLinearEquiv.toUnit egamma).isUnit

/-- Local real spectral-exclusion stability package.  At every physical
coupling and every real shifted-transfer unit point, the shifted operators stay
units on a relative neighborhood of the physical half-line, while the actual
resolvent is analytic there at the base coupling.  This is the local isolated-
spectral-sector input needed before introducing a spectral projection carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonLocalResolventStability_package
    (H N : ℕ) (hN : 0 < N) :
    (∀ beta gamma : ℝ, 0 ≤ beta → 0 ≤ gamma →
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN gamma -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta‖ ≤
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N * |gamma - beta|) ∧
    (∀ z beta : ℝ, 0 ≤ beta →
      IsUnit
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta) →
      (∀ᶠ gamma in 𝓝[Set.Ici (0 : ℝ)] beta,
        IsUnit
          (z • (1 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
                PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
              H N hN gamma)) ∧
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
  · intro beta gamma hbeta hgamma
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_norm_sub_le_abs
        H N hN beta gamma hbeta hgamma
  · intro z beta hbeta hunit
    exact ⟨
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_eventuallyWithin
        H N hN z beta hbeta hunit,
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shiftedInverse_analyticWithinAt
        H N hN z beta hbeta hunit⟩

end
end MathlibAnalytic
end MGAP4D
