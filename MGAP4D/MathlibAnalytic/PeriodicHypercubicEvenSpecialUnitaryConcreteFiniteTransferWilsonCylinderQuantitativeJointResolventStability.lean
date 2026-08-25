import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderLocalResolventStability
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set
open scoped InnerProductSpace Topology Ring

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

local instance wilsonCylinderQuantitativeJointResolventPhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- Joint operator-norm perturbation bound for the real spectral shift and the
physical Wilson coupling.  The shift contribution is kept in its intrinsic
operator norm, while the coupling contribution uses the already-proved global
Wilson Lipschitz estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_sub_shifted_norm_le
    (H N : ℕ) (hN : 0 < N)
    (z w beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) :
    ‖(w • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN gamma) -
      (z • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta)‖ ≤
      ‖(w - z) • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)‖ +
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N * |gamma - beta| := by
  with_reducible_and_instances
    let PH := PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N
    let T : ℝ → PH →L[ℝ] PH :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN
    have hT :
        ‖T gamma - T beta‖ ≤
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N * |gamma - beta| := by
      simpa [T] using
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_norm_sub_le_abs
          H N hN beta gamma hbeta hgamma
    have hid :
        (w • (1 : PH →L[ℝ] PH) - T gamma) -
            (z • (1 : PH →L[ℝ] PH) - T beta) =
          (w - z) • (1 : PH →L[ℝ] PH) - (T gamma - T beta) := by
      module
    change
      ‖(w • (1 : PH →L[ℝ] PH) - T gamma) -
          (z • (1 : PH →L[ℝ] PH) - T beta)‖ ≤
        ‖(w - z) • (1 : PH →L[ℝ] PH)‖ +
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N * |gamma - beta|
    rw [hid]
    exact le_trans
      (norm_sub_le ((w - z) • (1 : PH →L[ℝ] PH)) (T gamma - T beta))
      (add_le_add le_rfl hT)

/-- Quantitative joint real-resolvent stability.  Starting from a genuine unit
`z I - T beta`, Mathlib's Banach-algebra Neumann construction `Units.ofNearby`
produces a unit for `w I - T gamma` whenever the explicit joint perturbation
bound is smaller than the inverse-norm threshold at the base point.

No nontriviality assumption on the physical Hilbert carrier is inserted here:
the theorem states the exact Neumann implication and leaves positivity of the
threshold to a later carrier-nontriviality theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_of_joint_norm_lt
    (H N : ℕ) (hN : 0 < N)
    (z w beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hunit : IsUnit
      (z • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta))
    (hnear :
      ‖(w - z) • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)‖ +
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N * |gamma - beta| <
      ‖Ring.inverse
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta)‖⁻¹) :
    IsUnit
      (w • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN gamma) := by
  rcases hunit with ⟨u, hu⟩
  with_reducible_and_instances
    let PH := PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N
    let T : ℝ → PH →L[ℝ] PH :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN
    let A0 : PH →L[ℝ] PH := z • (1 : PH →L[ℝ] PH) - T beta
    let A1 : PH →L[ℝ] PH := w • (1 : PH →L[ℝ] PH) - T gamma
    have huA0 : (↑u : PH →L[ℝ] PH) = A0 := by
      simpa [A0, T] using hu
    have hinv : Ring.inverse A0 = (↑u⁻¹ : PH →L[ℝ] PH) := by
      rw [← huA0, Ring.inverse_unit]
    have hbound :
        ‖A1 - A0‖ ≤
          ‖(w - z) • (1 : PH →L[ℝ] PH)‖ +
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
                H N * |gamma - beta| := by
      simpa [A0, A1, T] using
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_sub_shifted_norm_le
          H N hN z w beta gamma hbeta hgamma
    have hlt : ‖A1 - A0‖ < ‖(↑u⁻¹ : PH →L[ℝ] PH)‖⁻¹ := by
      calc
        ‖A1 - A0‖ ≤
            ‖(w - z) • (1 : PH →L[ℝ] PH)‖ +
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
                  H N * |gamma - beta| := hbound
        _ < ‖Ring.inverse A0‖⁻¹ := by
          simpa [A0, T] using hnear
        _ = ‖(↑u⁻¹ : PH →L[ℝ] PH)‖⁻¹ := by rw [hinv]
    have hnearUnit : ‖A1 - (↑u : PH →L[ℝ] PH)‖ < ‖(↑u⁻¹ : PH →L[ℝ] PH)‖⁻¹ := by
      simpa [huA0] using hlt
    let unear := u.ofNearby A1 hnearUnit
    have hunear : (↑unear : PH →L[ℝ] PH) = A1 := by
      simp [unear, Units.ofNearby]
    let e : PH ≃L[ℝ] PH := ContinuousLinearEquiv.ofUnit unear
    have he : (e : PH →L[ℝ] PH) = A1 := by
      apply ContinuousLinearMap.ext
      intro x
      simpa [e, ContinuousLinearEquiv.toContinuousLinearMap,
        ContinuousLinearEquiv.ofUnit] using
        congrArg (fun f : PH →L[ℝ] PH => f x) hunear
    change IsUnit A1
    rw [← he]
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr (by
      simpa using e.bijective)

/-- The quantitative real-resolvent package: the exact joint perturbation norm
is bounded by the spectral-shift contribution plus the Wilson coupling
Lipschitz contribution, and that bound feeds directly into Mathlib's Neumann
unit construction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonQuantitativeJointResolventStability_package
    (H N : ℕ) (hN : 0 < N) :
    (∀ z w beta gamma : ℝ, 0 ≤ beta → 0 ≤ gamma →
      ‖(w • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN gamma) -
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta)‖ ≤
        ‖(w - z) • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)‖ +
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N * |gamma - beta|) ∧
    (∀ z w beta gamma : ℝ, 0 ≤ beta → 0 ≤ gamma →
      IsUnit
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta) →
      ‖(w - z) • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)‖ +
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N * |gamma - beta| <
        ‖Ring.inverse
          (z • (1 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
                PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
              H N hN beta)‖⁻¹ →
      IsUnit
        (w • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN gamma)) := by
  constructor
  · intro z w beta gamma hbeta hgamma
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_sub_shifted_norm_le
        H N hN z w beta gamma hbeta hgamma
  · intro z w beta gamma hbeta hgamma hunit hnear
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_of_joint_norm_lt
        H N hN z w beta gamma hbeta hgamma hunit hnear

end
end MathlibAnalytic
end MGAP4D