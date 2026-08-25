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
operator norm, avoiding any unnecessary scalar-norm coercion, while the Wilson
coupling contribution uses the already-proved global Lipschitz estimate. -/
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
    let T :=
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
    rw [hid]
    calc
      ‖(w - z) • (1 : PH →L[ℝ] PH) - (T gamma - T beta)‖ ≤
          ‖(w - z) • (1 : PH →L[ℝ] PH)‖ + ‖T gamma - T beta‖ :=
        norm_sub_le _ _
      _ ≤ ‖(w - z) • (1 : PH →L[ℝ] PH)‖ +
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N * |gamma - beta| :=
        add_le_add le_rfl hT

/-- The canonical Neumann radius of a real shifted Wilson transfer unit is
strictly positive.  This records the quantitative radius in terms of
`Ring.inverse`, independent of the particular `Units` witness chosen for the
base shifted operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shiftedInverseRadius_pos
    (H N : ℕ) (hN : 0 < N) (z beta : ℝ) (hbeta : 0 ≤ beta)
    (hunit : IsUnit
      (z • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta)) :
    0 <
      ‖Ring.inverse
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta)‖⁻¹ := by
  rcases hunit with ⟨u, hu⟩
  rw [← hu, Ring.inverse_unit]
  have huinv :
      0 <
        ‖(↑(u⁻¹) :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)‖ := by
    exact Units.norm_pos (u⁻¹)
  exact inv_pos.mpr huinv

/-- Quantitative joint resolvent stability.  If the combined perturbation of
spectral shift and Wilson coupling is smaller than the inverse norm radius of
the base shifted operator, then the nearby shifted operator is again a unit.
This is precisely the Banach-algebra Neumann criterion implemented by
Mathlib's `Units.ofNearby`. -/
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
    let T :=
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
    change IsUnit A1
    exact ⟨u.ofNearby A1 hnearUnit, rfl⟩

/-- Explicit coupling-only Neumann criterion at a fixed real spectral shift. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_of_coupling_norm_lt
    (H N : ℕ) (hN : 0 < N)
    (z beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hunit : IsUnit
      (z • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta))
    (hnear :
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N * |gamma - beta| <
      ‖Ring.inverse
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta)‖⁻¹) :
    IsUnit
      (z • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN gamma) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_of_joint_norm_lt
      H N hN z z beta gamma hbeta hgamma hunit
  simpa using hnear

/-- Explicit real spectral-shift Neumann criterion at a fixed physical Wilson
coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_of_shift_norm_lt
    (H N : ℕ) (hN : 0 < N)
    (z w beta : ℝ) (hbeta : 0 ≤ beta)
    (hunit : IsUnit
      (z • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta))
    (hnear :
      ‖(w - z) • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)‖ <
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
          H N hN beta) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_of_joint_norm_lt
      H N hN z w beta beta hbeta hbeta hunit
  simpa using hnear

/-- Quantitative joint real-resolvent stability package.  It upgrades the
previous topological local-stability theorem to an explicit Neumann-radius
statement in both spectral shift and Wilson coupling, together with the
strict positivity of that radius. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonQuantitativeJointResolventStability_package
    (H N : ℕ) (hN : 0 < N) :
    (∀ z beta : ℝ, 0 ≤ beta →
      IsUnit
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta) →
      0 <
        ‖Ring.inverse
          (z • (1 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
                PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
              H N hN beta)‖⁻¹) ∧
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
  · intro z beta hbeta hunit
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shiftedInverseRadius_pos
        H N hN z beta hbeta hunit
  · intro z w beta gamma hbeta hgamma hunit hnear
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_of_joint_norm_lt
        H N hN z w beta gamma hbeta hgamma hunit hnear

end
end MathlibAnalytic
end MGAP4D
