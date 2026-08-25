import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderPhysicalHilbertNontrivial
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace Ring

noncomputable section

/-- On the genuine finite Wilson physical Hilbert space, scalar multiples of the
identity have exactly the expected operator norm.  The lower bound is witnessed
by the normalized physical vacuum, so no global `Nontrivial` instance is needed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert_norm_smul_id_eq_abs
    (H N : ℕ) (a : ℝ) :
    ‖a • (1 :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)‖ = |a| := by
  let PH := PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N
  let Ω : PH := periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum H N
  have hΩnorm : ‖Ω‖ = 1 := by
    simpa [Ω] using periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum_norm H N
  apply le_antisymm
  · calc
      ‖a • (1 : PH →L[ℝ] PH)‖ ≤
          ‖a‖ * ‖(1 : PH →L[ℝ] PH)‖ :=
        ContinuousLinearMap.opNorm_smul_le a (1 : PH →L[ℝ] PH)
      _ ≤ ‖a‖ * 1 := by
        exact mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := PH)) (norm_nonneg a)
      _ = |a| := by simp [Real.norm_eq_abs]
  · have hbound :
        ‖(a • (1 : PH →L[ℝ] PH)) Ω‖ ≤
          ‖a • (1 : PH →L[ℝ] PH)‖ * ‖Ω‖ :=
      ContinuousLinearMap.le_opNorm (a • (1 : PH →L[ℝ] PH)) Ω
    calc
      |a| = ‖(a • (1 : PH →L[ℝ] PH)) Ω‖ := by
        simp [hΩnorm, Real.norm_eq_abs]
      _ ≤ ‖a • (1 : PH →L[ℝ] PH)‖ * ‖Ω‖ := hbound
      _ = ‖a • (1 : PH →L[ℝ] PH)‖ := by rw [hΩnorm, mul_one]

/-- The joint shifted-transfer perturbation bound in the ordinary real metric:
the spectral shift contributes exactly `|w-z|`, while the Wilson coupling keeps
its already-proved global Lipschitz constant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_sub_shifted_norm_le_abs
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
      |w - z| +
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N * |gamma - beta| := by
  have hbound :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_sub_shifted_norm_le
      H N hN z w beta gamma hbeta hgamma
  rw [periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert_norm_smul_id_eq_abs]
    at hbound
  exact hbound

/-- Quantitative joint real-resolvent stability in ordinary scalar distance.
This is the Neumann criterion from the preceding layer after the genuine vacuum
identifies the spectral-shift operator norm with `|w-z|`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_of_joint_abs_lt
    (H N : ℕ) (hN : 0 < N)
    (z w beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hunit : IsUnit
      (z • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta))
    (hnear :
      |w - z| +
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
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_of_joint_norm_lt
      H N hN z w beta gamma hbeta hgamma hunit
  rw [periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert_norm_smul_id_eq_abs]
  exact hnear

/-- Every genuine real resolvent point has an explicitly positive joint
spectral-shift/coupling Neumann neighborhood.  The radius is exactly the inverse
operator norm of the base-point resolvent, not an arbitrary epsilon. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_exists_positive_joint_resolvent_radius
    (H N : ℕ) (hN : 0 < N)
    (z beta : ℝ) (hbeta : 0 ≤ beta)
    (hunit : IsUnit
      (z • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta)) :
    ∃ r : ℝ,
      0 < r ∧
      r =
        ‖Ring.inverse
          (z • (1 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
                PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
              H N hN beta)‖⁻¹ ∧
      ∀ w gamma : ℝ, 0 ≤ gamma →
        |w - z| +
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N * |gamma - beta| < r →
        IsUnit
          (w • (1 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
                PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
              H N hN gamma) := by
  let r : ℝ :=
    ‖Ring.inverse
      (z • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN beta)‖⁻¹
  have hr : 0 < r := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shiftedInverseRadius_pos
        H N hN z beta hbeta hunit
  refine ⟨r, hr, rfl, ?_⟩
  intro w gamma hgamma hnear
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shifted_isUnit_of_joint_abs_lt
      H N hN z w beta gamma hbeta hgamma hunit hnear

/-- Audit-visible package for the ordinary-metric joint resolvent layer. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonExplicitJointResolventNeighborhood_package
    (H N : ℕ) (hN : 0 < N) :
    (∀ a : ℝ,
      ‖a • (1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)‖ = |a|) ∧
    (∀ z beta : ℝ, 0 ≤ beta →
      IsUnit
        (z • (1 :
            PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta) →
      ∃ r : ℝ, 0 < r ∧
        ∀ w gamma : ℝ, 0 ≤ gamma →
          |w - z| +
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
                H N * |gamma - beta| < r →
          IsUnit
            (w • (1 :
                PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
                  PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) -
              periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
                H N hN gamma)) := by
  constructor
  · intro a
    exact periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert_norm_smul_id_eq_abs H N a
  · intro z beta hbeta hunit
    obtain ⟨r, hr, _, hres⟩ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_exists_positive_joint_resolvent_radius
        H N hN z beta hbeta hunit
    exact ⟨r, hr, hres⟩

end
end MathlibAnalytic
end MGAP4D
