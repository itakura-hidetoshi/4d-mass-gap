import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwelveSpatialQualitativeConstantCollapse
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPoincareSixSpatialGap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- For a nonempty finite family, the normalized sum of squared residuals
vanishes exactly when every operator fixes the vector.

No projection, symmetry, or measure-theoretic hypothesis is needed for this
kernel identity: it is only positivity of the finitely many squared norms. -/
theorem groundStateJointColorNormalizedResidualEnergy_eq_zero_iff_fixed
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    [Nonempty C]
    (P : C → E →L[ℝ] E)
    (x : E) :
    groundStateJointColorNormalizedResidualEnergy P x = 0 ↔
      ∀ c : C, P c x = x := by
  classical
  constructor
  · intro henergy c
    have hcard : 0 < (Fintype.card C : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have hinv : (Fintype.card C : ℝ)⁻¹ ≠ 0 :=
      inv_ne_zero hcard.ne'
    have hsum : (∑ d : C, ‖x - P d x‖ ^ 2) = 0 := by
      unfold groundStateJointColorNormalizedResidualEnergy at henergy
      exact (mul_eq_zero.mp henergy).resolve_left hinv
    have hterm_le :
        ‖x - P c x‖ ^ 2 ≤ ∑ d : C, ‖x - P d x‖ ^ 2 := by
      exact Finset.single_le_sum
        (fun d _hd => sq_nonneg ‖x - P d x‖)
        (Finset.mem_univ c)
    rw [hsum] at hterm_le
    have hnorm : ‖x - P c x‖ = 0 := by
      nlinarith [norm_nonneg (x - P c x)]
    have hsub : x - P c x = 0 := norm_eq_zero.mp hnorm
    exact (sub_eq_zero.mp hsub).symm
  · intro hfixed
    unfold groundStateJointColorNormalizedResidualEnergy
    simp [hfixed]

/-- Exact kernel of the genuine conventional twelve-spatial Dirichlet energy.
A ground-state joint `L²` vector has zero twelve-color residual energy exactly
when its represented real function is almost everywhere constant for the
genuine Wilson ground-state joint law.

This is qualitative definiteness modulo constants only.  It does not assert a
positive, finite-volume-uniform, or scale-uniform Poincare coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_ae_const
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H N hN beta hbeta z = 0 ↔
      ∃ c : ℝ,
        (z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) =ᵐ[
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta]
          fun _ => c := by
  change
    groundStateJointColorNormalizedResidualEnergy
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
          H N hN beta hbeta) z = 0 ↔ _
  exact
    (groundStateJointColorNormalizedResidualEnergy_eq_zero_iff_fixed
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta) z).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_fixed_iff_ae_const
        H N hN beta hbeta z)

/-- The canonical constant vector in the actual Wilson ground-state joint `L²`.
This is deliberately constructed inside the same measure-space carrier as `z`;
no identification with a transfer-operator top eigenvector is used. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (c : ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  (memLp_const c).toLp
    (fun _ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => c)

/-- Hilbert-space form of the twelve-spatial residual kernel: zero energy is
exactly equality to an actual constant vector in the ground-state joint `L²`.

This upgrades the representative-level a.e.-constant statement to equality in
`Lp` using only `MemLp.coeFn_toLp` and `Lp.ext`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_eq_constantL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H N hN beta hbeta z = 0 ↔
      ∃ c : ℝ,
        z =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
            H N hN beta hbeta c := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_ae_const]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply Lp.ext
    exact hc.trans (MemLp.coeFn_toLp (memLp_const c)).symm
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    exact MemLp.coeFn_toLp (memLp_const c)

end

end MathlibAnalytic
end MGAP4D
