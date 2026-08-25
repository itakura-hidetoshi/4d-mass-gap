import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderQuantitativeJointResolventStability
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Ring

noncomputable section

/-- The constant-one Haar `L²` vector on the genuine spatial-slice configuration
space.  Because the spatial Haar measure is a probability measure, this vector
has norm exactly one. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTransferWordHaarVacuum
    (H N : ℕ) : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N :=
  Lp.const 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℝ)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryTransferWordHaarVacuum_norm
    (H N : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitaryTransferWordHaarVacuum H N‖ = 1 := by
  unfold periodicHypercubicEvenSpecialUnitaryTransferWordHaarVacuum
  simpa using
    (Lp.norm_const'
      (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (p := (2 : ENNReal)) (c := (1 : ℝ)) (by norm_num) (by norm_num))

/-- Constant one is fixed by every actual spatial lattice gauge pullback. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTransferWordHaarVacuum_gaugeFixed
    (H N : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry H N γ
        (periodicHypercubicEvenSpecialUnitaryTransferWordHaarVacuum H N) =
      periodicHypercubicEvenSpecialUnitaryTransferWordHaarVacuum H N := by
  unfold periodicHypercubicEvenSpecialUnitaryTransferWordHaarVacuum
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugePullbackLinearIsometry
  rfl

/-- The normalized vacuum as a genuine vector of the finite-volume Gauss-law
physical Hilbert subspace. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum
    (H N : ℕ) : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  ⟨periodicHypercubicEvenSpecialUnitaryTransferWordHaarVacuum H N, by
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_mem]
    intro γ
    exact periodicHypercubicEvenSpecialUnitaryTransferWordHaarVacuum_gaugeFixed H N γ⟩

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum_norm
    (H N : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum H N‖ = 1 := by
  change ‖periodicHypercubicEvenSpecialUnitaryTransferWordHaarVacuum H N‖ = 1
  exact periodicHypercubicEvenSpecialUnitaryTransferWordHaarVacuum_norm H N

/-- The physical vacuum cannot vanish. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum_ne_zero
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum H N ≠ 0 := by
  intro hzero
  have hnorm :=
    periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum_norm H N
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- The finite-volume Gauss-law physical Hilbert carrier is genuinely nontrivial,
proved from its normalized constant-one vacuum.  This is kept as a theorem,
rather than a global typeclass instance, so downstream spectral arguments can
install it only in the local carrier where it is actually needed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert_nontrivial
    (H N : ℕ) :
    Nontrivial (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  ⟨⟨periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum H N,
      0,
      periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum_ne_zero H N⟩⟩

/-- Once physical-carrier nontriviality is generated from the vacuum, every
unit shifted Wilson transfer has a strictly positive canonical Neumann radius.
The inverse operator is shown nonzero directly from the physical vacuum, avoiding
a global `Nontrivial` search through the reducible endomorphism carrier. -/
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
  let PH := PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N
  let Ω : PH := periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum H N
  have hΩ : Ω ≠ 0 := by
    exact periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum_ne_zero H N
  have huinv_ne : (↑(u⁻¹) : PH →L[ℝ] PH) ≠ 0 := by
    intro hzero
    have hinv_mul :
        (↑(u⁻¹) : PH →L[ℝ] PH) * (↑u : PH →L[ℝ] PH) = 1 := by
      simp
    rw [hzero, zero_mul] at hinv_mul
    have hΩzero : (0 : PH) = Ω := by
      simpa using congrArg (fun A : PH →L[ℝ] PH => A Ω) hinv_mul
    exact hΩ hΩzero.symm
  change
    (↑(u⁻¹) :
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) ≠ 0 at huinv_ne
  have hpos :
      0 < ‖(↑(u⁻¹) :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)‖ := by
    rw [norm_pos_iff]
    exact huinv_ne
  exact inv_pos.mpr hpos

/-- Audit-visible package tying the normalized Gauss-law vacuum, physical-space
nontriviality and the positive Neumann radius to the same finite Wilson carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinder_WilsonPhysicalHilbertNontrivial_package
    (H N : ℕ) (hN : 0 < N) :
    ‖periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum H N‖ = 1 ∧
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
              H N hN beta)‖⁻¹) := by
  constructor
  · exact periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum_norm H N
  · intro z beta hbeta hunit
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_shiftedInverseRadius_pos
        H N hN z beta hbeta hunit

end
end MathlibAnalytic
end MGAP4D
