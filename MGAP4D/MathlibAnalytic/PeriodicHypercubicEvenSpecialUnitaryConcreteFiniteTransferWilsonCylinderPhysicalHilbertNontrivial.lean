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
      (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)) (by norm_num) (by norm_num))

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
  have hnorm := congrArg norm hzero
  simpa using hnorm

/-- The finite-volume Gauss-law physical Hilbert carrier is genuinely nontrivial,
proved from its normalized constant-one vacuum rather than installed as an
assumption. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert_nontrivial
    (H N : ℕ) :
    Nontrivial (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  ⟨⟨periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum H N,
      0,
      periodicHypercubicEvenSpecialUnitaryTransferWordPhysicalVacuum_ne_zero H N⟩⟩

/-- Once physical-carrier nontriviality is generated from the vacuum, every
unit shifted Wilson transfer has a strictly positive canonical Neumann radius. -/
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
  exact inv_pos.mpr (Units.norm_pos u⁻¹)

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
