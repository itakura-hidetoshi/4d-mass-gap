import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumKernelHarnack
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000

/-- The complete direct ground-state one-link weight built from the canonical
continuous physical vacuum representative, before applying `ENNReal.ofReal`.

Unlike the older quotient-representative fiber weight, every factor here is a
genuine pointwise function.  The target dependence is exactly the product of
the literal one-slab Wilson kernel and the updated-right continuous vacuum. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ *
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta left *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta left (Function.update right target g) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta (Function.update right target g))

/-- `ENNReal` carrier for the complete continuous-vacuum direct ground-state
one-link weight. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal
      H N hN beta hbeta left right target g)

/-- The complete continuous-vacuum direct ground-state one-link weight is
strictly positive at every target value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal
        H N hN beta hbeta left right target g := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal
  have hlambda :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  have hleft :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta left :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta left
  have hkernel :
      0 < periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta left (Function.update right target g) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta left (Function.update right target g)
  have hright :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta (Function.update right target g) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta (Function.update right target g)
  exact mul_pos (inv_pos.mpr hlambda) (mul_pos (mul_pos hleft hkernel) hright)

/-- `ENNReal` positivity of the complete continuous-vacuum direct one-link
weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right target g := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
  exact ENNReal.ofReal_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal_pos
      H N hN beta hbeta left right target g)

/-- Complete direct one-link Harnack comparison on the continuous-vacuum
carrier.

The sharp raw-kernel factor `exp (8 * beta)` and the continuous-vacuum factor
`exp (8 * beta)` multiply, giving the explicit volume-independent complete
weight factor `exp (16 * beta)`.  The proof is division-free. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal_update_right_le_exp_sixteen_mul_update_right
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal
        H N hN beta hbeta left right target g ≤
      Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal
          H N hN beta hbeta left right target h := by
  let Bg := Function.update right target g
  let Bh := Function.update right target h
  let R : ℝ := Real.exp (8 * beta)
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let kernel := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
    H N beta
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ * omega left
  have hK : kernel left Bg ≤ R * kernel left Bh := by
    simpa [kernel, R, Bg, Bh] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_le_exp_eight_mul_update_right
        H N hN beta hbeta left right target g h
  have hOmega : omega Bg ≤ R * omega Bh := by
    simpa [omega, R, Bg, Bh] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_update_right_le_exp_eight_mul_update_right
        H N hN beta hbeta right target g h
  have hOg : 0 ≤ omega Bg :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta Bg).le
  have hKh : 0 ≤ kernel left Bh :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta left Bh).le
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hRR : R * R = Real.exp (16 * beta) := by
    dsimp [R]
    calc
      Real.exp (8 * beta) * Real.exp (8 * beta) =
          Real.exp ((8 * beta) + (8 * beta)) := by
        rw [Real.exp_add]
      _ = Real.exp (16 * beta) := by ring_nf
  have hcore :
      kernel left Bg * omega Bg ≤
        Real.exp (16 * beta) * (kernel left Bh * omega Bh) := by
    calc
      kernel left Bg * omega Bg ≤ (R * kernel left Bh) * omega Bg :=
        mul_le_mul_of_nonneg_right hK hOg
      _ ≤ (R * kernel left Bh) * (R * omega Bh) :=
        mul_le_mul_of_nonneg_left hOmega (mul_nonneg hR hKh)
      _ = (R * R) * (kernel left Bh * omega Bh) := by ring
      _ = Real.exp (16 * beta) * (kernel left Bh * omega Bh) := by rw [hRR]
  have hlambda :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  have hleft : 0 < omega left := by
    simpa [omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta left
  have hc : 0 ≤ c :=
    (mul_pos (inv_pos.mpr hlambda) hleft).le
  have hscaled := mul_le_mul_of_nonneg_left hcore hc
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal,
    Bg, Bh, R, omega, kernel, c, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- `ENNReal` form of the complete direct one-link Harnack comparison. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_update_right_le_exp_sixteen_mul_update_right
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right target g ≤
      ENNReal.ofReal (Real.exp (16 * beta)) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
          H N hN beta hbeta left right target h := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
  rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos (16 * beta)))]
  exact ENNReal.ofReal_le_ofReal
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal_update_right_le_exp_sixteen_mul_update_right
      H N hN beta hbeta left right target g h)

/-- Symmetric pairwise complete-weight Harnack comparison on the exact
continuous-vacuum direct-fiber carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_pairwise_harnack
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
          H N hN beta hbeta left right target g ≤
        ENNReal.ofReal (Real.exp (16 * beta)) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
            H N hN beta hbeta left right target h ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
          H N hN beta hbeta left right target h ≤
        ENNReal.ofReal (Real.exp (16 * beta)) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
            H N hN beta hbeta left right target g := by
  constructor
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_update_right_le_exp_sixteen_mul_update_right
        H N hN beta hbeta left right target g h
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_update_right_le_exp_sixteen_mul_update_right
        H N hN beta hbeta left right target h g

end

end MathlibAnalytic
end MGAP4D