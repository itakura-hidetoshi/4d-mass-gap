import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Any two values of the exact right-target local Boltzmann factor are
comparable by the volume-independent Harnack constant `exp (16 * beta)`.

This is the normalized-density-ready form of the pointwise `exp (±8 beta)`
bounds: no lattice-volume factor enters. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_sixteen_mul_localFactor
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g ≤
      Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target h := by
  calc
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g ≤ Real.exp (8 * beta) :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
        H N hN beta hbeta A B target g
    _ = Real.exp (16 * beta) * Real.exp (-8 * beta) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target h := by
      exact mul_le_mul_of_nonneg_left
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
          H N hN beta hbeta A B target h)
        (le_of_lt (Real.exp_pos _))

/-- Symmetric two-sided Harnack comparison for the exact local factors. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pairwise_harnack
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g ≤
        Real.exp (16 * beta) *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target h ∧
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target h ≤
        Real.exp (16 * beta) *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g := by
  constructor
  · exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_sixteen_mul_localFactor
        H N hN beta hbeta A B target g h
  · exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_sixteen_mul_localFactor
        H N hN beta hbeta A B target h g

end

end MathlibAnalytic
end MGAP4D
