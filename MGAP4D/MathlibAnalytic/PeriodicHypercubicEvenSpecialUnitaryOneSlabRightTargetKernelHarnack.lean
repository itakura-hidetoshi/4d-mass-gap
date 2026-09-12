import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Rebase the exact right-link factorization at an arbitrary comparison value.
The complete one-slab kernel changes by at most the sharp local Boltzmann factor
`exp (8 * beta)` when one right-boundary spatial link is changed.  The estimate
is volume-independent and uses no division or normalization. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_le_exp_eight_mul_update_right
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
        (Function.update B target g) ≤
      Real.exp (8 * beta) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B target h) := by
  classical
  let Bh : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B target h
  have hfactor :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B target g) =
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A Bh target g *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
            (Function.update B target h) := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
        H N beta A Bh target g
    simpa [Bh] using h
  have hupper :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A Bh target g ≤ Real.exp (8 * beta) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
      H N hN beta hbeta A Bh target g
  have hkernel_nonneg :
      0 ≤ periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
        (Function.update B target h) := by
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    exact Real.exp_nonneg _
  rw [hfactor]
  exact mul_le_mul_of_nonneg_right hupper hkernel_nonneg

/-- Symmetric pairwise Harnack comparison for a one-link update of the complete
one-slab kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_pairwise_harnack
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B target g) ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
            (Function.update B target h) ∧
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B target h) ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
            (Function.update B target g) := by
  constructor
  · exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_le_exp_eight_mul_update_right
        H N hN beta hbeta A B target g h
  · exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_le_exp_eight_mul_update_right
        H N hN beta hbeta A B target h g

end

end MathlibAnalytic
end MGAP4D
