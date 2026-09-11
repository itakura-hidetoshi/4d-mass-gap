import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalKernelFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumLocalHarnack
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The exact local Boltzmann factor multiplying the one-slab kernel when a
single right-boundary target link is updated. -/
def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp
    (-beta *
      ((specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * g) -
          specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * B target)) +
        (1 / 2 : ℝ) *
          ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
            (specialUnitaryWilsonPlaquetteEnergy N
                (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
                  (Function.update B target g) p) -
              specialUnitaryWilsonPlaquetteEnergy N
                (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p))))

/-- The exact one-link factor is everywhere strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 < periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g := by
  exact Real.exp_pos _

/-- Repackage the exact kernel update factorization through the named local
Boltzmann factor. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
        (Function.update B target g) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B := by
  simpa [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor] using
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_targetLocalFactor
      H N beta A B target g)

/-- The logarithmic target-local factor has the same volume-independent
oscillation bound `8` as the complete one-slab action. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalIncrement_abs_le_eight
    (H N : ℕ)
    (hN : 0 < N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |(specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * g) -
        specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * B target)) +
      (1 / 2 : ℝ) *
        ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
          (specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
                (Function.update B target g) p) -
            specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p))| ≤ 8 := by
  have hosc :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_continuousVacuumReplaceLink_sub_abs_le_eight
      H N hN A B target g (B target)
  have hosc' :
      |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A
          (Function.update B target g) -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B| ≤ 8 := by
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using hosc
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_update_right_sub_eq_targetLocal]
    at hosc'
  exact hosc'

/-- Uniform lower bound for the exact target-local Boltzmann factor.  The bound
is independent of the lattice volume and of the surrounding configuration. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-8 * beta) ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g := by
  let d : ℝ :=
    (specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * g) -
        specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * B target)) +
      (1 / 2 : ℝ) *
        ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
          (specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
                (Function.update B target g) p) -
            specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p))
  have hdabs : |d| ≤ 8 := by
    simpa [d] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalIncrement_abs_le_eight
        H N hN A B target g)
  have hdle : d ≤ 8 := (abs_le.mp hdabs).2
  have hmul : -8 * beta ≤ -beta * d := by
    nlinarith [mul_le_mul_of_nonneg_left hdle hbeta]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor]
  change Real.exp (-8 * beta) ≤ Real.exp (-beta * d)
  exact Real.exp_le_exp.mpr hmul

/-- Uniform upper bound for the exact target-local Boltzmann factor. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g ≤
      Real.exp (8 * beta) := by
  let d : ℝ :=
    (specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * g) -
        specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * B target)) +
      (1 / 2 : ℝ) *
        ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
          (specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
                (Function.update B target g) p) -
            specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p))
  have hdabs : |d| ≤ 8 := by
    simpa [d] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalIncrement_abs_le_eight
        H N hN A B target g)
  have hdge : -8 ≤ d := (abs_le.mp hdabs).1
  have hmul : -beta * d ≤ 8 * beta := by
    nlinarith [mul_le_mul_of_nonneg_left hdge hbeta]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor]
  change Real.exp (-beta * d) ≤ Real.exp (8 * beta)
  exact Real.exp_le_exp.mpr hmul

end

end MathlibAnalytic
end MGAP4D
