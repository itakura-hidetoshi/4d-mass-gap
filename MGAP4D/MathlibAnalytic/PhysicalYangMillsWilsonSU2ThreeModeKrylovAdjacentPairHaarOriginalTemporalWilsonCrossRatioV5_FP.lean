import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSelectedTemporalLinkExactKernelFactorV5_FO
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRightFiberEnvironmentHarnackV5_FN
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberCrossRatio
import Mathlib.Tactic

/-!
# P4-Q2-FP: true Wilson temporal-link cross-ratio, with exact cancellation

FO constructs the GENUINE original Wilson one-slab kernel K and its
off-link coefficient C(A,B,e), independent of the inserted right link g.
FN constructs the GENUINE right-environment factor
  r(B,e,g) = spatialHalfWeight(B[e <- g]) * Omega(B[e <- g])
with positive pointwise value and a volume-independent exp(14 beta)
Harnack comparison.

This file connects those exact functions to the ORIGINAL normalized
continuous-vacuum ground-state one-link fiber log weight used by the
physical posterior. No conditional law is replaced:

  W(A,B,e,g) = C(A,B,e) * k_beta(A_e,g) * r(B,e,g).

Because r is independent of the LEFT boundary, the mixed left/right
four-corner log difference is EXACTLY the one-link Wilson crossing
log-energy difference. Both the arbitrary positive off-link coefficient
and the spatial/vacuum environment cancel.

This is a genuinely source- and position-specific physical Wilson
kernel identity and a prerequisite for left Haar averaging and a
quantitative per-link frame lower bound. It does NOT itself assert
a positive or volume-uniform RMS frame lower bound, summability,
a Dobrushin hypothesis, or a 4D Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 700000

/-- The exact complete ORIGINAL continuous-ground-state right-link
fiber splits into a g-independent positive off-link coefficient,
the true temporal crossing Wilson kernel, and the actual spatial/vacuum
right environment r. -/
theorem p4Q2FP_actualWilsonCompleteFiberWeight_eq_offLink_mul_temporal_mul_environment
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
        H N hN beta hbeta left right e g =
      p4Q2FO_originalWilsonOffLinkKernelCoefficient H N beta left right e *
        specialUnitaryWilsonRelativeKernel N beta (left e) g *
        p4Q2FN_originalWilsonRightFiberEnvironmentWeight
          H N hN beta hbeta right e g := by
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta left (Function.update right e g) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta (Function.update right e g) =
      _
  rw [p4Q2FO_originalWilsonSelectedRightLink_vacuumExactFactor]
  unfold p4Q2FN_originalWilsonRightFiberEnvironmentWeight
  ring

/-- The true physical conditional log-weight is the sum of a constant
off-link contribution, the genuine temporal Wilson-link logarithm,
and the real spatial/vacuum environment logarithm. -/
theorem p4Q2FP_actualWilsonCompleteFiberLogWeight_eq_logC_add_logk_add_logr
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right e g =
      Real.log (p4Q2FO_originalWilsonOffLinkKernelCoefficient
        H N beta left right e) +
      Real.log (specialUnitaryWilsonRelativeKernel N beta (left e) g) +
      Real.log (p4Q2FN_originalWilsonRightFiberEnvironmentWeight
        H N hN beta hbeta right e g) := by
  let C := p4Q2FO_originalWilsonOffLinkKernelCoefficient H N beta left right e
  let k := specialUnitaryWilsonRelativeKernel N beta (left e) g
  let r := p4Q2FN_originalWilsonRightFiberEnvironmentWeight
    H N hN beta hbeta right e g
  have hC : C ≠ 0 := (p4Q2FO_originalWilsonOffLinkKernelCoefficient_pos
    H N beta left right e).ne'
  have hk : k ≠ 0 := by
    unfold k specialUnitaryWilsonRelativeKernel
      specialUnitaryWilsonBoltzmannCentralFunction
    exact (Real.exp_pos _).ne'
  have hr : r ≠ 0 := (p4Q2FN_originalWilsonRightFiberEnvironmentWeight_pos
    H N hN beta hbeta right e g).ne'
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
  rw [p4Q2FP_actualWilsonCompleteFiberWeight_eq_offLink_mul_temporal_mul_environment]
  change Real.log (C * k * r) = Real.log C + Real.log k + Real.log r
  rw [Real.log_mul (mul_ne_zero hC hk) hr, Real.log_mul hC hk]

/-- The logarithm of the ORIGINAL one-plaquette Wilson relative kernel
is literally the Wilson action, rather than a generic transfer bound. -/
theorem p4Q2FP_originalTemporalWilsonRelativeKernel_log_eq_energy
    (N : ℕ) (beta : ℝ)
    (a g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.log (specialUnitaryWilsonRelativeKernel N beta a g) =
      -beta * specialUnitaryWilsonPlaquetteEnergy N (a⁻¹ * g) := by
  unfold specialUnitaryWilsonRelativeKernel
    specialUnitaryWilsonBoltzmannCentralFunction
  exact Real.log_exp _

/-- The genuine original Wilson left/right four-corner log cross-difference
retains ONLY the temporal SU(N) Wilson one-link factor: all g-independent
off-link constants and the unchanged right environment cancel exactly.
There is NO reliance on a coupling/small-beta expansion. -/
theorem p4Q2FP_actualWilsonCompleteFiberLog_crossDifference_eq_temporal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left₁ left₂ right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left₁ right e g -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left₁ right e h) -
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left₂ right e g -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left₂ right e h) =
    (Real.log (specialUnitaryWilsonRelativeKernel N beta (left₁ e) g) -
      Real.log (specialUnitaryWilsonRelativeKernel N beta (left₁ e) h)) -
    (Real.log (specialUnitaryWilsonRelativeKernel N beta (left₂ e) g) -
      Real.log (specialUnitaryWilsonRelativeKernel N beta (left₂ e) h)) := by
  rw [
    p4Q2FP_actualWilsonCompleteFiberLogWeight_eq_logC_add_logk_add_logr
      H N hN beta hbeta left₁ right e g,
    p4Q2FP_actualWilsonCompleteFiberLogWeight_eq_logC_add_logk_add_logr
      H N hN beta hbeta left₁ right e h,
    p4Q2FP_actualWilsonCompleteFiberLogWeight_eq_logC_add_logk_add_logr
      H N hN beta hbeta left₂ right e g,
    p4Q2FP_actualWilsonCompleteFiberLogWeight_eq_logC_add_logk_add_logr
      H N hN beta hbeta left₂ right e h]
  ring

/-- The same exact crossed response in PHYSICAL Wilson plaquette energies,
with no vacuum, volume, or normalization artifact remaining. -/
theorem p4Q2FP_actualWilsonCompleteFiberLog_crossDifference_eq_temporalEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left₁ left₂ right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left₁ right e g -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left₁ right e h) -
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left₂ right e g -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left₂ right e h) =
      -beta *
        ((specialUnitaryWilsonPlaquetteEnergy N ((left₁ e)⁻¹ * g) -
            specialUnitaryWilsonPlaquetteEnergy N ((left₁ e)⁻¹ * h)) -
          (specialUnitaryWilsonPlaquetteEnergy N ((left₂ e)⁻¹ * g) -
            specialUnitaryWilsonPlaquetteEnergy N ((left₂ e)⁻¹ * h))) := by
  rw [p4Q2FP_actualWilsonCompleteFiberLog_crossDifference_eq_temporal]
  repeat rw [p4Q2FP_originalTemporalWilsonRelativeKernel_log_eq_energy]
  ring

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2FP_actualWilsonCompleteFiberWeight_eq_offLink_mul_temporal_mul_environment
#print axioms MGAP4D.MathlibAnalytic.p4Q2FP_actualWilsonCompleteFiberLogWeight_eq_logC_add_logk_add_logr
#print axioms MGAP4D.MathlibAnalytic.p4Q2FP_originalTemporalWilsonRelativeKernel_log_eq_energy
#print axioms MGAP4D.MathlibAnalytic.p4Q2FP_actualWilsonCompleteFiberLog_crossDifference_eq_temporal
#print axioms MGAP4D.MathlibAnalytic.p4Q2FP_actualWilsonCompleteFiberLog_crossDifference_eq_temporalEnergy
