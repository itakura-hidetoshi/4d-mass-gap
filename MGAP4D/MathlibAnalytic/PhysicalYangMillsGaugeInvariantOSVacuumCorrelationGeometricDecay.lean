import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumSectorDecayIteration
import Mathlib.Tactic

/-!
# Geometric decay of vacuum-orthogonal physical OS correlations

The preceding semigroup layer gives, for every fixed nonnegative Euclidean-time
step `t`, the iterated norm estimate

`‖T_{n t} psi‖ ≤ (decayFactor t)^n ‖psi‖`

on nonzero states orthogonal to the physical vacuum.  This file converts that
operator-norm estimate into the corresponding physical OS autocorrelation
bound at the even times `n t + n t`.

The first point is that symmetry and finite-time injectivity force every scalar
`decayFactor t` occurring in a `VacuumSemigroupGapSlope` package to be strictly
positive on a nonzero vacuum-orthogonal state.  Hence the geometric factors are
honest positive logarithmic decay factors for the next layer.

No spectral theorem, PVM, exponential-decay hypothesis, self-adjointness
assumption, or new physical axiom is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- On a nonzero vacuum-orthogonal state, every one-step decay factor is
strictly positive.  If it vanished, the continuum decay estimate would force a
finite-time physical semigroup vector to vanish, contradicting injectivity. -/
theorem VacuumSemigroupGapSlope.decayFactor_pos_of_orthogonal_ne_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    0 < G.decayFactor t := by
  have hd_nonneg : 0 ≤ G.decayFactor t :=
    G.decayFactor_nonneg_of_orthogonal_ne_zero T t hpsi hpsi_ne
  have hoperator_ne :
      T.toPhysicalSemigroup.operator t psi ≠ 0 :=
    T.physicalOperator_ne_zero_of_innerSymmetric
      hSymmetric t hpsi_ne
  have hnorm_pos :
      0 < ‖T.toPhysicalSemigroup.operator t psi‖ :=
    norm_pos_iff.mpr hoperator_ne
  have hdecay := G.decay t psi hpsi
  by_contra hnot
  have hd_le : G.decayFactor t ≤ 0 := le_of_not_gt hnot
  have hd_zero : G.decayFactor t = 0 := le_antisymm hd_le hd_nonneg
  rw [hd_zero, zero_mul] at hdecay
  linarith

/-- The iterated vacuum-sector norm estimate gives geometric decay of the
physical OS autocorrelation at the even time `n t + n t`. -/
theorem VacuumSemigroupGapSlope.physicalCorrelation_nat_mul_add_self_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (n : ℕ) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    T.physicalCorrelation psi
        (((n : NNReal) * t) + ((n : NNReal) * t)) ≤
      ((G.decayFactor t) ^ n * ‖psi‖) ^ 2 := by
  rw [T.physicalCorrelation_add_self_eq_norm_sq hSymmetric]
  have hnorm :=
    G.decay_nat_mul T hSymmetric t n hpsi hpsi_ne
  have hleft :
      0 ≤ ‖T.toPhysicalSemigroup.operator ((n : NNReal) * t) psi‖ :=
    norm_nonneg _
  have hd_nonneg : 0 ≤ G.decayFactor t :=
    G.decayFactor_nonneg_of_orthogonal_ne_zero T t hpsi hpsi_ne
  have hright :
      0 ≤ (G.decayFactor t) ^ n * ‖psi‖ :=
    mul_nonneg (pow_nonneg hd_nonneg n) (norm_nonneg psi)
  nlinarith

/-- The same geometric autocorrelation estimate, expressed through the
finite-volume vacuum-gap transfer package. -/
theorem FiniteVolumeVacuumGapTransfer.physicalCorrelation_nat_mul_add_self_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (n : ℕ) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    T.physicalCorrelation psi
        (((n : NNReal) * t) + ((n : NNReal) * t)) ≤
      ((G.decayFactor t) ^ n * ‖psi‖) ^ 2 := by
  exact
    G.toVacuumSemigroupGapSlope.physicalCorrelation_nat_mul_add_self_le
      T hSymmetric t n hpsi hpsi_ne

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
