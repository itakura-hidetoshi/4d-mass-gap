import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumCorrelationGeometricDecay
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCorrelationInfraredLogDecay
import Mathlib.Tactic

/-!
# Geometric envelope lower bounds for physical OS logarithmic decay

The preceding vacuum-sector decay layer gives a geometric upper bound on the
actual physical OS autocorrelation at the cofinal discrete times

`tau(n,t) = n t + n t`.

Because every nonzero symmetric physical OS correlation is strictly positive,
that upper bound can be passed through `Real.log`.  Subtracting from the fixed
zero-time logarithm reverses the inequality, and division by the positive time
`tau(n,t)` yields a lower bound for the normalized physical OS logarithmic
decay.

This file deliberately stops before simplifying the geometric envelope with
`log_mul` and `log_pow`.  The next layer can normalize the left-hand side to the
one-step rate `-log (decayFactor t) / t`, keeping the analytic and algebraic
steps separate.

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

/-- The geometric autocorrelation envelope from the vacuum-sector decay package
passes monotonically through the logarithm at every discrete even time. -/
theorem VacuumSemigroupGapSlope.physicalCorrelationRealClampLog_nat_mul_add_self_le_log_geometricEnvelope
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (n : ℕ) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    T.physicalCorrelationRealClampLog psi
        (((((n : NNReal) * t) + ((n : NNReal) * t) : NNReal) : ℝ)) ≤
      Real.log (((G.decayFactor t) ^ n * ‖psi‖) ^ 2) := by
  unfold physicalCorrelationRealClampLog
  rw [T.physicalCorrelationRealClamp_coe]
  exact
    Real.log_le_log
      (T.physicalCorrelation_pos_of_ne_zero
        hSymmetric
        (((n : NNReal) * t) + ((n : NNReal) * t))
        hpsi_ne)
      (G.physicalCorrelation_nat_mul_add_self_le
        T hSymmetric t n hpsi hpsi_ne)

/-- At every positive discrete even time, the normalized physical OS log decay
is bounded below by the corresponding geometric-envelope log loss. -/
theorem VacuumSemigroupGapSlope.log_geometricEnvelope_div_time_le_normalizedLogDecayFromZero_nat_mul_add_self
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (n : ℕ) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0)
    (ht : 0 < t) (hn : 0 < n) :
    (T.physicalCorrelationRealClampLog psi 0 -
        Real.log (((G.decayFactor t) ^ n * ‖psi‖) ^ 2)) /
        (((((n : NNReal) * t) + ((n : NNReal) * t) : NNReal) : ℝ)) ≤
      T.physicalCorrelationRealClampNormalizedLogDecayFromZero psi
        (((((n : NNReal) * t) + ((n : NNReal) * t) : NNReal) : ℝ)) := by
  have hlog :=
    G.physicalCorrelationRealClampLog_nat_mul_add_self_le_log_geometricEnvelope
      T hSymmetric t n hpsi hpsi_ne
  have hnum :=
    sub_le_sub_left hlog (T.physicalCorrelationRealClampLog psi 0)
  have hnNN : (0 : NNReal) < (n : NNReal) := by
    exact_mod_cast hn
  have hnt : 0 < (n : NNReal) * t := mul_pos hnNN ht
  have htau :
      0 < ((n : NNReal) * t) + ((n : NNReal) * t) :=
    add_pos hnt hnt
  have htauReal :
      0 < (((((n : NNReal) * t) + ((n : NNReal) * t) : NNReal) : ℝ)) := by
    exact_mod_cast htau
  unfold physicalCorrelationRealClampNormalizedLogDecayFromZero
  simp only [div_eq_mul_inv]
  exact
    mul_le_mul_of_nonneg_right hnum
      (inv_nonneg.mpr htauReal.le)

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
