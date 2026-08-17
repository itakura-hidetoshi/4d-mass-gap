import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUnregularizedNormalizedLogDecayLimit
import Mathlib.Tactic

/-!
# Elapsed-time normalization of unregularized physical OS logarithmic decay

For a nonzero completed physical state, the preceding layer identifies the
long-time limit of the Cesàro-normalized endpoint unregularized logarithmic
decay.  For a positive fixed sampling step `h`, the same quantity can be written
in physical elapsed-time form with denominator `t_n = n h`.

This file performs only that algebraic normalization.  No fixed positive
additive regularization, new analytic assumption, or new physical assumption is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter
open scoped Topology InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The unregularized endpoint logarithmic decay divided by physical elapsed
sampling time `n h` converges to the canonical fixed-step long-time effective
mass for every nonzero physical state. -/
theorem physicalCorrelationRealClampLogEndpoint_overElapsedTime_tendsto_effectiveMassLimit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {h : ℝ} (hh : 0 < h) :
    Tendsto
      (fun n : ℕ =>
        (T.physicalCorrelationRealClampLog psi 0 -
          T.physicalCorrelationRealClampLog psi ((n : ℝ) * h)) /
          ((n : ℝ) * h))
      atTop
      (𝓝 (T.physicalCorrelationRealClampEffectiveMassLimit psi h)) := by
  have hfun :
      (fun n : ℕ =>
        (T.physicalCorrelationRealClampLog psi 0 -
          T.physicalCorrelationRealClampLog psi ((n : ℝ) * h)) /
          ((n : ℝ) * h)) =
      (fun n : ℕ =>
        ((n : ℝ))⁻¹ *
          ((T.physicalCorrelationRealClampLog psi 0 -
              T.physicalCorrelationRealClampLog psi ((n : ℝ) * h)) / h)) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp
    · have hnR : (n : ℝ) ≠ 0 := by
        exact_mod_cast hn
      have hh0 : h ≠ 0 := ne_of_gt hh
      field_simp [hnR, hh0] <;> ring
  rw [hfun]
  exact
    T.physicalCorrelationRealClampNormalizedLogEndpoint_tendsto_effectiveMassLimit
      hSymmetric hpsi hh

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
