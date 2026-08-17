import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedNormalizedLogDecayLimit
import Mathlib.Tactic

/-!
# Elapsed-time normalization of regularized physical OS logarithmic decay

The preceding layer identifies the long-time limit of the Cesàro-normalized
endpoint logarithmic decay.  For a positive fixed sampling step `h`, the same
quantity can be written in the physical elapsed-time form with denominator
`tₙ = n h`.

This file performs only that algebraic normalization.  No new analytic or
physical assumption is introduced.
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

/-- The regularized endpoint logarithmic decay divided by the physical elapsed
sampling time `n h` converges to the canonical long-time regularized effective
mass. -/
theorem physicalCorrelationRealClampRegularizedLogEndpoint_overElapsedTime_tendsto_effectiveMassLimit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) :
    Tendsto
      (fun n : ℕ =>
        (T.physicalCorrelationRealClampRegularizedLog psi ε 0 -
          T.physicalCorrelationRealClampRegularizedLog psi ε ((n : ℝ) * h)) /
          ((n : ℝ) * h))
      atTop
      (𝓝 (T.physicalCorrelationRealClampRegularizedEffectiveMassLimit psi ε h)) := by
  have hfun :
      (fun n : ℕ =>
        (T.physicalCorrelationRealClampRegularizedLog psi ε 0 -
          T.physicalCorrelationRealClampRegularizedLog psi ε ((n : ℝ) * h)) /
          ((n : ℝ) * h)) =
      (fun n : ℕ =>
        ((n : ℝ))⁻¹ *
          ((T.physicalCorrelationRealClampRegularizedLog psi ε 0 -
              T.physicalCorrelationRealClampRegularizedLog psi ε ((n : ℝ) * h)) / h)) := by
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
    T.physicalCorrelationRealClampRegularizedNormalizedLogEndpoint_tendsto_effectiveMassLimit
      hSymmetric psi hε hh

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
