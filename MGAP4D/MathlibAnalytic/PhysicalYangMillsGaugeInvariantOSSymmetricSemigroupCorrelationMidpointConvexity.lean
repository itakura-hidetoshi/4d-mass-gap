import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUniformContinuity

/-!
# Midpoint convexity of physical OS two-point correlations

The symmetric physical OS semigroup already supplies the exact identity

`C(2a) + C(2(a+d)) - 2 C(2a+d) = ‖T_a ψ - T_(a+d) ψ‖²`.

This file exposes the immediate positivity consequences as a clean public API.
No spectral theorem, differentiability, decay estimate, or additional physical
assumption is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The exact midpoint defect of a symmetric physical OS correlation is
nonnegative.  This is the discrete convexity inequality before any spectral
representation is invoked. -/
theorem physicalCorrelation_midpoint_secondDifference_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (a d : NNReal) (psi : P.PhysicalHilbert) :
    0 ≤
      T.physicalCorrelation psi (a + a) +
        T.physicalCorrelation psi ((a + d) + (a + d)) -
        2 * T.physicalCorrelation psi ((a + a) + d) := by
  rw [T.physicalCorrelation_midpoint_defect_eq_norm_sq hSymmetric a d psi]
  positivity

/-- Equivalent midpoint-convexity form of the same exact Hilbert-space defect:
the midpoint correlation is bounded by the arithmetic mean of the two endpoint
correlations. -/
theorem physicalCorrelation_two_mul_midpoint_le_endpoints
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (a d : NNReal) (psi : P.PhysicalHilbert) :
    2 * T.physicalCorrelation psi ((a + a) + d) ≤
      T.physicalCorrelation psi (a + a) +
        T.physicalCorrelation psi ((a + d) + (a + d)) := by
  have h := T.physicalCorrelation_midpoint_secondDifference_nonneg
    hSymmetric a d psi
  linarith

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
