import MGAP4D.MathlibAnalytic.NNRealForwardMidpointPairConvexity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationMidpointConvexity

/-!
# Pairwise midpoint convexity of physical OS correlations

The previous physical theorem expresses midpoint convexity in forward form,
with endpoints `2a` and `2(a+d)`.  The generic `NNReal` symmetrization lemma
shows that this already covers an arbitrary pair of nonnegative half-times.

Thus a symmetric physical OS autocorrelation satisfies

`2 C(a+b) ≤ C(2a) + C(2b)`

for every `a,b ≥ 0`.  This is the pairwise midpoint inequality in the natural
half-time coordinates and uses no spectral theorem, differentiability, decay
estimate, or additional physical assumption.
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

/-- Pairwise midpoint inequality for the actual completed physical OS
correlation.  In half-time coordinates, the midpoint of the doubled endpoints
`2a` and `2b` is exactly `a+b`. -/
theorem physicalCorrelation_two_mul_pairMidpoint_le_doubledEndpoints
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (a b : NNReal) (psi : P.PhysicalHilbert) :
    2 * T.physicalCorrelation psi (a + b) ≤
      T.physicalCorrelation psi (a + a) +
        T.physicalCorrelation psi (b + b) := by
  exact
    MGAP4D.nnreal_two_mul_add_le_add_doubled_of_forward_midpoint
      (T.physicalCorrelation psi)
      (fun x d =>
        T.physicalCorrelation_two_mul_midpoint_le_endpoints
          hSymmetric x d psi)
      a b

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
