import MGAP4D.MathlibAnalytic.NNRealPairMidpointStandardForm
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationPairMidpointConvexity

/-!
# Standard midpoint convexity of physical OS correlations

The arbitrary half-time pair inequality from the previous layer is normalized
here to the ordinary midpoint statement

`2 C((s+t)/2) ≤ C(s) + C(t)`

for every pair of nonnegative Euclidean times.  The proof is entirely inherited
from the exact Hilbert-space midpoint defect; no spectral theorem,
differentiability, decay estimate, or new physical assumption is introduced.
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

/-- Standard midpoint-convexity inequality for the actual completed symmetric
physical OS autocorrelation on nonnegative Euclidean time. -/
theorem physicalCorrelation_two_mul_midpoint_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (s t : NNReal) (psi : P.PhysicalHilbert) :
    2 * T.physicalCorrelation psi ((s + t) / 2) ≤
      T.physicalCorrelation psi s + T.physicalCorrelation psi t := by
  exact
    MGAP4D.nnreal_two_mul_midpoint_le_of_pair_doubled
      (T.physicalCorrelation psi)
      (fun a b =>
        T.physicalCorrelation_two_mul_pairMidpoint_le_doubledEndpoints
          hSymmetric a b psi)
      s t

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
