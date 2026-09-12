import MGAP4D.MathlibAnalytic.NNRealContinuousRealClampLogMidpointExtension
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationLogMidpoint
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRealHalfLineMidpointConvexity

/-!
# Real-half-line multiplicative midpoint inequalities for physical OS correlations

The Hilbert-space Cauchy--Schwarz estimate already gives the multiplicative
midpoint inequality for the completed physical OS autocorrelation on `NNReal`.
This file transfers it to the canonical real clamp correlation and combines it
with the merged additive midpoint inequality.

For every `ε ≥ 0` and nonnegative real Euclidean times `s,t`, one obtains

`(C̃((s+t)/2)+ε)^2 ≤ (C̃(s)+ε)(C̃(t)+ε)`.

For `ε > 0` this is the zero-safe input for a logarithmic-convexity theorem.
No spectral theorem, differentiability, decay estimate, or additional physical
assumption is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Multiplicative midpoint inequality for the canonical real clamp physical OS
correlation on nonnegative Euclidean time. -/
theorem physicalCorrelationRealClamp_midpoint_sq_le_mul
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.physicalCorrelationRealClamp psi ((s + t) / 2) ^ 2 ≤
      T.physicalCorrelationRealClamp psi s *
        T.physicalCorrelationRealClamp psi t := by
  exact
    MGAP4D.nnrealRealClampExtension_midpoint_sq_le_mul
      (T.physicalCorrelation psi)
      (fun a b => T.physicalCorrelation_midpoint_sq_le_mul
        hSymmetric a b psi)
      hs ht

/-- Zero-safe regularized multiplicative midpoint inequality.  The case
`ε > 0` makes all three regularized correlation values strictly positive and is
therefore ready for logarithmic normalization. -/
theorem physicalCorrelationRealClamp_add_eps_midpoint_sq_le_mul
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    (ε : ℝ) (hε : 0 ≤ ε)
    {s t : ℝ} (hs : s ∈ Ici (0 : ℝ)) (ht : t ∈ Ici (0 : ℝ)) :
    (T.physicalCorrelationRealClamp psi ((s + t) / 2) + ε) ^ 2 ≤
      (T.physicalCorrelationRealClamp psi s + ε) *
        (T.physicalCorrelationRealClamp psi t + ε) := by
  exact
    MGAP4D.nnrealRealClampExtension_add_eps_midpoint_sq_le_mul
      (T.physicalCorrelation psi)
      (fun a b => T.physicalCorrelation_two_mul_midpoint_le
        hSymmetric a b psi)
      (fun a b => T.physicalCorrelation_midpoint_sq_le_mul
        hSymmetric a b psi)
      ε hε hs ht

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
