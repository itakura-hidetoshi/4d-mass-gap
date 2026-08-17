import MGAP4D.MathlibAnalytic.ContinuousMidpointConvexRealHalfLine
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRealHalfLineMidpointConvexity

/-!
# Convexity of physical OS two-point correlations

The completed symmetric physical OS autocorrelation is already continuous on
the real nonnegative half-line and satisfies the standard midpoint Jensen
inequality there.  The generic compact-maximum principle now upgrades this to
full arbitrary-weight convexity.

Thus the canonical real clamp correlation is a genuine
`ConvexOn ℝ (Set.Ici 0)` function, without invoking a spectral theorem,
differentiability, a new decay estimate, or any additional physical assumption.
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

/-- The real nonnegative-time physical OS autocorrelation is fully convex. -/
theorem physicalCorrelationRealClamp_convexOn_Ici
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) :
    ConvexOn ℝ (Ici (0 : ℝ)) (T.physicalCorrelationRealClamp psi) := by
  exact
    MGAP4D.convexOn_Ici_of_continuous_midpoint
      (T.physicalCorrelationRealClamp psi)
      (T.physicalCorrelationRealClamp_continuous psi)
      (fun hs ht =>
        T.physicalCorrelationRealClamp_midpoint_le_average
          hSymmetric psi hs ht)

/-- Explicit arbitrary-weight Jensen inequality for the physical OS
autocorrelation on nonnegative real Euclidean time. -/
theorem physicalCorrelationRealClamp_jensen_two
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {s t a b : ℝ}
    (hs : s ∈ Ici (0 : ℝ)) (ht : t ∈ Ici (0 : ℝ))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    T.physicalCorrelationRealClamp psi (a * s + b * t) ≤
      a * T.physicalCorrelationRealClamp psi s +
        b * T.physicalCorrelationRealClamp psi t := by
  simpa only [smul_eq_mul] using
    (T.physicalCorrelationRealClamp_convexOn_Ici hSymmetric psi).2
      hs ht ha hb hab

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
