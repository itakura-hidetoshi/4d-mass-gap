import MGAP4D.MathlibAnalytic.NNRealContinuousRealClampMidpointExtension
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationStandardMidpointConvexity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUniformContinuity

/-!
# Physical OS correlations on the real nonnegative half-line

The completed physical OS semigroup is naturally parameterized by `NNReal`.
For compatibility with Mathlib's real convexity API, this file constructs the
canonical real clamp extension

`C̃_ψ(t) = C_ψ(t.toNNReal)`.

It is continuous on all of `ℝ`, agrees exactly with the original physical
correlation on nonnegative times, and inherits the standard midpoint-convexity
inequality on `Set.Ici 0`.

No spectral theorem, differentiability, decay estimate, or additional physical
assumption is introduced.
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

/-- Canonical real clamp extension of the completed physical OS correlation. -/
def physicalCorrelationRealClamp
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (t : ℝ) : ℝ :=
  MGAP4D.nnrealRealClampExtension (T.physicalCorrelation psi) t

/-- The real clamp extension is continuous on the entire real line. -/
theorem physicalCorrelationRealClamp_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    Continuous (T.physicalCorrelationRealClamp psi) := by
  exact MGAP4D.nnrealRealClampExtension_continuous
    (T.physicalCorrelation psi) (T.physicalCorrelation_continuous psi)

/-- On a coerced nonnegative time the real clamp extension is exactly the
original physical OS correlation. -/
@[simp]
theorem physicalCorrelationRealClamp_coe
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (t : NNReal) :
    T.physicalCorrelationRealClamp psi (t : ℝ) =
      T.physicalCorrelation psi t := by
  exact MGAP4D.nnrealRealClampExtension_coe (T.physicalCorrelation psi) t

/-- The real clamp extension is continuous on the nonnegative half-line. -/
theorem physicalCorrelationRealClamp_continuousOn_Ici
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    ContinuousOn (T.physicalCorrelationRealClamp psi) (Ici 0) :=
  (T.physicalCorrelationRealClamp_continuous psi).continuousOn

/-- Standard midpoint inequality for every pair of nonnegative real Euclidean
times. -/
theorem physicalCorrelationRealClamp_two_mul_midpoint_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    2 * T.physicalCorrelationRealClamp psi ((s + t) / 2) ≤
      T.physicalCorrelationRealClamp psi s +
        T.physicalCorrelationRealClamp psi t := by
  exact
    MGAP4D.nnrealRealClampExtension_two_mul_midpoint_le
      (T.physicalCorrelation psi)
      (fun a b => T.physicalCorrelation_two_mul_midpoint_le
        hSymmetric a b psi)
      hs ht

/-- Average-value form, ready for the real `ConvexOn ℝ (Ici 0)` layer. -/
theorem physicalCorrelationRealClamp_midpoint_le_average
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {s t : ℝ} (hs : s ∈ Ici (0 : ℝ)) (ht : t ∈ Ici (0 : ℝ)) :
    T.physicalCorrelationRealClamp psi ((s + t) / 2) ≤
      (T.physicalCorrelationRealClamp psi s +
        T.physicalCorrelationRealClamp psi t) / 2 := by
  exact
    MGAP4D.nnrealRealClampExtension_midpoint_le_average
      (T.physicalCorrelation psi)
      (fun a b => T.physicalCorrelation_two_mul_midpoint_le
        hSymmetric a b psi)
      hs ht

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
