import MGAP4D.MathlibAnalytic.ConvexSecantDecayRate
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedLogConvex

/-!
# Regularized effective-mass secants of physical OS correlations

For the positive regularization `ε > 0`, the merged theorem gives convexity of

`L_ε(t) = log (C̃(t) + ε)`

on nonnegative Euclidean time.  The negative secant slope

`m_ε(s,t) = (L_ε(s) - L_ε(t)) / (t-s)`

is therefore antitone across adjacent intervals.  This is the finite-difference
effective-mass monotonicity associated with log-convexity, obtained directly
from Mathlib's convex-slope API.

No differentiability, spectral theorem, new decay estimate, or additional
physical assumption is used.
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

/-- Regularized finite-difference effective mass: the negative secant slope of
`log (C̃ + ε)`. -/
def physicalCorrelationRealClampRegularizedEffectiveMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (ε s t : ℝ) : ℝ :=
  MGAP4D.secantDecayRate
    (T.physicalCorrelationRealClampRegularizedLog psi ε) s t

/-- Adjacent regularized effective-mass secants decrease with Euclidean time. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMass_anti_adjacent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε x y z : ℝ} (hε : 0 < ε)
    (hx : x ∈ Ici (0 : ℝ)) (hz : z ∈ Ici (0 : ℝ))
    (hxy : x < y) (hyz : y < z) :
    T.physicalCorrelationRealClampRegularizedEffectiveMass psi ε y z ≤
      T.physicalCorrelationRealClampRegularizedEffectiveMass psi ε x y := by
  exact
    (T.physicalCorrelationRealClampRegularizedLog_convexOn_Ici
      hSymmetric psi hε).secantDecayRate_anti_adjacent hx hz hxy hyz

/-- Equal-width version: the regularized effective mass on the next step is no
larger than on the preceding step. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMass_step_antitone
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε s h : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hh : 0 < h) :
    T.physicalCorrelationRealClampRegularizedEffectiveMass
        psi ε (s + h) (s + 2 * h) ≤
      T.physicalCorrelationRealClampRegularizedEffectiveMass
        psi ε s (s + h) := by
  apply T.physicalCorrelationRealClampRegularizedEffectiveMass_anti_adjacent
    hSymmetric psi hε
  · exact hs
  · linarith
  · linarith
  · linarith

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
