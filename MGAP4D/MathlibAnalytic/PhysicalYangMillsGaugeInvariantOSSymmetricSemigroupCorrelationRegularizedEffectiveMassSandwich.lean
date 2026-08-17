import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedEffectiveMassNonnegative

/-!
# Regularized effective-mass decay-rate sandwiches

The two preceding physical OS layers prove complementary facts about the
positive-regularized finite-difference effective mass:

* every ordered secant is nonnegative;
* adjacent secants decrease as Euclidean time advances.

This file packages those facts into a single interval estimate, first for an
arbitrary adjacent triple and then for equal-width time steps.  The resulting
API is the convenient input for a later long-time infimum/limit construction.

No differentiability, spectral theorem, new decay estimate, or additional
physical assumption is introduced.
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

/-- On adjacent ordered intervals, the later regularized effective mass is
nonnegative and bounded above by the earlier one. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMass_adjacent_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε x y z : ℝ} (hε : 0 < ε)
    (hx : x ∈ Ici (0 : ℝ)) (hz : z ∈ Ici (0 : ℝ))
    (hxy : x < y) (hyz : y < z) :
    0 ≤ T.physicalCorrelationRealClampRegularizedEffectiveMass psi ε y z ∧
      T.physicalCorrelationRealClampRegularizedEffectiveMass psi ε y z ≤
        T.physicalCorrelationRealClampRegularizedEffectiveMass psi ε x y := by
  constructor
  · exact T.physicalCorrelationRealClampRegularizedEffectiveMass_nonneg
      hSymmetric psi hε hyz.le
  · exact T.physicalCorrelationRealClampRegularizedEffectiveMass_anti_adjacent
      hSymmetric psi hε hx hz hxy hyz

/-- Equal-width decay-rate sandwich.  For every `h > 0`, the next-step
regularized effective mass lies between zero and the preceding one. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMass_step_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε s h : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hh : 0 < h) :
    0 ≤ T.physicalCorrelationRealClampRegularizedEffectiveMass
        psi ε (s + h) (s + 2 * h) ∧
      T.physicalCorrelationRealClampRegularizedEffectiveMass
          psi ε (s + h) (s + 2 * h) ≤
        T.physicalCorrelationRealClampRegularizedEffectiveMass
          psi ε s (s + h) := by
  constructor
  · apply T.physicalCorrelationRealClampRegularizedEffectiveMass_nonneg
      hSymmetric psi hε
    linarith
  · exact T.physicalCorrelationRealClampRegularizedEffectiveMass_step_antitone
      hSymmetric psi hε hs hh

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
