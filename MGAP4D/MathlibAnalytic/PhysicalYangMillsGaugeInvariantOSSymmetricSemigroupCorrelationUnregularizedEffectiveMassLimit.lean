import MGAP4D.MathlibAnalytic.NonnegativeAntitoneRealSequenceLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUnregularizedEffectiveMassSequence

/-!
# Long-time limit of the unregularized physical OS effective mass

For a nonzero completed physical state and fixed positive Euclidean-time step
`h`, the merged unregularized effective-mass sequence is nonnegative and
antitone.  Its long-time limit is therefore canonically the conditional infimum
of its sampled values.

This is the monotone-convergence closure of the unregularized finite-difference
spine.  Unlike the fixed-positive-`ε` route, there is no additive floor forcing
this limit to vanish.  No differentiability, spectral theorem, new decay
estimate, or additional physical assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set
open scoped Topology InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Long-time unregularized effective mass at fixed sampling step: the infimum
of the discrete equal-width effective-mass sequence. -/
def physicalCorrelationRealClampEffectiveMassLimit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (h : ℝ) : ℝ :=
  ⨅ n : ℕ,
    T.physicalCorrelationRealClampEffectiveMassSequence psi h n

/-- The discrete unregularized physical OS effective-mass sequence converges to
its canonical long-time infimum for every nonzero physical state. -/
theorem physicalCorrelationRealClampEffectiveMassSequence_tendsto_limit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {h : ℝ} (hh : 0 < h) :
    Tendsto
      (T.physicalCorrelationRealClampEffectiveMassSequence psi h)
      atTop
      (𝓝 (T.physicalCorrelationRealClampEffectiveMassLimit psi h)) := by
  unfold physicalCorrelationRealClampEffectiveMassLimit
  exact
    MGAP4D.nonnegativeAntitoneRealSequence_tendsto_ciInf
      (T.physicalCorrelationRealClampEffectiveMassSequence psi h)
      (T.physicalCorrelationRealClampEffectiveMassSequence_antitone
        hSymmetric hpsi hh)
      (T.physicalCorrelationRealClampEffectiveMassSequence_nonneg
        hSymmetric hpsi hh.le)

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
