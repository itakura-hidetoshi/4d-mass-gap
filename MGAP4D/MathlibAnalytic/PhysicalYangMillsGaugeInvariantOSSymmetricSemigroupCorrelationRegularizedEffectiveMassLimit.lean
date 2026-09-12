import MGAP4D.MathlibAnalytic.NonnegativeAntitoneRealSequenceLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedEffectiveMassSequence

/-!
# Long-time limit of the regularized physical OS effective mass

For fixed positive regularization `ε` and positive Euclidean-time step `h`, the
sampled physical OS effective-mass sequence is nonnegative and antitone.  Its
long-time limit is therefore canonically the conditional infimum of its sampled
values.

This layer uses only Mathlib monotone convergence applied to the already merged
physical sequence theorem.  No differentiability, spectral theorem, new decay
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

/-- Long-time regularized effective mass at fixed sampling step: the infimum of
the discrete equal-width effective-mass sequence. -/
def physicalCorrelationRealClampRegularizedEffectiveMassLimit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (ε h : ℝ) : ℝ :=
  ⨅ n : ℕ,
    T.physicalCorrelationRealClampRegularizedEffectiveMassSequence psi ε h n

/-- The discrete regularized physical OS effective-mass sequence converges to
its canonical long-time infimum. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMassSequence_tendsto_limit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) :
    Tendsto
      (T.physicalCorrelationRealClampRegularizedEffectiveMassSequence psi ε h)
      atTop
      (𝓝 (T.physicalCorrelationRealClampRegularizedEffectiveMassLimit psi ε h)) := by
  unfold physicalCorrelationRealClampRegularizedEffectiveMassLimit
  exact
    MGAP4D.nonnegativeAntitoneRealSequence_tendsto_ciInf
      (T.physicalCorrelationRealClampRegularizedEffectiveMassSequence psi ε h)
      (T.physicalCorrelationRealClampRegularizedEffectiveMassSequence_antitone
        hSymmetric psi hε hh)
      (T.physicalCorrelationRealClampRegularizedEffectiveMassSequence_nonneg
        hSymmetric psi hε hh.le)

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
