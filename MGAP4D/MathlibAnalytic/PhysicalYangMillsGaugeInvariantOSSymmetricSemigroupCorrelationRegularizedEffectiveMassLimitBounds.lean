import MGAP4D.MathlibAnalytic.NonnegativeRealSequenceCiInfBounds
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedEffectiveMassLimit

/-!
# Bounds for the long-time regularized physical OS effective mass

The fixed-step regularized physical OS effective-mass limit is defined as the
conditional infimum of a nonnegative discrete sequence.  It is therefore
nonnegative and bounded above by every finite-time effective-mass sample.

This packages the order bounds needed before identifying the limit with a
long-time average logarithmic decay rate.
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

/-- The fixed-step long-time regularized physical OS effective mass is
nonnegative. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMassLimit_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε h : ℝ} (hε : 0 < ε) (hh : 0 ≤ h) :
    0 ≤ T.physicalCorrelationRealClampRegularizedEffectiveMassLimit psi ε h := by
  unfold physicalCorrelationRealClampRegularizedEffectiveMassLimit
  exact
    (MGAP4D.nonnegativeRealSequence_ciInf_bounds
      (T.physicalCorrelationRealClampRegularizedEffectiveMassSequence psi ε h)
      (T.physicalCorrelationRealClampRegularizedEffectiveMassSequence_nonneg
        hSymmetric psi hε hh)).1

/-- The long-time regularized effective-mass limit lies below every finite-time
sample of the same fixed-step sequence. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMassLimit_le_sequence
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε h : ℝ} (hε : 0 < ε) (hh : 0 ≤ h) (n : ℕ) :
    T.physicalCorrelationRealClampRegularizedEffectiveMassLimit psi ε h ≤
      T.physicalCorrelationRealClampRegularizedEffectiveMassSequence psi ε h n := by
  unfold physicalCorrelationRealClampRegularizedEffectiveMassLimit
  exact
    (MGAP4D.nonnegativeRealSequence_ciInf_bounds
      (T.physicalCorrelationRealClampRegularizedEffectiveMassSequence psi ε h)
      (T.physicalCorrelationRealClampRegularizedEffectiveMassSequence_nonneg
        hSymmetric psi hε hh)).2 n

/-- Combined long-time decay-rate sandwich against an arbitrary sampled
finite-time effective mass. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMassLimit_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε h : ℝ} (hε : 0 < ε) (hh : 0 ≤ h) (n : ℕ) :
    0 ≤ T.physicalCorrelationRealClampRegularizedEffectiveMassLimit psi ε h ∧
      T.physicalCorrelationRealClampRegularizedEffectiveMassLimit psi ε h ≤
        T.physicalCorrelationRealClampRegularizedEffectiveMassSequence psi ε h n := by
  exact ⟨
    T.physicalCorrelationRealClampRegularizedEffectiveMassLimit_nonneg
      hSymmetric psi hε hh,
    T.physicalCorrelationRealClampRegularizedEffectiveMassLimit_le_sequence
      hSymmetric psi hε hh n⟩

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
