import MGAP4D.MathlibAnalytic.NonnegativeRealSequenceCiInfBounds
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUnregularizedEffectiveMassLimit

/-!
# Bounds for the long-time unregularized physical OS effective mass

For a nonzero completed physical state, the fixed-step unregularized physical OS
effective-mass limit is the conditional infimum of a nonnegative discrete
sequence.  It is therefore nonnegative and lies below every finite-time sampled
effective mass.

These bounds are the order interface needed before identifying the unregularized
long-time limit with Cesàro/telescoping logarithmic decay.  No differentiability,
spectral theorem, new decay estimate, or additional physical assumption is
introduced.
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

/-- The fixed-step long-time unregularized physical OS effective mass is
nonnegative for every nonzero physical state. -/
theorem physicalCorrelationRealClampEffectiveMassLimit_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ T.physicalCorrelationRealClampEffectiveMassLimit psi h := by
  unfold physicalCorrelationRealClampEffectiveMassLimit
  exact
    (MGAP4D.nonnegativeRealSequence_ciInf_bounds
      (T.physicalCorrelationRealClampEffectiveMassSequence psi h)
      (T.physicalCorrelationRealClampEffectiveMassSequence_nonneg
        hSymmetric hpsi hh)).1

/-- The long-time unregularized effective-mass limit lies below every
finite-time sample of the same fixed-step sequence. -/
theorem physicalCorrelationRealClampEffectiveMassLimit_le_sequence
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    T.physicalCorrelationRealClampEffectiveMassLimit psi h ≤
      T.physicalCorrelationRealClampEffectiveMassSequence psi h n := by
  unfold physicalCorrelationRealClampEffectiveMassLimit
  exact
    (MGAP4D.nonnegativeRealSequence_ciInf_bounds
      (T.physicalCorrelationRealClampEffectiveMassSequence psi h)
      (T.physicalCorrelationRealClampEffectiveMassSequence_nonneg
        hSymmetric hpsi hh)).2 n

/-- Combined long-time unregularized decay-rate sandwich against an arbitrary
sampled finite-time effective mass. -/
theorem physicalCorrelationRealClampEffectiveMassLimit_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    0 ≤ T.physicalCorrelationRealClampEffectiveMassLimit psi h ∧
      T.physicalCorrelationRealClampEffectiveMassLimit psi h ≤
        T.physicalCorrelationRealClampEffectiveMassSequence psi h n := by
  exact ⟨
    T.physicalCorrelationRealClampEffectiveMassLimit_nonneg
      hSymmetric hpsi hh,
    T.physicalCorrelationRealClampEffectiveMassLimit_le_sequence
      hSymmetric hpsi hh n⟩

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
