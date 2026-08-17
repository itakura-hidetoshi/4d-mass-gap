import MGAP4D.MathlibAnalytic.NNRealRealClampAntitone
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedEffectiveMass

/-!
# Nonnegativity of regularized physical OS effective-mass secants

The completed symmetric physical OS correlation is already antitone on
`NNReal`, by contraction of the semigroup.  Monotonicity of `Real.toNNReal`
therefore transfers this to the canonical real clamp correlation.

For every `ε > 0`, adding `ε` preserves antitonicity and strict positivity, so
its logarithm is antitone as well.  Consequently every ordered secant decay
rate

`(log(C̃(s)+ε) - log(C̃(t)+ε)) / (t-s)`

is nonnegative for `s ≤ t`.

Together with the adjacent antitonicity merged previously, the regularized
finite-difference effective mass is now both nonnegative and decreasing across
successive Euclidean-time intervals.
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

/-- The real clamp physical OS correlation is antitone on all real arguments. -/
theorem physicalCorrelationRealClamp_antitone
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) :
    Antitone (T.physicalCorrelationRealClamp psi) := by
  exact
    MGAP4D.nnrealRealClampExtension_antitone
      (T.physicalCorrelation psi)
      (T.physicalCorrelation_antitone hSymmetric psi)

/-- For every positive regularization, the logarithm of the real clamp
correlation is antitone. -/
theorem physicalCorrelationRealClampRegularizedLog_antitone
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε : ℝ} (hε : 0 < ε) :
    Antitone (T.physicalCorrelationRealClampRegularizedLog psi ε) := by
  intro s t hst
  unfold physicalCorrelationRealClampRegularizedLog
  have hcorr := T.physicalCorrelationRealClamp_antitone hSymmetric psi hst
  have hsum :
      T.physicalCorrelationRealClamp psi t + ε ≤
        T.physicalCorrelationRealClamp psi s + ε :=
    add_le_add_right hcorr ε
  exact
    Real.log_le_log
      (add_pos_of_nonneg_of_pos
        (T.physicalCorrelationRealClamp_nonneg hSymmetric psi t) hε)
      hsum

/-- Every ordered regularized effective-mass secant is nonnegative. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMass_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε s t : ℝ} (hε : 0 < ε) (hst : s ≤ t) :
    0 ≤ T.physicalCorrelationRealClampRegularizedEffectiveMass psi ε s t := by
  have hlog :=
    T.physicalCorrelationRealClampRegularizedLog_antitone
      hSymmetric psi hε hst
  unfold physicalCorrelationRealClampRegularizedEffectiveMass
  unfold MGAP4D.secantDecayRate
  exact div_nonneg (sub_nonneg.mpr hlog) (sub_nonneg.mpr hst)

/-- Equal-width regularized effective masses are nonnegative. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMass_step_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε s h : ℝ} (hε : 0 < ε) (hh : 0 ≤ h) :
    0 ≤ T.physicalCorrelationRealClampRegularizedEffectiveMass
      psi ε s (s + h) := by
  apply T.physicalCorrelationRealClampRegularizedEffectiveMass_nonneg
    hSymmetric psi hε
  linarith

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
