import MGAP4D.MathlibAnalytic.PositiveContinuousLogMidpointConvexRealHalfLine
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRealLogMidpoint

/-!
# Regularized logarithmic convexity of physical OS correlations

The canonical real clamp physical OS autocorrelation is nonnegative everywhere:
negative real arguments are clamped to the nonnegative semigroup parameter.
For every `ε > 0`, the regularized correlation

`C̃_ε(t) = C̃(t) + ε`

is therefore strictly positive and continuous.  The merged regularized
multiplicative midpoint inequality gives

`C̃_ε((s+t)/2)^2 ≤ C̃_ε(s) C̃_ε(t)`.

Taking logarithms converts this into additive midpoint convexity, and the generic
continuous midpoint theorem upgrades it to full
`ConvexOn ℝ (Set.Ici 0)` for `log C̃_ε`.

No spectral theorem, differentiability, new decay estimate, or additional
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

/-- The canonical real clamp correlation is nonnegative on the whole real line. -/
theorem physicalCorrelationRealClamp_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) (t : ℝ) :
    0 ≤ T.physicalCorrelationRealClamp psi t := by
  unfold physicalCorrelationRealClamp MGAP4D.nnrealRealClampExtension
  exact T.physicalCorrelation_nonneg hSymmetric t.toNNReal psi

/-- Positive-regularized logarithm of the real clamp physical OS correlation. -/
def physicalCorrelationRealClampRegularizedLog
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (ε t : ℝ) : ℝ :=
  Real.log (T.physicalCorrelationRealClamp psi t + ε)

/-- For `ε > 0`, the regularized logarithm is continuous on the whole real
line. -/
theorem physicalCorrelationRealClampRegularizedLog_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (T.physicalCorrelationRealClampRegularizedLog psi ε) := by
  unfold physicalCorrelationRealClampRegularizedLog
  exact
    ((T.physicalCorrelationRealClamp_continuous psi).add continuous_const).log
      (fun t => (add_pos_of_nonneg_of_pos
        (T.physicalCorrelationRealClamp_nonneg hSymmetric psi t) hε).ne')

/-- The positive-regularized logarithm of a symmetric physical OS
correlation is fully convex on nonnegative real Euclidean time. -/
theorem physicalCorrelationRealClampRegularizedLog_convexOn_Ici
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε : ℝ} (hε : 0 < ε) :
    ConvexOn ℝ (Ici (0 : ℝ))
      (T.physicalCorrelationRealClampRegularizedLog psi ε) := by
  unfold physicalCorrelationRealClampRegularizedLog
  exact
    MGAP4D.convexOn_log_Ici_of_continuous_pos_midpoint_sq_le_mul
      (fun t => T.physicalCorrelationRealClamp psi t + ε)
      ((T.physicalCorrelationRealClamp_continuous psi).add continuous_const)
      (fun t => add_pos_of_nonneg_of_pos
        (T.physicalCorrelationRealClamp_nonneg hSymmetric psi t) hε)
      (fun hs ht =>
        T.physicalCorrelationRealClamp_add_eps_midpoint_sq_le_mul
          hSymmetric psi ε hε.le hs ht)

/-- Explicit arbitrary-weight Jensen inequality for the regularized logarithm. -/
theorem physicalCorrelationRealClampRegularizedLog_jensen_two
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε s t a b : ℝ} (hε : 0 < ε)
    (hs : s ∈ Ici (0 : ℝ)) (ht : t ∈ Ici (0 : ℝ))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    T.physicalCorrelationRealClampRegularizedLog psi ε (a * s + b * t) ≤
      a * T.physicalCorrelationRealClampRegularizedLog psi ε s +
        b * T.physicalCorrelationRealClampRegularizedLog psi ε t := by
  simpa only [smul_eq_mul] using
    (T.physicalCorrelationRealClampRegularizedLog_convexOn_Ici
      hSymmetric psi hε).2 hs ht ha hb hab

/-- Exponential geometric-Jensen form of regularized logarithmic convexity. -/
theorem physicalCorrelationRealClamp_add_eps_le_exp_jensen_two
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε s t a b : ℝ} (hε : 0 < ε)
    (hs : s ∈ Ici (0 : ℝ)) (ht : t ∈ Ici (0 : ℝ))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    T.physicalCorrelationRealClamp psi (a * s + b * t) + ε ≤
      Real.exp
        (a * Real.log (T.physicalCorrelationRealClamp psi s + ε) +
          b * Real.log (T.physicalCorrelationRealClamp psi t + ε)) := by
  have hlog :=
    T.physicalCorrelationRealClampRegularizedLog_jensen_two
      hSymmetric psi hε hs ht ha hb hab
  exact Real.le_exp_of_log_le hlog

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
