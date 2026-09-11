import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationStrictPositivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedLogConvex

/-!
# Unregularized logarithmic convexity of physical OS correlations

For every nonzero completed physical state, the finite-time injectivity theorem
for the strongly continuous symmetric OS semigroup gives strict positivity of
the unregularized correlation at every nonnegative semigroup time.  After the
canonical real clamp this becomes global strict positivity on `ℝ`.

Consequently the logarithm

`L(t) = log C̃_psi(t)`

is continuous and, by the already merged multiplicative midpoint inequality and
the generic positive-continuous midpoint theorem, convex on `Set.Ici 0`.

This removes the fixed-positive-`ε` obstruction from the logarithmic spine.  No
spectral theorem, differentiability, decay estimate, or additional physical
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

/-- For a nonzero physical state, the canonical real clamp correlation is
strictly positive on the whole real line. -/
theorem physicalCorrelationRealClamp_pos_of_ne_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    (t : ℝ) :
    0 < T.physicalCorrelationRealClamp psi t := by
  unfold physicalCorrelationRealClamp MGAP4D.nnrealRealClampExtension
  exact T.physicalCorrelation_pos_of_ne_zero hSymmetric t.toNNReal hpsi

/-- Unregularized logarithm of the real-clamped physical OS correlation. -/
def physicalCorrelationRealClampLog
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (t : ℝ) : ℝ :=
  Real.log (T.physicalCorrelationRealClamp psi t)

/-- For every nonzero physical state, the unregularized logarithm is continuous
on the whole real line. -/
theorem physicalCorrelationRealClampLog_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0) :
    Continuous (T.physicalCorrelationRealClampLog psi) := by
  unfold physicalCorrelationRealClampLog
  exact
    (T.physicalCorrelationRealClamp_continuous psi).log
      (fun t => (T.physicalCorrelationRealClamp_pos_of_ne_zero
        hSymmetric hpsi t).ne')

/-- The unregularized logarithm of a nonzero symmetric physical OS correlation
is fully convex on nonnegative real Euclidean time. -/
theorem physicalCorrelationRealClampLog_convexOn_Ici
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0) :
    ConvexOn ℝ (Ici (0 : ℝ))
      (T.physicalCorrelationRealClampLog psi) := by
  unfold physicalCorrelationRealClampLog
  exact
    MGAP4D.convexOn_log_Ici_of_continuous_pos_midpoint_sq_le_mul
      (fun t => T.physicalCorrelationRealClamp psi t)
      (T.physicalCorrelationRealClamp_continuous psi)
      (fun t => T.physicalCorrelationRealClamp_pos_of_ne_zero
        hSymmetric hpsi t)
      (fun hs ht =>
        T.physicalCorrelationRealClamp_midpoint_sq_le_mul
          hSymmetric psi hs ht)

/-- Explicit arbitrary-weight Jensen inequality for the unregularized
logarithm. -/
theorem physicalCorrelationRealClampLog_jensen_two
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {s t a b : ℝ}
    (hs : s ∈ Ici (0 : ℝ)) (ht : t ∈ Ici (0 : ℝ))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    T.physicalCorrelationRealClampLog psi (a * s + b * t) ≤
      a * T.physicalCorrelationRealClampLog psi s +
        b * T.physicalCorrelationRealClampLog psi t := by
  simpa only [smul_eq_mul] using
    (T.physicalCorrelationRealClampLog_convexOn_Ici
      hSymmetric hpsi).2 hs ht ha hb hab

/-- Exponential geometric-Jensen form of unregularized logarithmic convexity. -/
theorem physicalCorrelationRealClamp_le_exp_jensen_two
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {s t a b : ℝ}
    (hs : s ∈ Ici (0 : ℝ)) (ht : t ∈ Ici (0 : ℝ))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    T.physicalCorrelationRealClamp psi (a * s + b * t) ≤
      Real.exp
        (a * Real.log (T.physicalCorrelationRealClamp psi s) +
          b * Real.log (T.physicalCorrelationRealClamp psi t)) := by
  have hlog :=
    T.physicalCorrelationRealClampLog_jensen_two
      hSymmetric hpsi hs ht ha hb hab
  have hpos :
      0 < T.physicalCorrelationRealClamp psi (a * s + b * t) :=
    T.physicalCorrelationRealClamp_pos_of_ne_zero hSymmetric hpsi _
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr hlog

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
