import MGAP4D.MathlibAnalytic.ConvexSecantDecayRate
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUnregularizedLogConvex
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedEffectiveMassNonnegative

/-!
# Unregularized effective-mass secants of physical OS correlations

For every nonzero completed physical state, the merged unregularized theorem
gives convexity of

`L(t) = log C̃_psi(t)`

on nonnegative Euclidean time.  Define the finite-difference effective mass by

`m(s,t) = (L(s) - L(t)) / (t-s)`.

Convexity makes adjacent secants antitone, while antitonicity and strict
positivity of the underlying physical correlation make `L` antitone and hence
all ordered effective-mass secants nonnegative.

Thus the same finite-difference decay-rate sandwich previously available only
for fixed positive regularization now holds directly at `ε = 0` for every
nonzero physical state.  No spectral theorem, differentiability, decay estimate,
or additional physical assumption is introduced.
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

/-- Unregularized finite-difference effective mass: the negative secant slope of
`log C̃_psi`. -/
def physicalCorrelationRealClampEffectiveMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (s t : ℝ) : ℝ :=
  MGAP4D.secantDecayRate
    (T.physicalCorrelationRealClampLog psi) s t

/-- Adjacent unregularized effective-mass secants decrease with Euclidean time
for every nonzero physical state. -/
theorem physicalCorrelationRealClampEffectiveMass_anti_adjacent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {x y z : ℝ}
    (hx : x ∈ Ici (0 : ℝ)) (hz : z ∈ Ici (0 : ℝ))
    (hxy : x < y) (hyz : y < z) :
    T.physicalCorrelationRealClampEffectiveMass psi y z ≤
      T.physicalCorrelationRealClampEffectiveMass psi x y := by
  exact
    MGAP4D.ConvexOn.secantDecayRate_anti_adjacent
      (T.physicalCorrelationRealClampLog_convexOn_Ici hSymmetric hpsi)
      hx hz hxy hyz

/-- Equal-width version of unregularized effective-mass antitonicity. -/
theorem physicalCorrelationRealClampEffectiveMass_step_antitone
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {s h : ℝ} (hs : 0 ≤ s) (hh : 0 < h) :
    T.physicalCorrelationRealClampEffectiveMass psi (s + h) (s + 2 * h) ≤
      T.physicalCorrelationRealClampEffectiveMass psi s (s + h) := by
  apply T.physicalCorrelationRealClampEffectiveMass_anti_adjacent
    hSymmetric hpsi
  · exact hs
  · exact show 0 ≤ s + 2 * h by positivity
  · linarith
  · linarith

/-- The unregularized logarithm is antitone because the real-clamped physical
correlation is antitone and strictly positive for nonzero states. -/
theorem physicalCorrelationRealClampLog_antitone
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0) :
    Antitone (T.physicalCorrelationRealClampLog psi) := by
  intro s t hst
  unfold physicalCorrelationRealClampLog
  have hcorr := T.physicalCorrelationRealClamp_antitone hSymmetric psi hst
  exact
    Real.log_le_log
      (T.physicalCorrelationRealClamp_pos_of_ne_zero hSymmetric hpsi t)
      hcorr

/-- Every ordered unregularized effective-mass secant is nonnegative. -/
theorem physicalCorrelationRealClampEffectiveMass_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {s t : ℝ} (hst : s ≤ t) :
    0 ≤ T.physicalCorrelationRealClampEffectiveMass psi s t := by
  have hlog :=
    T.physicalCorrelationRealClampLog_antitone hSymmetric hpsi hst
  unfold physicalCorrelationRealClampEffectiveMass
  unfold MGAP4D.secantDecayRate
  exact div_nonneg (sub_nonneg.mpr hlog) (sub_nonneg.mpr hst)

/-- Equal-width unregularized effective masses are nonnegative. -/
theorem physicalCorrelationRealClampEffectiveMass_step_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {s h : ℝ} (hh : 0 ≤ h) :
    0 ≤ T.physicalCorrelationRealClampEffectiveMass psi s (s + h) := by
  apply T.physicalCorrelationRealClampEffectiveMass_nonneg hSymmetric hpsi
  linarith

/-- On adjacent ordered intervals, the later unregularized effective mass is
nonnegative and bounded above by the earlier one. -/
theorem physicalCorrelationRealClampEffectiveMass_adjacent_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {x y z : ℝ}
    (hx : x ∈ Ici (0 : ℝ)) (hz : z ∈ Ici (0 : ℝ))
    (hxy : x < y) (hyz : y < z) :
    0 ≤ T.physicalCorrelationRealClampEffectiveMass psi y z ∧
      T.physicalCorrelationRealClampEffectiveMass psi y z ≤
        T.physicalCorrelationRealClampEffectiveMass psi x y := by
  constructor
  · exact T.physicalCorrelationRealClampEffectiveMass_nonneg
      hSymmetric hpsi hyz.le
  · exact T.physicalCorrelationRealClampEffectiveMass_anti_adjacent
      hSymmetric hpsi hx hz hxy hyz

/-- Equal-width unregularized decay-rate sandwich.  For every `h > 0`, the
next-step effective mass lies between zero and the preceding one. -/
theorem physicalCorrelationRealClampEffectiveMass_step_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {s h : ℝ} (hs : 0 ≤ s) (hh : 0 < h) :
    0 ≤ T.physicalCorrelationRealClampEffectiveMass
        psi (s + h) (s + 2 * h) ∧
      T.physicalCorrelationRealClampEffectiveMass
          psi (s + h) (s + 2 * h) ≤
        T.physicalCorrelationRealClampEffectiveMass
          psi s (s + h) := by
  constructor
  · apply T.physicalCorrelationRealClampEffectiveMass_nonneg
      hSymmetric hpsi
    linarith
  · exact T.physicalCorrelationRealClampEffectiveMass_step_antitone
      hSymmetric hpsi hs hh

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
