import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkConditional
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCenteredVariance

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The configuration weight seen on one Wilson resampling fiber.  In the
physical ground-state application, `Omega` is the nonnegative vacuum weight
and this is exactly `g ↦ Omega (A[target ← g])`.

The codomain is `ENNReal` so that the definition feeds directly into the
generic normalized Doob-measure API without discarding the exact normalizing
mass. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkDoobWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (Omega : C.base.Configuration → ℝ≥0∞)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ≥0∞ :=
  Omega (C.base.replaceLink A target g)

/-- The normalized Doob reweighting of the exact Wilson one-link conditional
law by a configuration weight.  No product or same-color factorization is
assumed here: this is a single-fiber object. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkDoobConditionalMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (Omega : C.base.Configuration → ℝ≥0∞)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : Measure C.base.Gauge :=
  doobWeightedMeasure
    (C.singleLinkConditionalMeasure A target)
    (C.singleLinkDoobWeight Omega A target)

/-- Audit-visible exact identification with the generic Doob construction. -/
theorem continuous_compact_oriented_singleLinkDoobConditionalMeasure_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (Omega : C.base.Configuration → ℝ≥0∞)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkDoobConditionalMeasure Omega A target =
      doobWeightedMeasure
        (C.singleLinkConditionalMeasure A target)
        (fun g => Omega (C.base.replaceLink A target g)) := by
  rfl

/-- One-link Wilson variance comparison under explicit fiberwise Doob bounds.

This is the raw-Wilson specialization of
`doobWeightedMeasure_evariance_lower_bound`.  The lower and upper constants
remain explicit fiber parameters; in particular, this theorem makes no
volume-uniformity claim and does not infer a positive uniform lower bound from
almost-everywhere positivity. -/
theorem continuous_compact_oriented_singleLinkDoob_evariance_lower_bound
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (Omega : C.base.Configuration → ℝ≥0∞)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (X : C.base.Gauge → ℝ)
    (m M : ℝ≥0∞)
    (hw : AEMeasurable (C.singleLinkDoobWeight Omega A target)
      (C.singleLinkConditionalMeasure A target))
    (hm : 0 < m)
    (hM : M < ∞)
    (hLower : ∀ g, m ≤ C.singleLinkDoobWeight Omega A target g)
    (hUpper : ∀ g, C.singleLinkDoobWeight Omega A target g ≤ M)
    (hX : MemLp X 2 (C.singleLinkConditionalMeasure A target)) :
    (m / M) * evariance X (C.singleLinkConditionalMeasure A target) ≤
      evariance X (C.singleLinkDoobConditionalMeasure Omega A target) := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  exact doobWeightedMeasure_evariance_lower_bound
    (C.singleLinkConditionalMeasure A target)
    (C.singleLinkDoobWeight Omega A target)
    X m M hw hm hM hLower hUpper hX

end

end MathlibAnalytic
end MGAP4D
