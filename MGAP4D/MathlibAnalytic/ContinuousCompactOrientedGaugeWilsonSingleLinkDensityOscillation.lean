import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedSharedPlaquetteOscillation
import MGAP4D.MathlibAnalytic.ContinuousNormalizedExponentialOscillation

/-!
# Continuous compact Wilson one-link density under shared-plaquette oscillation

This file rebuilds only the one-link density layer needed by the current same-root
compact `SU(N)` Wilson route.

For a continuous compact oriented Wilson system it defines the exact one-link
logarithmic Gibbs weight obtained by replacing one physical link, its normalized
compact-Haar density, and proves that the already-canonical shared-plaquette
oscillation bound gives a mutual pointwise likelihood-ratio bound.

No finite-gauge Dobrushin theorem, heat-bath spectral gap, transfer-operator gap,
clustering hypothesis, or physical mass-gap identification is used here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Replacing one physical link is continuous in the inserted compact gauge value. -/
theorem continuous_compact_oriented_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Continuous (fun g : C.base.Gauge => C.base.replaceLink A target g) := by
  classical
  apply continuous_pi
  intro e
  by_cases h : e = target
  · subst e
    simpa [CompactOrientedGaugeWilsonSystem.replaceLink] using
      (continuous_id : Continuous (fun g : C.base.Gauge => g))
  · simpa [CompactOrientedGaugeWilsonSystem.replaceLink, h] using
      (continuous_const : Continuous (fun _ : C.base.Gauge => A e))

/-- Logarithmic one-link Gibbs weight on normalized compact Haar measure. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkGibbsExponent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ :=
  C.base.gibbsExponent (C.base.replaceLink A target g)

/-- The exact one-link Gibbs exponent is continuous. -/
theorem continuous_compact_oriented_singleLinkGibbsExponent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Continuous (C.singleLinkGibbsExponent A target) :=
  (continuous_compact_oriented_gibbsExponent C).comp
    (continuous_compact_oriented_replaceLink C A target)

/-- One-link compact-Haar partition function. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  continuousExpPartition
    (normalizedCompactHaar C.base.Gauge)
    (C.singleLinkGibbsExponent A target)

/-- Every continuous compact one-link partition function is strictly positive. -/
theorem continuous_compact_oriented_singleLinkPartitionFunction_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    0 < C.singleLinkPartitionFunction A target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
  exact continuousExpPartition_pos
    (normalizedCompactHaar C.base.Gauge)
    (C.singleLinkGibbsExponent A target)
    (continuous_compact_oriented_singleLinkGibbsExponent C A target)

/-- Exact normalized one-link conditional density with respect to compact Haar probability. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ :=
  continuousNormalizedExp
    (normalizedCompactHaar C.base.Gauge)
    (C.singleLinkGibbsExponent A target)
    g

/-- The one-link conditional density is strictly positive pointwise. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    0 < C.singleLinkConditionalDensity A target g := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
  unfold continuousNormalizedExp
  exact div_pos (Real.exp_pos _)
    (continuous_compact_oriented_singleLinkPartitionFunction_pos C A target)

/-- Abstract one-link exponent-difference oscillation gives a mutual normalized-density
likelihood-ratio bound. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_mutual_le_exp_mul_of_oscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (R : ℝ)
    (hOsc : ∀ u v : C.base.Gauge,
      (C.singleLinkGibbsExponent A target u -
          C.singleLinkGibbsExponent B target u) -
        (C.singleLinkGibbsExponent A target v -
          C.singleLinkGibbsExponent B target v) ≤ R)
    (g : C.base.Gauge) :
    C.singleLinkConditionalDensity A target g ≤
        Real.exp R * C.singleLinkConditionalDensity B target g ∧
      C.singleLinkConditionalDensity B target g ≤
        Real.exp R * C.singleLinkConditionalDensity A target g := by
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity] using
    (continuousNormalizedExp_mutual_le_exp_mul_of_difference_oscillation
      (normalizedCompactHaar C.base.Gauge)
      (C.singleLinkGibbsExponent A target)
      (C.singleLinkGibbsExponent B target)
      (continuous_compact_oriented_singleLinkGibbsExponent C A target)
      (continuous_compact_oriented_singleLinkGibbsExponent C B target)
      R hOsc g)

/-- The canonical shared-plaquette Gibbs-exponent oscillation estimate controls the exact
continuous compact-Haar one-link conditional density pointwise.

The two backgrounds differ only at `source`; the target conditional law is therefore affected
only through plaquettes shared by `target` and `source`. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_mutual_le_exp_mul_of_shared
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (energyBound : ℝ)
    (hEnergyBound_nonneg : 0 ≤ energyBound)
    (hEnergy_le : ∀ g : C.base.Gauge, C.base.plaquetteEnergy g ≤ energyBound)
    (A B : C.base.Configuration)
    (target source : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B source)
    (g : C.base.Gauge) :
    C.singleLinkConditionalDensity A target g ≤
        Real.exp
            (C.base.beta *
              (2 * ((C.base.sharedPlaquettes target source).card : ℝ) * energyBound)) *
          C.singleLinkConditionalDensity B target g ∧
      C.singleLinkConditionalDensity B target g ≤
        Real.exp
            (C.base.beta *
              (2 * ((C.base.sharedPlaquettes target source).card : ℝ) * energyBound)) *
          C.singleLinkConditionalDensity A target g := by
  apply
    continuous_compact_oriented_singleLinkConditionalDensity_mutual_le_exp_mul_of_oscillation
      C A B target
      (C.base.beta *
        (2 * ((C.base.sharedPlaquettes target source).card : ℝ) * energyBound))
  intro u v
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkGibbsExponent
  exact
    (abs_le.mp
      (compact_oriented_gibbsExponent_sourceResponse_oscillation_abs_le_shared
        C.base energyBound hEnergyBound_nonneg hEnergy_le
        A B target source u v hAgree)).2

end

end MathlibAnalytic
end MGAP4D
