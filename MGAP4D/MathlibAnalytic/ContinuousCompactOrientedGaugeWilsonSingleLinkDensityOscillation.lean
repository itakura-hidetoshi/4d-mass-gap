import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkKernel
import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedSharedPlaquetteOscillation
import MGAP4D.MathlibAnalytic.ContinuousNormalizedExponentialOscillation

/-!
# Continuous compact Wilson one-link density under shared-plaquette oscillation

The current canonical tree already contains the exact compact-Haar one-link
conditional measure and its jointly measurable `ENNReal` density.  This file
adds only the missing quantitative bridge: oscillation of the logarithmic
one-link Gibbs response controls the normalized conditional density, and the
canonical shared-plaquette oscillation estimate supplies that oscillation.

No finite-gauge Dobrushin theorem, heat-bath spectral gap, transfer-operator
gap, clustering hypothesis, or physical mass-gap identification is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- An oscillation bound for the difference of two exact one-link log weights
controls their real normalized Haar densities pointwise. -/
theorem continuous_compact_oriented_singleLinkRealDensity_mutual_le_exp_mul_of_oscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (R : ℝ)
    (hOsc : ∀ u v : C.base.Gauge,
      (C.base.gibbsExponent (C.base.replaceLink A target u) -
          C.base.gibbsExponent (C.base.replaceLink B target u)) -
        (C.base.gibbsExponent (C.base.replaceLink A target v) -
          C.base.gibbsExponent (C.base.replaceLink B target v)) ≤ R)
    (g : C.base.Gauge) :
    C.singleLinkBoltzmannFactor A target g /
        C.singleLinkPartitionFunction A target ≤
      Real.exp R *
        (C.singleLinkBoltzmannFactor B target g /
          C.singleLinkPartitionFunction B target) ∧
    C.singleLinkBoltzmannFactor B target g /
        C.singleLinkPartitionFunction B target ≤
      Real.exp R *
        (C.singleLinkBoltzmannFactor A target g /
          C.singleLinkPartitionFunction A target) := by
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor,
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction,
    continuousExpPartition, continuousNormalizedExp] using
    (continuousNormalizedExp_mutual_le_exp_mul_of_difference_oscillation
      (normalizedCompactHaar C.base.Gauge)
      (fun u : C.base.Gauge =>
        C.base.gibbsExponent (C.base.replaceLink A target u))
      (fun u : C.base.Gauge =>
        C.base.gibbsExponent (C.base.replaceLink B target u))
      (continuous_compact_oriented_singleLinkGibbsExponent C A target)
      (continuous_compact_oriented_singleLinkGibbsExponent C B target)
      R hOsc g)

/-- The same likelihood-ratio estimate for the canonical jointly measurable
`ENNReal` one-link conditional density used by the Markov-kernel layer. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_mutual_le_of_oscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (R : ℝ)
    (hOsc : ∀ u v : C.base.Gauge,
      (C.base.gibbsExponent (C.base.replaceLink A target u) -
          C.base.gibbsExponent (C.base.replaceLink B target u)) -
        (C.base.gibbsExponent (C.base.replaceLink A target v) -
          C.base.gibbsExponent (C.base.replaceLink B target v)) ≤ R)
    (g : C.base.Gauge) :
    C.singleLinkConditionalDensity target A g ≤
        ENNReal.ofReal (Real.exp R) *
          C.singleLinkConditionalDensity target B g ∧
      C.singleLinkConditionalDensity target B g ≤
        ENNReal.ofReal (Real.exp R) *
          C.singleLinkConditionalDensity target A g := by
  have hReal :=
    continuous_compact_oriented_singleLinkRealDensity_mutual_le_exp_mul_of_oscillation
      C A B target R hOsc g
  constructor
  · unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
    calc
      ENNReal.ofReal
          (C.singleLinkBoltzmannFactor A target g /
            C.singleLinkPartitionFunction A target) ≤
        ENNReal.ofReal
          (Real.exp R *
            (C.singleLinkBoltzmannFactor B target g /
              C.singleLinkPartitionFunction B target)) :=
        ENNReal.ofReal_le_ofReal hReal.1
      _ = ENNReal.ofReal (Real.exp R) *
          ENNReal.ofReal
            (C.singleLinkBoltzmannFactor B target g /
              C.singleLinkPartitionFunction B target) := by
        rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos R))]
  · unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
    calc
      ENNReal.ofReal
          (C.singleLinkBoltzmannFactor B target g /
            C.singleLinkPartitionFunction B target) ≤
        ENNReal.ofReal
          (Real.exp R *
            (C.singleLinkBoltzmannFactor A target g /
              C.singleLinkPartitionFunction A target)) :=
        ENNReal.ofReal_le_ofReal hReal.2
      _ = ENNReal.ofReal (Real.exp R) *
          ENNReal.ofReal
            (C.singleLinkBoltzmannFactor A target g /
              C.singleLinkPartitionFunction A target) := by
        rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos R))]

/-- The canonical shared-plaquette Gibbs-exponent oscillation bound controls
the exact compact-Haar one-link conditional density pointwise.

The two backgrounds differ only at `source`; hence only plaquettes shared by
`target` and `source` enter the likelihood-ratio constant. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_mutual_le_of_shared
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (energyBound : ℝ)
    (hEnergyBound_nonneg : 0 ≤ energyBound)
    (hEnergy_le : ∀ g : C.base.Gauge,
      C.base.plaquetteEnergy g ≤ energyBound)
    (A B : C.base.Configuration)
    (target source : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B source)
    (g : C.base.Gauge) :
    C.singleLinkConditionalDensity target A g ≤
        ENNReal.ofReal
            (Real.exp
              (C.base.beta *
                (2 * ((C.base.sharedPlaquettes target source).card : ℝ) *
                  energyBound))) *
          C.singleLinkConditionalDensity target B g ∧
      C.singleLinkConditionalDensity target B g ≤
        ENNReal.ofReal
            (Real.exp
              (C.base.beta *
                (2 * ((C.base.sharedPlaquettes target source).card : ℝ) *
                  energyBound))) *
          C.singleLinkConditionalDensity target A g := by
  apply
    continuous_compact_oriented_singleLinkConditionalDensity_mutual_le_of_oscillation
      C A B target
      (C.base.beta *
        (2 * ((C.base.sharedPlaquettes target source).card : ℝ) * energyBound))
  intro u v
  exact
    (abs_le.mp
      (compact_oriented_gibbsExponent_sourceResponse_oscillation_abs_le_shared
        C.base energyBound hEnergyBound_nonneg hEnergy_le
        A B target source u v hAgree)).2

end

end MathlibAnalytic
end MGAP4D
