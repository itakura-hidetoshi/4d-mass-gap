import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkDensityOscillation
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Tactic

/-!
# Sharp one-link total variation for continuous compact Wilson conditionals

The canonical compact Wilson one-link law is Haar absolutely continuous.  We
therefore use its exact real normalized Haar density, identify its normalization,
and prove the sharp symmetric likelihood-ratio estimate

`(1/2) ∫ |p-q| ≤ (c-1)/(c+1)`.

Combining this with the canonical shared-plaquette exponent oscillation gives
an explicit total-variation influence bound for two backgrounds differing at
one source link.

This remains a static finite-volume Gibbs statement.  No heat-bath spectral
gap is identified with OS time and no physical mass-gap claim is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Real normalized Haar density underlying the canonical `ENNReal` one-link
kernel density. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkRealConditionalDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ :=
  C.singleLinkBoltzmannFactor A target g /
    C.singleLinkPartitionFunction A target

/-- The real one-link conditional density is continuous. -/
theorem continuous_compact_oriented_singleLinkRealConditionalDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Continuous (C.singleLinkRealConditionalDensity A target) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkRealConditionalDensity
  exact
    (continuous_compact_oriented_singleLinkBoltzmannFactor C A target).div_const _

/-- The real one-link conditional density is nonnegative. -/
theorem continuous_compact_oriented_singleLinkRealConditionalDensity_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    0 ≤ C.singleLinkRealConditionalDensity A target g := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkRealConditionalDensity
  exact div_nonneg (by
    unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
    exact le_of_lt (Real.exp_pos _))
    (le_of_lt
      (continuous_compact_oriented_singleLinkPartitionFunction_pos C A target))

/-- The real one-link conditional density integrates to one against normalized
compact Haar measure. -/
theorem continuous_compact_oriented_integral_singleLinkRealConditionalDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    ∫ g : C.base.Gauge,
        C.singleLinkRealConditionalDensity A target g
        ∂normalizedCompactHaar C.base.Gauge = 1 := by
  have hZ : C.singleLinkPartitionFunction A target ≠ 0 :=
    ne_of_gt
      (continuous_compact_oriented_singleLinkPartitionFunction_pos C A target)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkRealConditionalDensity
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  change C.singleLinkPartitionFunction A target *
      (C.singleLinkPartitionFunction A target)⁻¹ = 1
  exact mul_inv_cancel₀ hZ

/-- Density-based total variation of the two exact one-link Haar conditional
laws.  Since both real densities are normalized, this is their standard
`(1/2) L¹` total variation. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalTotalVariation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  (2 : ℝ)⁻¹ *
    ∫ g : C.base.Gauge,
      |C.singleLinkRealConditionalDensity A target g -
        C.singleLinkRealConditionalDensity B target g|
      ∂normalizedCompactHaar C.base.Gauge

/-- Pointwise algebraic core of the sharp symmetric likelihood-ratio bound. -/
theorem real_density_abs_sub_mul_le_of_mutual_le_mul_current
    {X : Type*}
    (p q : X → ℝ)
    (c : ℝ)
    (hc : 1 ≤ c)
    (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x)
    (hpq : ∀ x, p x ≤ c * q x)
    (hqp : ∀ x, q x ≤ c * p x)
    (x : X) :
    (c + 1) * |p x - q x| ≤
      (c - 1) * (p x + q x) := by
  by_cases h : p x ≤ q x
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    nlinarith [hp x, hq x, hqp x]
  · have h' : q x ≤ p x := le_of_not_ge h
    rw [abs_of_nonneg (sub_nonneg.mpr h')]
    nlinarith [hp x, hq x, hpq x]

/-- Sharp total-variation estimate for two continuous probability densities
with a mutual pointwise likelihood-ratio bound. -/
theorem continuous_probabilityDensity_halfL1_le_of_mutual_le_mul
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p q : X → ℝ)
    (hp_cont : Continuous p)
    (hq_cont : Continuous q)
    (hp_int : ∫ x, p x ∂μ = 1)
    (hq_int : ∫ x, q x ∂μ = 1)
    (c : ℝ)
    (hc : 1 ≤ c)
    (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x)
    (hpq : ∀ x, p x ≤ c * q x)
    (hqp : ∀ x, q x ≤ c * p x) :
    (2 : ℝ)⁻¹ * ∫ x, |p x - q x| ∂μ ≤
      (c - 1) / (c + 1) := by
  have hPoint : ∀ x : X,
      (c + 1) * |p x - q x| ≤
        (c - 1) * (p x + q x) :=
    real_density_abs_sub_mul_le_of_mutual_le_mul_current
      p q c hc hp hq hpq hqp
  have hLeftContinuous : Continuous
      (fun x : X => (c + 1) * |p x - q x|) :=
    continuous_const.mul ((hp_cont.sub hq_cont).abs)
  have hRightContinuous : Continuous
      (fun x : X => (c - 1) * (p x + q x)) :=
    continuous_const.mul (hp_cont.add hq_cont)
  have hLeftIntegrable : Integrable
      (fun x : X => (c + 1) * |p x - q x|) μ :=
    hLeftContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hRightIntegrable : Integrable
      (fun x : X => (c - 1) * (p x + q x)) μ :=
    hRightContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntegral :
      ∫ x, (c + 1) * |p x - q x| ∂μ ≤
        ∫ x, (c - 1) * (p x + q x) ∂μ :=
    integral_mono hLeftIntegrable hRightIntegrable hPoint
  rw [integral_const_mul, integral_const_mul] at hIntegral
  have hpIntegrable : Integrable p μ :=
    hp_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace p)
  have hqIntegrable : Integrable q μ :=
    hq_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace q)
  have hpqIntegral : ∫ x, p x + q x ∂μ = 2 := by
    rw [integral_add hpIntegrable hqIntegrable, hp_int, hq_int]
    norm_num
  rw [hpqIntegral] at hIntegral
  have hden : 0 < c + 1 := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Exponent-difference oscillation gives the sharp total-variation estimate
for the exact compact-Haar one-link conditional laws. -/
theorem continuous_compact_oriented_singleLinkConditionalTotalVariation_le_of_oscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc : ∀ u v : C.base.Gauge,
      (C.base.gibbsExponent (C.base.replaceLink A target u) -
          C.base.gibbsExponent (C.base.replaceLink B target u)) -
        (C.base.gibbsExponent (C.base.replaceLink A target v) -
          C.base.gibbsExponent (C.base.replaceLink B target v)) ≤ R) :
    C.singleLinkConditionalTotalVariation A B target ≤
      (Real.exp R - 1) / (Real.exp R + 1) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalTotalVariation
  apply continuous_probabilityDensity_halfL1_le_of_mutual_le_mul
    (normalizedCompactHaar C.base.Gauge)
    (C.singleLinkRealConditionalDensity A target)
    (C.singleLinkRealConditionalDensity B target)
    (continuous_compact_oriented_singleLinkRealConditionalDensity C A target)
    (continuous_compact_oriented_singleLinkRealConditionalDensity C B target)
    (continuous_compact_oriented_integral_singleLinkRealConditionalDensity C A target)
    (continuous_compact_oriented_integral_singleLinkRealConditionalDensity C B target)
    (Real.exp R) (Real.one_le_exp hR)
    (continuous_compact_oriented_singleLinkRealConditionalDensity_nonneg C A target)
    (continuous_compact_oriented_singleLinkRealConditionalDensity_nonneg C B target)
  · intro g
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkRealConditionalDensity] using
      (continuous_compact_oriented_singleLinkRealDensity_mutual_le_exp_mul_of_oscillation
        C A B target R hOsc g).1
  · intro g
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkRealConditionalDensity] using
      (continuous_compact_oriented_singleLinkRealDensity_mutual_le_exp_mul_of_oscillation
        C A B target R hOsc g).2

/-- Shared-plaquette locality gives an explicit sharp one-link conditional
TV influence bound. -/
theorem continuous_compact_oriented_singleLinkConditionalTotalVariation_le_of_shared
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (energyBound : ℝ)
    (hEnergyBound_nonneg : 0 ≤ energyBound)
    (hEnergy_le : ∀ g : C.base.Gauge,
      C.base.plaquetteEnergy g ≤ energyBound)
    (A B : C.base.Configuration)
    (target source : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B source) :
    C.singleLinkConditionalTotalVariation A B target ≤
      (Real.exp
          (C.base.beta *
            (2 * ((C.base.sharedPlaquettes target source).card : ℝ) * energyBound)) - 1) /
        (Real.exp
          (C.base.beta *
            (2 * ((C.base.sharedPlaquettes target source).card : ℝ) * energyBound)) + 1) := by
  let R : ℝ :=
    C.base.beta *
      (2 * ((C.base.sharedPlaquettes target source).card : ℝ) * energyBound)
  have hR : 0 ≤ R := by
    unfold R
    positivity
  apply
    continuous_compact_oriented_singleLinkConditionalTotalVariation_le_of_oscillation
      C A B target R hR
  intro u v
  exact
    (abs_le.mp
      (compact_oriented_gibbsExponent_sourceResponse_oscillation_abs_le_shared
        C.base energyBound hEnergyBound_nonneg hEnergy_le
        A B target source u v hAgree)).2

end

end MathlibAnalytic
end MGAP4D
