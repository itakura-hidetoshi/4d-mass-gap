import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalOverlapCoupling
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HaarLikelihoodRatioInfluence

/-- The positive part of `p - q`, written as `p - min p q`, is one half of
`|p - q| + (p - q)`. -/
theorem sub_min_eq_half_abs_add_sub
    (p q : ℝ) :
    p - min p q =
      (2 : ℝ)⁻¹ * (|p - q| + (p - q)) := by
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq, sub_self, abs_of_nonpos (sub_nonpos.mpr hpq)]
    ring
  · rw [min_eq_right hqp, abs_of_nonneg (sub_nonneg.mpr hqp)]
    ring

/-- The positive-part difference of two integrable real densities is
integrable. -/
theorem integrable_sub_min
    {α : Type*}
    [MeasurableSpace α]
    {μ : Measure α}
    {p q : α → ℝ}
    (hp : Integrable p μ)
    (hq : Integrable q μ) :
    Integrable (fun x => p x - min (p x) (q x)) μ := by
  have hDiff : Integrable (fun x => p x - q x) μ := hp.sub hq
  have hAbs : Integrable (fun x => |p x - q x|) μ := hDiff.abs
  have hAux : Integrable (fun x =>
      (2 : ℝ)⁻¹ * (|p x - q x| + (p x - q x))) μ :=
    (hAbs.add hDiff).const_mul (2 : ℝ)⁻¹
  exact hAux.congr <| Filter.Eventually.of_forall fun x =>
    (sub_min_eq_half_abs_add_sub (p x) (q x)).symm

/-- Mutual likelihood-ratio domination of two probability densities controls
exactly the integral of the unmatched positive part by the sharp coefficient
`(K - 1) / (K + 1)`. -/
theorem integral_sub_min_le_coefficient
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (p q : α → ℝ)
    (hpInt : Integrable p μ)
    (hqInt : Integrable q μ)
    (hpOne : ∫ x, p x ∂μ = 1)
    (hqOne : ∫ x, q x ∂μ = 1)
    (K : ℝ)
    (hK : 1 ≤ K)
    (hRatio : ∀ x, p x ≤ K * q x ∧ q x ≤ K * p x) :
    (∫ x, p x - min (p x) (q x) ∂μ) ≤ coefficient K := by
  have hDiffInt : Integrable (fun x => p x - q x) μ := hpInt.sub hqInt
  have hAbsInt : Integrable (fun x => |p x - q x|) μ := hDiffInt.abs
  have hSumInt : Integrable (fun x => p x + q x) μ := hpInt.add hqInt
  have hRightInt : Integrable (fun x => coefficient K * (p x + q x)) μ :=
    hSumInt.const_mul (coefficient K)
  have hAbsIntegral :
      (∫ x, |p x - q x| ∂μ) ≤ 2 * coefficient K := by
    calc
      (∫ x, |p x - q x| ∂μ) ≤
          ∫ x, coefficient K * (p x + q x) ∂μ := by
        apply integral_mono_ae hAbsInt hRightInt
        filter_upwards [] with x
        exact abs_sub_le_coefficient_mul_add K (p x) (q x) hK
          (hRatio x).1 (hRatio x).2
      _ = coefficient K * ((∫ x, p x ∂μ) + ∫ x, q x ∂μ) := by
        rw [integral_const_mul, integral_add hpInt hqInt]
      _ = 2 * coefficient K := by rw [hpOne, hqOne]; ring
  have hResidualIntegral :
      (∫ x, p x - min (p x) (q x) ∂μ) =
        (2 : ℝ)⁻¹ * ∫ x, |p x - q x| ∂μ := by
    calc
      (∫ x, p x - min (p x) (q x) ∂μ) =
          ∫ x, (2 : ℝ)⁻¹ *
            (|p x - q x| + (p x - q x)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact sub_min_eq_half_abs_add_sub (p x) (q x)
      _ = (2 : ℝ)⁻¹ *
          ((∫ x, |p x - q x| ∂μ) + ∫ x, p x - q x ∂μ) := by
        rw [integral_const_mul, integral_add hAbsInt hDiffInt]
      _ = (2 : ℝ)⁻¹ *
          ((∫ x, |p x - q x| ∂μ) +
            ((∫ x, p x ∂μ) - ∫ x, q x ∂μ)) := by
        rw [integral_sub hpInt hqInt]
      _ = (2 : ℝ)⁻¹ * ∫ x, |p x - q x| ∂μ := by
        rw [hpOne, hqOne]
        ring
  have hCoeffNonneg : 0 ≤ coefficient K := by
    unfold coefficient
    exact div_nonneg (sub_nonneg.mpr hK) (by linarith)
  rw [hResidualIntegral]
  nlinarith

end HaarLikelihoodRatioInfluence

/-- The ENNReal exact conditional density is the `ofReal` image of the named
real conditional density. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_eq_ofReal_real
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkConditionalDensity target A g =
      ENNReal.ofReal (C.singleLinkConditionalDensityReal A target g) := by
  rfl

/-- The left unmatched ENNReal density is exactly the `ofReal` image of the
positive-part difference of the two real conditional densities. -/
theorem continuous_compact_oriented_singleLinkConditionalLeftResidualDensity_eq_ofReal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkConditionalLeftResidualDensity A B target g =
      ENNReal.ofReal
        (C.singleLinkConditionalDensityReal A target g -
          min (C.singleLinkConditionalDensityReal A target g)
            (C.singleLinkConditionalDensityReal B target g)) := by
  let p := C.singleLinkConditionalDensityReal A target g
  let q := C.singleLinkConditionalDensityReal B target g
  have hp : 0 ≤ p := by
    dsimp [p, ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal]
    exact div_nonneg (Real.exp_pos _).le
      (continuous_compact_oriented_singleLinkPartitionFunction_pos C A target).le
  have hq : 0 ≤ q := by
    dsimp [q, ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal]
    exact div_nonneg (Real.exp_pos _).le
      (continuous_compact_oriented_singleLinkPartitionFunction_pos C B target).le
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalLeftResidualDensity
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapDensity
  rw [continuous_compact_oriented_singleLinkConditionalDensity_eq_ofReal_real,
    continuous_compact_oriented_singleLinkConditionalDensity_eq_ofReal_real,
    ← ENNReal.ofReal_min]
  exact (ENNReal.ofReal_sub p (le_min hp hq)).symm

/-- Real conditional densities are integrable against normalized compact Haar. -/
theorem continuous_compact_oriented_singleLinkConditionalDensityReal_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Integrable (C.singleLinkConditionalDensityReal A target)
      (normalizedCompactHaar C.base.Gauge) := by
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal] using
    (continuous_compact_oriented_singleLinkBoltzmannIntegrable C A target).div_const
      (C.singleLinkPartitionFunction A target)

/-- Real conditional densities integrate to one against normalized compact Haar. -/
theorem continuous_compact_oriented_integral_singleLinkConditionalDensityReal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    (∫ g, C.singleLinkConditionalDensityReal A target g
      ∂normalizedCompactHaar C.base.Gauge) = 1 := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal
  rw [integral_div]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
  exact div_self
    (ne_of_gt (continuous_compact_oriented_singleLinkPartitionFunction_pos C A target))

/-- The unmatched residual mass is exactly the `ofReal` image of the integral
of the real positive-part density difference. -/
theorem continuous_compact_oriented_singleLinkConditionalResidualMass_eq_ofReal_integral
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalResidualMass A B target =
      ENNReal.ofReal
        (∫ g,
          C.singleLinkConditionalDensityReal A target g -
            min (C.singleLinkConditionalDensityReal A target g)
              (C.singleLinkConditionalDensityReal B target g)
          ∂normalizedCompactHaar C.base.Gauge) := by
  let μ := normalizedCompactHaar C.base.Gauge
  let p := C.singleLinkConditionalDensityReal A target
  let q := C.singleLinkConditionalDensityReal B target
  have hpInt : Integrable p μ := by
    simpa [μ, p] using
      continuous_compact_oriented_singleLinkConditionalDensityReal_integrable
        C A target
  have hqInt : Integrable q μ := by
    simpa [μ, q] using
      continuous_compact_oriented_singleLinkConditionalDensityReal_integrable
        C B target
  have hResidualInt : Integrable (fun g => p g - min (p g) (q g)) μ :=
    HaarLikelihoodRatioInfluence.integrable_sub_min hpInt hqInt
  have hResidualNonneg : ∀ g, 0 ≤ p g - min (p g) (q g) := fun g =>
    sub_nonneg.mpr (min_le_left _ _)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalResidualMass
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalLeftResidualMeasure
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  calc
    (∫⁻ g, C.singleLinkConditionalLeftResidualDensity A B target g
        ∂normalizedCompactHaar C.base.Gauge) =
      ∫⁻ g, ENNReal.ofReal
        (C.singleLinkConditionalDensityReal A target g -
          min (C.singleLinkConditionalDensityReal A target g)
            (C.singleLinkConditionalDensityReal B target g))
        ∂normalizedCompactHaar C.base.Gauge := by
          apply lintegral_congr
          intro g
          exact
            continuous_compact_oriented_singleLinkConditionalLeftResidualDensity_eq_ofReal
              C A B target g
    _ = ENNReal.ofReal
        (∫ g,
          C.singleLinkConditionalDensityReal A target g -
            min (C.singleLinkConditionalDensityReal A target g)
              (C.singleLinkConditionalDensityReal B target g)
          ∂normalizedCompactHaar C.base.Gauge) := by
          symm
          simpa [μ, p, q] using
            ofReal_integral_eq_lintegral_ofReal hResidualInt
              (Filter.Eventually.of_forall hResidualNonneg)

/-- Mutual pointwise domination of the real exact one-link conditional
densities bounds the unmatched ENNReal mass by the sharp coefficient. -/
theorem continuous_compact_oriented_singleLinkConditionalResidualMass_le_of_densityRatioReal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (K : ℝ)
    (hK : 1 ≤ K)
    (hRatio : ∀ g : C.base.Gauge,
      C.singleLinkConditionalDensityReal A target g ≤
          K * C.singleLinkConditionalDensityReal B target g ∧
        C.singleLinkConditionalDensityReal B target g ≤
          K * C.singleLinkConditionalDensityReal A target g) :
    C.singleLinkConditionalResidualMass A B target ≤
      ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K) := by
  let μ := normalizedCompactHaar C.base.Gauge
  let p := C.singleLinkConditionalDensityReal A target
  let q := C.singleLinkConditionalDensityReal B target
  have hpInt : Integrable p μ := by
    simpa [μ, p] using
      continuous_compact_oriented_singleLinkConditionalDensityReal_integrable
        C A target
  have hqInt : Integrable q μ := by
    simpa [μ, q] using
      continuous_compact_oriented_singleLinkConditionalDensityReal_integrable
        C B target
  have hpOne : ∫ g, p g ∂μ = 1 := by
    simpa [μ, p] using
      continuous_compact_oriented_integral_singleLinkConditionalDensityReal
        C A target
  have hqOne : ∫ g, q g ∂μ = 1 := by
    simpa [μ, q] using
      continuous_compact_oriented_integral_singleLinkConditionalDensityReal
        C B target
  rw [continuous_compact_oriented_singleLinkConditionalResidualMass_eq_ofReal_integral]
  apply ENNReal.ofReal_le_ofReal
  exact HaarLikelihoodRatioInfluence.integral_sub_min_le_coefficient
    μ p q hpInt hqInt hpOne hqOne K hK hRatio

/-- A nonnegative log-density oscillation radius bounds the unmatched
conditional mass by the named compact-Haar influence. -/
theorem continuous_compact_oriented_singleLinkConditionalResidualMass_le_compactHaarOscillationInfluence_of_densityRatio
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio : ∀ g : C.base.Gauge,
      C.singleLinkConditionalDensityReal A target g ≤
          Real.exp R * C.singleLinkConditionalDensityReal B target g ∧
        C.singleLinkConditionalDensityReal B target g ≤
          Real.exp R * C.singleLinkConditionalDensityReal A target g) :
    C.singleLinkConditionalResidualMass A B target ≤
      ENNReal.ofReal (compactHaarOscillationInfluence R) := by
  simpa [compactHaarOscillationInfluence] using
    continuous_compact_oriented_singleLinkConditionalResidualMass_le_of_densityRatioReal
      C A B target (Real.exp R) (Real.one_le_exp hR) hRatio

/-- Gibbs-exponent oscillation control gives the sharp unmatched conditional
mass bound. -/
theorem continuous_compact_oriented_singleLinkConditionalResidualMass_le_compactHaarOscillationInfluence_of_oscillation
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
    C.singleLinkConditionalResidualMass A B target ≤
      ENNReal.ofReal (compactHaarOscillationInfluence R) := by
  apply
    continuous_compact_oriented_singleLinkConditionalResidualMass_le_compactHaarOscillationInfluence_of_densityRatio
      C A B target R hR
  intro g
  exact continuous_compact_oriented_singleLinkConditionalDensityReal_mutual_le
    C A B target R hOsc g

/-- The explicit overlap coupling has mismatch mass bounded by the sharp
compact-Haar influence whenever the real conditional densities satisfy the
mutual likelihood-ratio estimate. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapCouplingMeasure_ne_diagonal_le_compactHaarOscillationInfluence
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio : ∀ g : C.base.Gauge,
      C.singleLinkConditionalDensityReal A target g ≤
          Real.exp R * C.singleLinkConditionalDensityReal B target g ∧
        C.singleLinkConditionalDensityReal B target g ≤
          Real.exp R * C.singleLinkConditionalDensityReal A target g) :
    C.singleLinkConditionalOverlapCouplingMeasure A B target
        {z | z.1 ≠ z.2} ≤
      ENNReal.ofReal (compactHaarOscillationInfluence R) := by
  exact le_trans
    (continuous_compact_oriented_singleLinkConditionalOverlapCouplingMeasure_ne_diagonal_le
      C A B target)
    (continuous_compact_oriented_singleLinkConditionalResidualMass_le_compactHaarOscillationInfluence_of_densityRatio
      C A B target R hR hRatio)

end

end MathlibAnalytic
end MGAP4D
