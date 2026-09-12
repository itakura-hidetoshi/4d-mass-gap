import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalResidualMassInfluence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Observable transport difference obtained by inserting the two coupled target
link values into one fixed background configuration.  Using one common
background is what makes the integrand vanish on the diagonal of the coupling. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Gauge × C.base.Gauge) : ℝ :=
  O (C.base.replaceLink background target z.1) -
    O (C.base.replaceLink background target z.2)

/-- The fixed-background observable transport difference is continuous. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous
      (C.singleLinkConditionalOverlapObservableTransportBCF
        background target O) := by
  have hLeft : Continuous
      (fun z : C.base.Gauge × C.base.Gauge =>
        C.base.replaceLink background target z.1) :=
    (continuous_compact_oriented_replaceLink_uncurry C target).comp
      (continuous_const.prodMk continuous_fst)
  have hRight : Continuous
      (fun z : C.base.Gauge × C.base.Gauge =>
        C.base.replaceLink background target z.2) :=
    (continuous_compact_oriented_replaceLink_uncurry C target).comp
      (continuous_const.prodMk continuous_snd)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportBCF
  exact (O.continuous.comp hLeft).sub (O.continuous.comp hRight)

/-- The observable transport difference vanishes whenever the two inserted
link values agree. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_eq_zero_of_fst_eq_snd
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Gauge × C.base.Gauge)
    (hz : z.1 = z.2) :
    C.singleLinkConditionalOverlapObservableTransportBCF
        background target O z = 0 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportBCF
  rw [hz]
  exact sub_self _

/-- The fixed-background observable transport amplitude is bounded by twice the
bounded-continuous norm. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Gauge × C.base.Gauge) :
    |C.singleLinkConditionalOverlapObservableTransportBCF
        background target O z| ≤ 2 * ‖O‖ := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportBCF
  calc
    |O (C.base.replaceLink background target z.1) -
        O (C.base.replaceLink background target z.2)| ≤
      |O (C.base.replaceLink background target z.1)| +
        |O (C.base.replaceLink background target z.2)| := abs_sub _ _
    _ ≤ ‖O‖ + ‖O‖ := by
      exact add_le_add
        (by simpa [Real.norm_eq_abs] using
          O.norm_coe_le_norm (C.base.replaceLink background target z.1))
        (by simpa [Real.norm_eq_abs] using
          O.norm_coe_le_norm (C.base.replaceLink background target z.2))
    _ = 2 * ‖O‖ := (two_mul ‖O‖).symm

/-- Squared fixed-background transport is integrable under the exact overlap
coupling. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (fun z =>
        (C.singleLinkConditionalOverlapObservableTransportBCF
          background target O z) ^ 2)
      (C.singleLinkConditionalOverlapCouplingMeasure A B target) := by
  exact
    ((continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_continuous
      C background target O).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Fixed-background square transport energy of the exact conditional overlap
coupling. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ z,
    (C.singleLinkConditionalOverlapObservableTransportBCF
      background target O z) ^ 2
    ∂C.singleLinkConditionalOverlapCouplingMeasure A B target

/-- Conditional overlap transport energy is nonnegative. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.singleLinkConditionalOverlapObservableTransportEnergyBCF
      A B background target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportEnergyBCF
  exact integral_nonneg fun z => sq_nonneg _

/-- The square transport energy is localized to the off-diagonal mass of the
coupling.  This is the actual L² bridge missing from bounded-test estimates:
the integrand is zero on the diagonal and bounded by `(2 * ‖O‖)^2` elsewhere. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_le_two_norm_sq_mul_ne_diagonal_toReal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkConditionalOverlapObservableTransportEnergyBCF
        A B background target O ≤
      (2 * ‖O‖) ^ 2 *
        (C.singleLinkConditionalOverlapCouplingMeasure A B target
          {z | z.1 ≠ z.2}).toReal := by
  let μ := C.singleLinkConditionalOverlapCouplingMeasure A B target
  let S : Set (C.base.Gauge × C.base.Gauge) := {z | z.1 ≠ z.2}
  let f := C.singleLinkConditionalOverlapObservableTransportBCF
    background target O
  let c : ℝ := (2 * ‖O‖) ^ 2
  letI : IsProbabilityMeasure μ :=
    continuousCompactOriented_singleLinkConditionalOverlapCouplingMeasure_isProbability
      C A B target
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (isClosed_eq continuous_fst continuous_snd).isOpen_compl.measurableSet
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  change (∫ z, (f z) ^ 2 ∂μ) ≤ c * (μ S).toReal
  by_cases hc : c = 0
  · have hnorm : ‖O‖ = 0 := by
      dsimp [c] at hc
      nlinarith [norm_nonneg O]
    have hfzero : ∀ z, f z = 0 := by
      intro z
      have hAbs : |f z| ≤ 0 := by
        simpa [f, hnorm] using
          continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_abs_le
            C background target O z
      exact abs_eq_zero.mp (le_antisymm hAbs (abs_nonneg _))
    simp_rw [hfzero]
    simp [hc]
  · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
    have hScaled :
        ENNReal.ofReal (∫ z, (f z) ^ 2 / c ∂μ) ≤ μ S := by
      apply integral_le_measure
      · intro z hz
        have hAbs : |f z| ≤ 2 * ‖O‖ := by
          simpa [f] using
            continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_abs_le
              C background target O z
        have hSq : (f z) ^ 2 ≤ c := by
          dsimp [c]
          have hBounds := abs_le.mp hAbs
          nlinarith [norm_nonneg O]
        exact (div_le_one hcpos).2 hSq
      · intro z hz
        have hEq : z.1 = z.2 := by
          simpa [S] using hz
        have hfEq : f z = 0 := by
          simpa [f] using
            continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_eq_zero_of_fst_eq_snd
              C background target O z hEq
        simp [hfEq]
    have hMuTop : μ S ≠ ∞ := measure_ne_top μ S
    have hScaledReal :
        (∫ z, (f z) ^ 2 / c ∂μ) ≤ (μ S).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hMuTop).1 hScaled
    have hIntegralDiv :
        (∫ z, (f z) ^ 2 / c ∂μ) =
          (∫ z, (f z) ^ 2 ∂μ) / c := by
      rw [integral_div]
    rw [hIntegralDiv] at hScaledReal
    have hFinal := (div_le_iff₀ hcpos).1 hScaledReal
    simpa [mul_comm] using hFinal

/-- Mutual real-density domination bounds the square observable transport energy
by the sharp likelihood-ratio coefficient. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_le_coefficient_of_densityRatioReal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (K : ℝ)
    (hK : 1 ≤ K)
    (hRatio : ∀ g : C.base.Gauge,
      C.singleLinkConditionalDensityReal A target g ≤
          K * C.singleLinkConditionalDensityReal B target g ∧
        C.singleLinkConditionalDensityReal B target g ≤
          K * C.singleLinkConditionalDensityReal A target g) :
    C.singleLinkConditionalOverlapObservableTransportEnergyBCF
        A B background target O ≤
      (2 * ‖O‖) ^ 2 * HaarLikelihoodRatioInfluence.coefficient K := by
  let μ := C.singleLinkConditionalOverlapCouplingMeasure A B target
  let S : Set (C.base.Gauge × C.base.Gauge) := {z | z.1 ≠ z.2}
  have hMass : μ S ≤
      ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K) :=
    le_trans
      (continuous_compact_oriented_singleLinkConditionalOverlapCouplingMeasure_ne_diagonal_le
        C A B target)
      (continuous_compact_oriented_singleLinkConditionalResidualMass_le_of_densityRatioReal
        C A B target K hK hRatio)
  have hCoeff0 : 0 ≤ HaarLikelihoodRatioInfluence.coefficient K := by
    unfold HaarLikelihoodRatioInfluence.coefficient
    exact div_nonneg (sub_nonneg.mpr hK) (by linarith)
  have hMassReal : (μ S).toReal ≤ HaarLikelihoodRatioInfluence.coefficient K :=
    ENNReal.toReal_le_of_le_ofReal hCoeff0 hMass
  calc
    C.singleLinkConditionalOverlapObservableTransportEnergyBCF
        A B background target O ≤
      (2 * ‖O‖) ^ 2 * (μ S).toReal := by
        simpa [μ, S] using
          continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_le_two_norm_sq_mul_ne_diagonal_toReal
            C A B background target O
    _ ≤ (2 * ‖O‖) ^ 2 *
        HaarLikelihoodRatioInfluence.coefficient K := by
      exact mul_le_mul_of_nonneg_left hMassReal (sq_nonneg _)

/-- A nonnegative log-density oscillation radius bounds the square observable
transport energy by the named compact-Haar influence. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_le_compactHaarOscillationInfluence_of_densityRatio
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio : ∀ g : C.base.Gauge,
      C.singleLinkConditionalDensityReal A target g ≤
          Real.exp R * C.singleLinkConditionalDensityReal B target g ∧
        C.singleLinkConditionalDensityReal B target g ≤
          Real.exp R * C.singleLinkConditionalDensityReal A target g) :
    C.singleLinkConditionalOverlapObservableTransportEnergyBCF
        A B background target O ≤
      (2 * ‖O‖) ^ 2 * compactHaarOscillationInfluence R := by
  simpa [compactHaarOscillationInfluence] using
    continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_le_coefficient_of_densityRatioReal
      C A B background target O (Real.exp R) (Real.one_le_exp hR) hRatio

/-- Gibbs-exponent oscillation control gives the sharp square observable
transport-energy estimate. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_le_compactHaarOscillationInfluence_of_oscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc : ∀ u v : C.base.Gauge,
      (C.base.gibbsExponent (C.base.replaceLink A target u) -
        C.base.gibbsExponent (C.base.replaceLink B target u)) -
      (C.base.gibbsExponent (C.base.replaceLink A target v) -
        C.base.gibbsExponent (C.base.replaceLink B target v)) ≤ R) :
    C.singleLinkConditionalOverlapObservableTransportEnergyBCF
        A B background target O ≤
      (2 * ‖O‖) ^ 2 * compactHaarOscillationInfluence R := by
  apply
    continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_le_compactHaarOscillationInfluence_of_densityRatio
      C A B background target O R hR
  intro g
  exact continuous_compact_oriented_singleLinkConditionalDensityReal_mutual_le
    C A B target R hOsc g

end

end MathlibAnalytic
end MGAP4D
