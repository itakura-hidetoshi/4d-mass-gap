import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkSharpTV
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitarySparseConditionalTVCertificate
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Tactic

/-!
# One-link conditional expectations controlled by total variation

The current compact Wilson route already provides the exact normalized Haar
one-link density and a sharp total-variation influence bound.  This file adds
the analytic comparison lemma needed before any Dobrushin-style covariance
recursion: a bounded continuous one-link test has expectation oscillation
controlled by the density total variation.

For a real test `phi` with `|phi| <= M`,

`|E_A phi - E_B phi| <= 2 M TV(A,B)`.

The final theorem specializes this directly to the actual periodic compact
`SU(N)` Wilson source and the sparse influence certificate already canonical.
This is still a static finite-volume Gibbs statement.  No Markov-update time
is identified with physical OS Euclidean time, and no factorial-continuum
small-coupling hypothesis is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Exact one-link expectation of a real gauge-variable test, written through
the canonical normalized real Haar density. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalGaugeExpectation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (phi : C.base.Gauge → ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  ∫ g, phi g * C.singleLinkRealConditionalDensity A target g
    ∂normalizedCompactHaar C.base.Gauge

/-- The real-density definition above is exactly integration against the
canonical one-link conditional probability measure. -/
theorem continuous_compact_oriented_singleLinkConditionalGaugeExpectation_eq_integral
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (phi : C.base.Gauge → ℝ)
    (hphi : Continuous phi)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalGaugeExpectation phi A target =
      ∫ g, phi g ∂C.singleLinkConditionalMeasure A target := by
  let rho : C.base.Gauge → ℝ≥0∞ :=
    fun g => ENNReal.ofReal (C.singleLinkRealConditionalDensity A target g)
  have hrho_meas : Measurable rho := by
    exact ENNReal.measurable_ofReal.comp
      (continuous_compact_oriented_singleLinkRealConditionalDensity
        C A target).measurable
  have hrho_lt_top : ∀ᵐ g ∂normalizedCompactHaar C.base.Gauge, rho g < ∞ :=
    Filter.Eventually.of_forall fun g => by simp [rho]
  rw [continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalGaugeExpectation
  change
    (∫ g, phi g * C.singleLinkRealConditionalDensity A target g
      ∂normalizedCompactHaar C.base.Gauge) =
      ∫ g, phi g
        ∂(normalizedCompactHaar C.base.Gauge).withDensity rho
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hrho_meas.aemeasurable hrho_lt_top phi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g => by
    rw [ENNReal.toReal_ofReal
      (continuous_compact_oriented_singleLinkRealConditionalDensity_nonneg
        C A target g)]
    change phi g * C.singleLinkRealConditionalDensity A target g =
      C.singleLinkRealConditionalDensity A target g * phi g
    ring

/-- Analytic core: two continuous densities tested against the same bounded
continuous function differ by at most `2 M` times their half-`L1` distance. -/
theorem continuous_probabilityDensity_boundedTest_expectation_sub_abs_le_halfL1
    {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (phi p q : X → ℝ)
    (hphi : Continuous phi)
    (hp : Continuous p)
    (hq : Continuous q)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hphi_bound : ∀ x, |phi x| ≤ M) :
    |(∫ x, phi x * p x ∂mu) - (∫ x, phi x * q x ∂mu)| ≤
      2 * M * ((2 : ℝ)⁻¹ * ∫ x, |p x - q x| ∂mu) := by
  have hpInt : Integrable (fun x => phi x * p x) mu :=
    (hphi.mul hp).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hqInt : Integrable (fun x => phi x * q x) mu :=
    (hphi.mul hq).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hdiffCont : Continuous (fun x => phi x * (p x - q x)) :=
    hphi.mul (hp.sub hq)
  have hdiffAbsInt : Integrable (fun x => |phi x * (p x - q x)|) mu :=
    hdiffCont.abs.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmajorInt : Integrable (fun x => M * |p x - q x|) mu :=
    (continuous_const.mul (hp.sub hq).abs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hpInt hqInt]
  have hrewrite :
      (fun x => phi x * p x - phi x * q x) =
        (fun x => phi x * (p x - q x)) := by
    funext x
    ring
  rw [hrewrite]
  calc
    |∫ x, phi x * (p x - q x) ∂mu| ≤
        ∫ x, |phi x * (p x - q x)| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, M * |p x - q x| ∂mu := by
      apply integral_mono hdiffAbsInt hmajorInt
      intro x
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hphi_bound x) (abs_nonneg _)
    _ = M * ∫ x, |p x - q x| ∂mu := by
      rw [integral_const_mul]
    _ = 2 * M * ((2 : ℝ)⁻¹ * ∫ x, |p x - q x| ∂mu) := by
      ring

/-- Exact compact-Wilson one-link expectation comparison by the canonical
conditional total variation. -/
theorem continuous_compact_oriented_singleLinkConditionalGaugeExpectation_sub_abs_le_totalVariation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (phi : C.base.Gauge → ℝ)
    (hphi : Continuous phi)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hphi_bound : ∀ g, |phi g| ≤ M)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    |C.singleLinkConditionalGaugeExpectation phi A target -
        C.singleLinkConditionalGaugeExpectation phi B target| ≤
      2 * M * C.singleLinkConditionalTotalVariation A B target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalGaugeExpectation
  exact
    continuous_probabilityDensity_boundedTest_expectation_sub_abs_le_halfL1
      (normalizedCompactHaar C.base.Gauge)
      phi
      (C.singleLinkRealConditionalDensity A target)
      (C.singleLinkRealConditionalDensity B target)
      hphi
      (continuous_compact_oriented_singleLinkRealConditionalDensity C A target)
      (continuous_compact_oriented_singleLinkRealConditionalDensity C B target)
      M hM hphi_bound

/-- Periodic `SU(N)` specialization: the full sparse one-link TV certificate
controls every bounded continuous gauge-test expectation oscillation. -/
theorem periodicHypercubicSpecialUnitary_singleLinkConditionalGaugeExpectation_sub_abs_le_sparseInfluence
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : Continuous phi)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hphi_bound : ∀ g, |phi g| ≤ M)
    (A B : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.Configuration)
    (target source : PeriodicHypercubicEdge n)
    (hAgree : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.AgreeOffLink A B source) :
    |(periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).singleLinkConditionalGaugeExpectation phi A target -
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).singleLinkConditionalGaugeExpectation phi B target| ≤
      2 * M * periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        n beta target source := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta hBeta
  have hExpectation :=
    continuous_compact_oriented_singleLinkConditionalGaugeExpectation_sub_abs_le_totalVariation
      C phi hphi M hM hphi_bound A B target
  have hTV :=
    periodicHypercubicSpecialUnitary_singleLinkConditionalTotalVariation_le_sparseInfluence
      n N hn hN beta hBeta A B target source hAgree
  have hScale : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM
  exact le_trans hExpectation (mul_le_mul_of_nonneg_left hTV hScale)

end

end MathlibAnalytic
end MGAP4D
