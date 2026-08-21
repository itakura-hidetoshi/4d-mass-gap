import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkOscillationTVComparison
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitarySparseConditionalTVCertificate
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Tactic

/-!
# Centered one-link variation propagation for compact Wilson conditionals

The current compact-Haar route now controls a common bounded one-link test by
conditional total variation, sharpened to its oscillation radius.  This file
lifts that estimate to genuine configuration observables.

For two backgrounds that differ at one physical source link, the difference of
one-link conditional expectations splits into two pieces:

* the observable itself changes while the conditional law is held fixed;
* the conditional law changes while the same target-fiber test is held fixed.

A proof-relevant centered variation profile controls the first term by the
source variation and the second by the target variation times the exact
conditional TV.  For the actual periodic compact `SU(N)` Wilson system, the
canonical sparse TV influence therefore gives

`variation source + influence target source * variation target`.

This is the local Dobrushin variation recursion needed before any finite matrix
iteration.  It remains a static finite-volume Gibbs statement.  No random-scan
or heat-bath update time is identified with physical OS Euclidean time, and no
factorial-continuum small-coupling hypothesis is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A proof-relevant physical-link oscillation bound for a compact Wilson
configuration observable. -/
structure ContinuousCompactOrientedGaugeWilsonLinkVariationBound
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.base.Configuration → ℝ) where
  variation : C.base.geometry.Edge → ℝ
  variation_nonneg : ∀ e : C.base.geometry.Edge, 0 ≤ variation e
  variation_bound :
    ∀ (e : C.base.geometry.Edge) (A B : C.base.Configuration),
      C.base.AgreeOffLink A B e → |f A - f B| ≤ variation e

/-- A centered one-link variation profile.  The target-fiber radius is half
of the full link variation, which is the normalization that pairs sharply with
total variation. -/
structure ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    extends ContinuousCompactOrientedGaugeWilsonLinkVariationBound C O where
  fiberCenter : C.base.Configuration → C.base.geometry.Edge → ℝ
  fiber_radius_bound :
    ∀ (A : C.base.Configuration) (e : C.base.geometry.Edge) (g : C.base.Gauge),
      |O (C.base.replaceLink A e g) - fiberCenter A e| ≤ variation e / 2

/-- Applying the same target replacement preserves agreement away from a
separately declared source link. -/
theorem compact_oriented_replaceLink_agreeOffLink_current
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.geometry.Edge)
    (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B source) :
    L.AgreeOffLink
      (L.replaceLink A target g)
      (L.replaceLink B target g)
      source := by
  intro e he
  by_cases ht : e = target
  · subst e
    simp
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, ht, hAgree e he]

/-- A bounded continuous configuration observable pulled back to one compact
link is integrable against the exact conditional law. -/
theorem continuous_compact_oriented_singleLinkObservable_integrable_current
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Integrable
      (fun g : C.base.Gauge => O (C.base.replaceLink A target g))
      (C.singleLinkConditionalMeasure A target) := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  exact
    (O.continuous.comp
      (continuous_compact_oriented_replaceLink C A target)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Holding one exact conditional law fixed, a uniform pointwise source
perturbation bounds the corresponding expectation change by the same amount. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_direct_difference_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (sourceBound : ℝ)
    (hSourceNonneg : 0 ≤ sourceBound)
    (hSourceBound : ∀ g : C.base.Gauge,
      |O (C.base.replaceLink A target g) -
        O (C.base.replaceLink B target g)| ≤ sourceBound) :
    |(∫ g : C.base.Gauge,
        O (C.base.replaceLink A target g)
        ∂C.singleLinkConditionalMeasure A target) -
      ∫ g : C.base.Gauge,
        O (C.base.replaceLink B target g)
        ∂C.singleLinkConditionalMeasure A target| ≤ sourceBound := by
  let mu := C.singleLinkConditionalMeasure A target
  letI : IsProbabilityMeasure mu :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  have hAInt : Integrable
      (fun g : C.base.Gauge => O (C.base.replaceLink A target g)) mu := by
    simpa [mu] using
      continuous_compact_oriented_singleLinkObservable_integrable_current
        C O A target
  have hBInt : Integrable
      (fun g : C.base.Gauge => O (C.base.replaceLink B target g)) mu := by
    have hCont : Continuous
        (fun g : C.base.Gauge => O (C.base.replaceLink B target g)) :=
      O.continuous.comp (continuous_compact_oriented_replaceLink C B target)
    exact hCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDiffInt : Integrable
      (fun g : C.base.Gauge =>
        O (C.base.replaceLink A target g) -
          O (C.base.replaceLink B target g)) mu :=
    hAInt.sub hBInt
  have hAbsInt : Integrable
      (fun g : C.base.Gauge =>
        |O (C.base.replaceLink A target g) -
          O (C.base.replaceLink B target g)|) mu := by
    simpa [Real.norm_eq_abs] using hDiffInt.norm
  have hConstInt : Integrable (fun _ : C.base.Gauge => sourceBound) mu :=
    integrable_const sourceBound
  change
    |(∫ g : C.base.Gauge,
        O (C.base.replaceLink A target g) ∂mu) -
      ∫ g : C.base.Gauge,
        O (C.base.replaceLink B target g) ∂mu| ≤ sourceBound
  rw [← integral_sub hAInt hBInt]
  calc
    |∫ g : C.base.Gauge,
        (O (C.base.replaceLink A target g) -
          O (C.base.replaceLink B target g)) ∂mu| ≤
      ∫ g : C.base.Gauge,
        |O (C.base.replaceLink A target g) -
          O (C.base.replaceLink B target g)| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _g : C.base.Gauge, sourceBound ∂mu := by
      apply integral_mono hAbsInt hConstInt
      intro g
      exact hSourceBound g
    _ = sourceBound := by simp

/-- Changing only the conditional law while keeping a common continuous
target-fiber test is controlled by its centered radius times exact TV. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_test_difference_abs_le_of_center
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (phi : C.base.Gauge → ℝ)
    (hphi : Continuous phi)
    (center radius : ℝ)
    (hRadiusNonneg : 0 ≤ radius)
    (hRadius : ∀ g : C.base.Gauge, |phi g - center| ≤ radius) :
    |(∫ g : C.base.Gauge, phi g
        ∂C.singleLinkConditionalMeasure A target) -
      ∫ g : C.base.Gauge, phi g
        ∂C.singleLinkConditionalMeasure B target| ≤
      2 * radius * C.singleLinkConditionalTotalVariation A B target := by
  have h :=
    continuous_compact_oriented_singleLinkConditionalGaugeExpectation_sub_abs_le_totalVariation_of_center
      C phi hphi center radius hRadiusNonneg hRadius A B target
  rw [continuous_compact_oriented_singleLinkConditionalGaugeExpectation_eq_integral
      C phi hphi A target,
    continuous_compact_oriented_singleLinkConditionalGaugeExpectation_eq_integral
      C phi hphi B target] at h
  exact h

/-- Local compact one-link propagation: source variation plus target-fiber
oscillation transported through conditional TV. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_difference_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target source : C.base.geometry.Edge)
    (A B : C.base.Configuration)
    (hAgree : C.base.AgreeOffLink A B source)
    (sourceBound targetRadius center : ℝ)
    (hSourceNonneg : 0 ≤ sourceBound)
    (hSourceBound : ∀ g : C.base.Gauge,
      |O (C.base.replaceLink A target g) -
        O (C.base.replaceLink B target g)| ≤ sourceBound)
    (hTargetRadiusNonneg : 0 ≤ targetRadius)
    (hTargetRadius : ∀ g : C.base.Gauge,
      |O (C.base.replaceLink B target g) - center| ≤ targetRadius) :
    |C.singleLinkConditionalExpectation O A target -
        C.singleLinkConditionalExpectation O B target| ≤
      sourceBound +
        2 * targetRadius * C.singleLinkConditionalTotalVariation A B target := by
  let hA : C.base.Gauge → ℝ :=
    fun g => O (C.base.replaceLink A target g)
  let hB : C.base.Gauge → ℝ :=
    fun g => O (C.base.replaceLink B target g)
  have hhB : Continuous hB :=
    O.continuous.comp (continuous_compact_oriented_replaceLink C B target)
  have hDirect :=
    continuous_compact_oriented_singleLinkConditionalExpectation_direct_difference_abs_le
      C O A B target sourceBound hSourceNonneg hSourceBound
  have hLaw :=
    continuous_compact_oriented_singleLinkConditionalMeasure_test_difference_abs_le_of_center
      C A B target hB hhB center targetRadius hTargetRadiusNonneg
      (by intro g; simpa [hB] using hTargetRadius g)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
  change
    |(∫ g : C.base.Gauge, hA g
        ∂C.singleLinkConditionalMeasure A target) -
      ∫ g : C.base.Gauge, hB g
        ∂C.singleLinkConditionalMeasure B target| ≤
      sourceBound +
        2 * targetRadius * C.singleLinkConditionalTotalVariation A B target
  have hSplit :
      (∫ g : C.base.Gauge, hA g
          ∂C.singleLinkConditionalMeasure A target) -
        ∫ g : C.base.Gauge, hB g
          ∂C.singleLinkConditionalMeasure B target =
      ((∫ g : C.base.Gauge, hA g
          ∂C.singleLinkConditionalMeasure A target) -
        ∫ g : C.base.Gauge, hB g
          ∂C.singleLinkConditionalMeasure A target) +
      ((∫ g : C.base.Gauge, hB g
          ∂C.singleLinkConditionalMeasure A target) -
        ∫ g : C.base.Gauge, hB g
          ∂C.singleLinkConditionalMeasure B target) := by
    ring
  rw [hSplit]
  exact le_trans (abs_add_le _ _) (add_le_add hDirect hLaw)

/-- A centered variation profile gives the sharp local update with the exact
conditional TV coefficient. -/
theorem continuous_compact_oriented_centeredVariation_conditionalExpectation_difference_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (target source : C.base.geometry.Edge)
    (A B : C.base.Configuration)
    (hAgree : C.base.AgreeOffLink A B source) :
    |C.singleLinkConditionalExpectation O A target -
        C.singleLinkConditionalExpectation O B target| ≤
      P.variation source +
        C.singleLinkConditionalTotalVariation A B target * P.variation target := by
  have hSourceBound : ∀ g : C.base.Gauge,
      |O (C.base.replaceLink A target g) -
        O (C.base.replaceLink B target g)| ≤ P.variation source := by
    intro g
    exact P.variation_bound source
      (C.base.replaceLink A target g)
      (C.base.replaceLink B target g)
      (compact_oriented_replaceLink_agreeOffLink_current
        C.base A B target source g hAgree)
  have hRadiusNonneg : 0 ≤ P.variation target / 2 :=
    div_nonneg (P.variation_nonneg target) (by norm_num)
  have h :=
    continuous_compact_oriented_singleLinkConditionalExpectation_difference_abs_le
      C O target source A B hAgree
      (P.variation source) (P.variation target / 2)
      (P.fiberCenter B target)
      (P.variation_nonneg source) hSourceBound hRadiusNonneg
      (P.fiber_radius_bound B target)
  calc
    |C.singleLinkConditionalExpectation O A target -
        C.singleLinkConditionalExpectation O B target| ≤
      P.variation source +
        2 * (P.variation target / 2) *
          C.singleLinkConditionalTotalVariation A B target := h
    _ = P.variation source +
        C.singleLinkConditionalTotalVariation A B target * P.variation target := by
      ring

/-- Actual periodic compact `SU(N)` specialization: the sparse one-link TV
influence transports target variation into source variation. -/
theorem periodicHypercubicSpecialUnitary_centeredVariation_conditionalExpectation_difference_abs_le_sparseInfluence
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta) O)
    (target source : PeriodicHypercubicEdge n)
    (A B : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.Configuration)
    (hAgree : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.AgreeOffLink A B source) :
    |(periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).singleLinkConditionalExpectation O A target -
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).singleLinkConditionalExpectation O B target| ≤
      P.variation source +
        periodicHypercubicSpecialUnitarySparseActiveTVInfluence
          n beta target source * P.variation target := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta hBeta
  have hBase :=
    continuous_compact_oriented_centeredVariation_conditionalExpectation_difference_abs_le
      C O P target source A B hAgree
  have hTV :=
    periodicHypercubicSpecialUnitary_singleLinkConditionalTotalVariation_le_sparseInfluence
      n N hn hN beta hBeta A B target source hAgree
  have hTransport :
      C.singleLinkConditionalTotalVariation A B target * P.variation target ≤
        periodicHypercubicSpecialUnitarySparseActiveTVInfluence
          n beta target source * P.variation target :=
    mul_le_mul_of_nonneg_right hTV (P.variation_nonneg target)
  exact le_trans hBase (add_le_add_left hTransport (P.variation source))

end

end MathlibAnalytic
end MGAP4D
