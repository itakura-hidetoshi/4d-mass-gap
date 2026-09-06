import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorConditionalLocality
import Mathlib.MeasureTheory.Integral.Prod

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Exact one-link heat-bath transform on real observables. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathTransform
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : C.base.Configuration → ℝ) :
    C.base.Configuration → ℝ :=
  fun A =>
    ∫ g : C.base.Gauge,
      O (C.base.replaceLink A target g)
      ∂C.singleLinkConditionalMeasure A target

@[simp] theorem continuous_compact_oriented_singleLinkHeatBathTransform_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : C.base.Configuration → ℝ)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathTransform target O A =
      ∫ g : C.base.Gauge,
        O (C.base.replaceLink A target g)
        ∂C.singleLinkConditionalMeasure A target := by
  rfl

/-- Replacements of two distinct physical links commute. -/
theorem compact_oriented_replaceLink_commute_of_ne
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    {target source : L.geometry.Edge}
    (hNe : source ≠ target)
    (g h : L.Gauge) :
    L.replaceLink (L.replaceLink A source h) target g =
      L.replaceLink (L.replaceLink A target g) source h := by
  funext e
  by_cases ht : e = target
  · subst e
    simp [CompactOrientedGaugeWilsonSystem.replaceLink, hNe]
  · by_cases hs : e = source
    · subst e
      simp [CompactOrientedGaugeWilsonSystem.replaceLink, ht]
    · simp [CompactOrientedGaugeWilsonSystem.replaceLink, ht, hs]

/-- Simultaneously varying two distinct compact links is continuous. -/
theorem continuous_compact_oriented_replaceTwoLinks
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    {target source : C.base.geometry.Edge}
    (hNe : source ≠ target) :
    Continuous
      (fun z : C.base.Gauge × C.base.Gauge =>
        C.base.replaceLink
          (C.base.replaceLink A source z.1) target z.2) := by
  apply continuous_pi
  intro e
  by_cases ht : e = target
  · subst e
    simpa [CompactOrientedGaugeWilsonSystem.replaceLink] using
      (continuous_snd : Continuous
        (fun z : C.base.Gauge × C.base.Gauge => z.2))
  · by_cases hs : e = source
    · subst e
      simpa [CompactOrientedGaugeWilsonSystem.replaceLink, ht] using
        (continuous_fst : Continuous
          (fun z : C.base.Gauge × C.base.Gauge => z.1))
    · simpa [CompactOrientedGaugeWilsonSystem.replaceLink, ht, hs] using
        (continuous_const : Continuous
          (fun _z : C.base.Gauge × C.base.Gauge => A e))

/-- Fubini swap for a continuous observable after two distinct compact-link
replacements. -/
theorem continuous_compact_oriented_twoLinkObservable_integral_swap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : C.base.Configuration → ℝ)
    (hO : Continuous O)
    (A : C.base.Configuration)
    {target source : C.base.geometry.Edge}
    (hNe : source ≠ target) :
    (∫ h : C.base.Gauge,
      ∫ g : C.base.Gauge,
        O (C.base.replaceLink
          (C.base.replaceLink A source h) target g)
        ∂C.singleLinkConditionalMeasure A target
      ∂C.singleLinkConditionalMeasure A source) =
    ∫ g : C.base.Gauge,
      ∫ h : C.base.Gauge,
        O (C.base.replaceLink
          (C.base.replaceLink A target g) source h)
        ∂C.singleLinkConditionalMeasure A source
      ∂C.singleLinkConditionalMeasure A target := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A source) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A source
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  have hCont :
      Continuous
        (Function.uncurry
          (fun h : C.base.Gauge =>
            fun g : C.base.Gauge =>
              O (C.base.replaceLink
                (C.base.replaceLink A source h) target g))) := by
    exact hO.comp
      (continuous_compact_oriented_replaceTwoLinks C A hNe)
  have hSwap :=
    integral_integral_swap_of_hasCompactSupport
      (μ := C.singleLinkConditionalMeasure A source)
      (ν := C.singleLinkConditionalMeasure A target)
      hCont (HasCompactSupport.of_compactSpace _)
  calc
    (∫ h : C.base.Gauge,
      ∫ g : C.base.Gauge,
        O (C.base.replaceLink
          (C.base.replaceLink A source h) target g)
        ∂C.singleLinkConditionalMeasure A target
      ∂C.singleLinkConditionalMeasure A source) =
      ∫ g : C.base.Gauge,
        ∫ h : C.base.Gauge,
          O (C.base.replaceLink
            (C.base.replaceLink A source h) target g)
          ∂C.singleLinkConditionalMeasure A source
        ∂C.singleLinkConditionalMeasure A target := hSwap
    _ =
      ∫ g : C.base.Gauge,
        ∫ h : C.base.Gauge,
          O (C.base.replaceLink
            (C.base.replaceLink A target g) source h)
          ∂C.singleLinkConditionalMeasure A source
        ∂C.singleLinkConditionalMeasure A target := by
      simp_rw [compact_oriented_replaceLink_commute_of_ne C.base A hNe]

/-- If each one-link conditional law is invariant under resampling the other
link, then the two exact heat-bath transforms commute at the given
configuration. -/
theorem continuous_compact_oriented_singleLinkHeatBathTransform_commute_at_of_measure_invariant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : C.base.Configuration → ℝ)
    (hO : Continuous O)
    (A : C.base.Configuration)
    {target source : C.base.geometry.Edge}
    (hNe : source ≠ target)
    (hTarget : ∀ h : C.base.Gauge,
      C.singleLinkConditionalMeasure
          (C.base.replaceLink A source h) target =
        C.singleLinkConditionalMeasure A target)
    (hSource : ∀ g : C.base.Gauge,
      C.singleLinkConditionalMeasure
          (C.base.replaceLink A target g) source =
        C.singleLinkConditionalMeasure A source) :
    C.singleLinkHeatBathTransform source
        (C.singleLinkHeatBathTransform target O) A =
      C.singleLinkHeatBathTransform target
        (C.singleLinkHeatBathTransform source O) A := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathTransform
  simp_rw [hTarget, hSource]
  exact continuous_compact_oriented_twoLinkObservable_integral_swap
    C O hO A hNe

/-- Distinct links in one canonical eight-color class have commuting exact
compact `SU(N)` Wilson heat-bath transforms. -/
theorem periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathTransform_commute_of_sameColor
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (O : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hO : Continuous O)
    {target source : PeriodicHypercubicEvenEdge H}
    (hNe : source ≠ target)
    (hColor :
      periodicHypercubicEvenEdgeColor H target =
        periodicHypercubicEvenEdgeColor H source) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
    C.singleLinkHeatBathTransform source
        (C.singleLinkHeatBathTransform target O) =
      C.singleLinkHeatBathTransform target
        (C.singleLinkHeatBathTransform source O) := by
  dsimp only
  funext A
  apply
    continuous_compact_oriented_singleLinkHeatBathTransform_commute_at_of_measure_invariant
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta)
      O hO A hNe
  · intro h
    exact
      periodicHypercubicEvenSpecialUnitary_singleLinkConditionalMeasure_replaceLink_eq_of_sameColor
        H N hN beta hBeta A h hNe hColor
  · intro g
    exact
      periodicHypercubicEvenSpecialUnitary_singleLinkConditionalMeasure_replaceLink_eq_of_sameColor
        H N hN beta hBeta A g hNe.symm hColor.symm

end
end MathlibAnalytic
end MGAP4D
