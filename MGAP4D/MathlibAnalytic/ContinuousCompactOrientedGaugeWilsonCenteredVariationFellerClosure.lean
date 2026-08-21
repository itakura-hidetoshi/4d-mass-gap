import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkFellerClosure
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Centered variation closure for current compact Wilson one-link updates

The current one-link conditional expectation is now a bounded continuous
observable.  To iterate the sharp Dobrushin variation theorem, the remaining
local issue is to recover a centered fiber profile after each update without
inflating the variation constants.

For a continuous real function on a compact nonempty space, a pairwise
oscillation bound `|f x - f y| ≤ r` admits the midpoint of its attained minimum
and maximum as a center with radius `r / 2`.  Applying this to every compact
one-link fiber upgrades any current `LinkVariationBound` on a bounded continuous
observable to a `CenteredVariationProfile` with exactly the same variation
function.

Combining this compact midpoint closure with the current Feller theorem and the
existing sharp one-step Dobrushin estimate gives a genuinely closed one-link
BCF-to-BCF centered variation update.

This remains finite-volume heat-bath/Dobrushin algebra.  Update count is not
Euclidean time, and no covariance decay, continuum clustering, physical mass
gap, or uniform continuum Dobrushin threshold is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Set

noncomputable section

/-- A continuous real function on a compact nonempty space whose pairwise
oscillation is at most `r` admits a midpoint center of radius `r / 2`. -/
theorem continuous_compact_exists_midpoint_center_of_pairwise_abs_sub_le
    {X : Type*}
    [TopologicalSpace X]
    [CompactSpace X]
    [Nonempty X]
    (f : X → ℝ)
    (hf : Continuous f)
    (r : ℝ)
    (hPair : ∀ x y : X, |f x - f y| ≤ r) :
    ∃ c : ℝ, ∀ x : X, |f x - c| ≤ r / 2 := by
  obtain ⟨xmin, _hxmin_mem, hxmin⟩ :=
    isCompact_univ.exists_isMinOn (Set.univ_nonempty : (Set.univ : Set X).Nonempty)
      hf.continuousOn
  obtain ⟨xmax, _hxmax_mem, hxmax⟩ :=
    isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set X).Nonempty)
      hf.continuousOn
  refine ⟨(f xmin + f xmax) / 2, ?_⟩
  intro x
  have hMin : f xmin ≤ f x := hxmin (Set.mem_univ x)
  have hMax : f x ≤ f xmax := hxmax (Set.mem_univ x)
  have hWidth : f xmax - f xmin ≤ r := by
    exact le_trans (le_abs_self (f xmax - f xmin)) (hPair xmax xmin)
  rw [abs_le]
  constructor <;> linarith

/-- A current physical one-link variation bound supplies a midpoint center on
every compact one-link fiber with exactly half the same variation radius. -/
theorem continuous_compact_oriented_linkVariationBound_exists_fiberCenter
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => O A))
    (A : C.base.Configuration)
    (e : C.base.geometry.Edge) :
    ∃ c : ℝ, ∀ g : C.base.Gauge,
      |O (C.base.replaceLink A e g) - c| ≤ P.variation e / 2 := by
  let f : C.base.Gauge → ℝ := fun g => O (C.base.replaceLink A e g)
  have hf : Continuous f :=
    O.continuous.comp (continuous_compact_oriented_replaceLink C A e)
  have hPair : ∀ g h : C.base.Gauge, |f g - f h| ≤ P.variation e := by
    intro g h
    apply P.variation_bound e
    intro source hsource
    simp [CompactOrientedGaugeWilsonSystem.replaceLink, hsource]
  simpa [f] using
    (continuous_compact_exists_midpoint_center_of_pairwise_abs_sub_le
      f hf (P.variation e) hPair)

/-- Compact midpoint recentering upgrades a variation bound on a bounded
continuous observable to a centered variation profile without changing any
linkwise variation constant. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonLinkVariationBound.toCenteredVariationProfile
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => O A)) :
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O := by
  classical
  have hCenter : ∀ (A : C.base.Configuration) (e : C.base.geometry.Edge),
      ∃ c : ℝ, ∀ g : C.base.Gauge,
        |O (C.base.replaceLink A e g) - c| ≤ P.variation e / 2 :=
    fun A e =>
      continuous_compact_oriented_linkVariationBound_exists_fiberCenter
        C O P A e
  refine
    { variation := P.variation
      variation_nonneg := P.variation_nonneg
      variation_bound := P.variation_bound
      fiberCenter := fun A e => Classical.choose (hCenter A e)
      fiber_radius_bound := ?_ }
  intro A e g
  exact (Classical.choose_spec (hCenter A e)) g

/-- The current sharp one-link Dobrushin update is closed on the bounded
continuous centered-variation carrier: Feller continuity supplies the new BCF,
and compact midpoint recentering restores the centered profile with no loss in
the already-proved updated variation constants. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.
      conditionalExpectationCenteredVariationProfile
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (target : C.base.geometry.Edge) :
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C
      (C.singleLinkConditionalExpectationContinuousBCF target O) := by
  let Q : ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => C.singleLinkConditionalExpectationContinuousBCF target O A) := by
    simpa only [continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_apply]
      using P.conditionalExpectationVariationBound D target
  exact Q.toCenteredVariationProfile

end

end MathlibAnalytic
end MGAP4D
