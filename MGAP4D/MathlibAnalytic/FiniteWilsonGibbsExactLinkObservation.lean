import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsLinkReadoutPointSeparation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Normalize finite Wilson link readout to an exact link-value observation.

Instead of carrying an arbitrary decoder at each Euclidean link point, identify
that observation fibre with the gauge carrier and require the transported global
observation to be exactly the corresponding physical link variable.  The
existing decoder-based readout and all of its interaction and spectral
consequences are then generated canonically.
-/

/-- A Euclidean observation point for every physical link whose observation
fibre is identified with the gauge carrier and whose observed value is exactly
the link variable. -/
structure FiniteWilsonGibbsExactLinkObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) where
  linkPoint : (W.system R.sourceScale).Edge → EuclideanFourSpace
  fieldValue_eq_gauge :
    ∀ e : (W.system R.sourceScale).Edge,
      R.fieldValue (linkPoint e) = (W.system R.sourceScale).Gauge
  globalObserve_link :
    ∀ (A : (W.system R.sourceScale).Configuration)
      (e : (W.system R.sourceScale).Edge),
      Eq.mp (fieldValue_eq_gauge e)
          (R.globalObserve A (linkPoint e)) =
        A e

/-- Exact link observation canonically supplies the decoder-based link readout. -/
def FiniteWilsonGibbsExactLinkObservation.toLinkReadout
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (E : FiniteWilsonGibbsExactLinkObservation R) :
    FiniteWilsonGibbsLinkReadout R where
  linkPoint := E.linkPoint
  decode := fun e v => Eq.mp (E.fieldValue_eq_gauge e) v
  decode_globalObserve := E.globalObserve_link

/-- Exact link observation proves pointwise separation of unequal source
configurations. -/
def FiniteWilsonGibbsExactLinkObservation.toGlobalPointSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (E : FiniteWilsonGibbsExactLinkObservation R) :
    FiniteWilsonGibbsGlobalPointSeparation R :=
  E.toLinkReadout.toGlobalPointSeparation

/-- Exact link observation generates a finite separating coordinate selector. -/
noncomputable def
    FiniteWilsonGibbsExactLinkObservation.toFiniteCoordinateSelector
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (E : FiniteWilsonGibbsExactLinkObservation R) :
    FiniteWilsonGibbsFiniteCoordinateSelector R :=
  E.toLinkReadout.toFiniteCoordinateSelector

/-- Exact link observation proves faithfulness of the global observation map. -/
def FiniteWilsonGibbsExactLinkObservation.toFaithfulGlobalObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (E : FiniteWilsonGibbsExactLinkObservation R) :
    FiniteWilsonGibbsFaithfulGlobalObservation R :=
  E.toLinkReadout.toFaithfulGlobalObservation

/-- Exact link observation generates the finite-cylinder interaction witness. -/
noncomputable def FiniteWilsonGibbsExactLinkObservation.toInteractionWitness
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (E : FiniteWilsonGibbsExactLinkObservation R) :
    FiniteWilsonGibbsCylinderInteractionWitness R :=
  E.toLinkReadout.toInteractionWitness

/-- The interaction obtained from exact link observation survives in the
continuum connected correlation. -/
theorem finite_wilson_exact_link_observation_interaction_passes_to_continuum
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (L : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R)
    (E : FiniteWilsonGibbsExactLinkObservation R) :
    finiteWilsonContinuumCylinderConnectedCorrelation R L
      E.toInteractionWitness.support
      E.toInteractionWitness.leftObservable
      E.toInteractionWitness.rightObservable ≠ 0 := by
  exact finite_wilson_link_readout_interaction_passes_to_continuum
    R L E.toLinkReadout

/-- Exact link observation reaches the exact-threshold spectral endpoint. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.exactLinkObservation_exactThresholdSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (E : FiniteWilsonGibbsExactLinkObservation R) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      (C.toExactGapConstructionSpineOfGlobalObservationSeparation
        E.toFiniteCoordinateSelector.toGlobalObservationSeparation).toConstructionSpine := by
  exact C.linkReadout_exactThresholdSeparation E.toLinkReadout

end

end MathlibAnalytic
end MGAP4D
