import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsExactLinkObservation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Place every physical link of a finite Wilson source at a canonical point of
four-dimensional Euclidean space.

The finite edge type is enumerated by `Fintype.equivFin`.  Its index is stored in
the first Euclidean coordinate and the remaining coordinates are zero.  Thus the
choice of `linkPoint` is no longer external realization data.  The remaining
model-specific statement is only the exact interpolation formula at these
canonical edge points.
-/

/-- Canonical Euclidean point assigned to a physical finite Wilson link. -/
noncomputable def finiteWilsonCanonicalEdgePoint
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (e : (W.system R.sourceScale).Edge) : EuclideanFourSpace :=
  fun i => if i = 0 then ((Fintype.equivFin _ e).val : ℝ) else 0

/-- The canonical Euclidean placement distinguishes physical links. -/
theorem finiteWilsonCanonicalEdgePoint_injective
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    Function.Injective (finiteWilsonCanonicalEdgePoint R) := by
  intro e f hef
  apply (Fintype.equivFin (W.system R.sourceScale).Edge).injective
  apply Fin.ext
  have h0 := congrFun hef (0 : Fin 4)
  simp [finiteWilsonCanonicalEdgePoint] at h0
  exact_mod_cast h0

/-- Exact observation of every physical link at its canonical Euclidean point.

Only the fibre identification and the exact value formula remain as
model-specific interpolation statements. -/
structure FiniteWilsonGibbsCanonicalEdgeObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) where
  fieldValue_eq_gauge :
    ∀ e : (W.system R.sourceScale).Edge,
      R.fieldValue (finiteWilsonCanonicalEdgePoint R e) =
        (W.system R.sourceScale).Gauge
  globalObserve_edge :
    ∀ (A : (W.system R.sourceScale).Configuration)
      (e : (W.system R.sourceScale).Edge),
      Eq.mp (fieldValue_eq_gauge e)
          (R.globalObserve A (finiteWilsonCanonicalEdgePoint R e)) =
        A e

/-- Canonical edge observation generates the normalized exact-link observation
package. -/
def FiniteWilsonGibbsCanonicalEdgeObservation.toExactLinkObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (E : FiniteWilsonGibbsCanonicalEdgeObservation R) :
    FiniteWilsonGibbsExactLinkObservation R where
  linkPoint := finiteWilsonCanonicalEdgePoint R
  fieldValue_eq_gauge := E.fieldValue_eq_gauge
  globalObserve_link := E.globalObserve_edge

/-- Canonical edge observation proves faithfulness of the complete global
observation map. -/
def FiniteWilsonGibbsCanonicalEdgeObservation.toFaithfulGlobalObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (E : FiniteWilsonGibbsCanonicalEdgeObservation R) :
    FiniteWilsonGibbsFaithfulGlobalObservation R :=
  E.toExactLinkObservation.toFaithfulGlobalObservation

/-- Canonical edge observation generates the finite cylinder interaction
witness. -/
noncomputable def FiniteWilsonGibbsCanonicalEdgeObservation.toInteractionWitness
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (E : FiniteWilsonGibbsCanonicalEdgeObservation R) :
    FiniteWilsonGibbsCylinderInteractionWitness R :=
  E.toExactLinkObservation.toInteractionWitness

/-- The interaction witness generated from canonical edge points survives as a
nonzero continuum connected correlation. -/
theorem finite_wilson_canonical_edge_observation_interaction_passes_to_continuum
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (L : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R)
    (E : FiniteWilsonGibbsCanonicalEdgeObservation R) :
    finiteWilsonContinuumCylinderConnectedCorrelation R L
      E.toInteractionWitness.support
      E.toInteractionWitness.leftObservable
      E.toInteractionWitness.rightObservable ≠ 0 := by
  exact finite_wilson_exact_link_observation_interaction_passes_to_continuum
    R L E.toExactLinkObservation

/-- Canonical edge observation reaches the exact-threshold spectral endpoint. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.canonicalEdgeObservation_exactThresholdSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (E : FiniteWilsonGibbsCanonicalEdgeObservation R) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      (C.toExactGapConstructionSpineOfGlobalObservationSeparation
        E.toExactLinkObservation.toFiniteCoordinateSelector
          .toGlobalObservationSeparation).toConstructionSpine := by
  exact C.exactLinkObservation_exactThresholdSeparation
    E.toExactLinkObservation

end

end MathlibAnalytic
end MGAP4D
