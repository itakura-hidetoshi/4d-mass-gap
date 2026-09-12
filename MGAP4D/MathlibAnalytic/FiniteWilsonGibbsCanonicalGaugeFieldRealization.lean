import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsCanonicalEdgeObservation

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-!
Construct the single-source projective realization from one global observation
map, and specialize it to a gauge-valued field whose canonical edge coordinates
read the physical Wilson link variables exactly.
-/

/-- Data for one measurable global dependent observation map. -/
structure FiniteWilsonGibbsGlobalObservationData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  fieldValue : EuclideanFourSpace → Type
  [fieldValueMeasurableSpace : ∀ x, MeasurableSpace (fieldValue x)]
  sourceScale : W.index
  globalObserve :
    (W.system sourceScale).Configuration →
      (∀ x : EuclideanFourSpace, fieldValue x)
  globalObserve_measurable : Measurable globalObserve

attribute [instance]
  FiniteWilsonGibbsGlobalObservationData.fieldValueMeasurableSpace

/-- Restriction of a measurable global observation to a finite support is
measurable. -/
theorem FiniteWilsonGibbsGlobalObservationData.restrict_measurable
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonGibbsGlobalObservationData W)
    (J : Finset EuclideanFourSpace) :
    Measurable (fun A => J.restrict (D.globalObserve A)) := by
  rw [measurable_pi_iff]
  intro x
  change Measurable (fun A => D.globalObserve A x.1)
  exact (measurable_pi_apply x.1).comp D.globalObserve_measurable

/-- One global observation canonically generates all compatible finite
observation maps. -/
noncomputable def FiniteWilsonGibbsGlobalObservationData.toProjectiveRealization
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonGibbsGlobalObservationData W) :
    FiniteWilsonGibbsSingleSourceProjectiveRealization W where
  fieldValue := D.fieldValue
  fieldValueMeasurableSpace := D.fieldValueMeasurableSpace
  sourceScale := D.sourceScale
  observe := fun J A => J.restrict (D.globalObserve A)
  observe_measurable := D.restrict_measurable
  observe_restrict := by
    intro I J hJI A
    funext x
    rfl

/-- The generated realization recovers the original global observation. -/
theorem FiniteWilsonGibbsGlobalObservationData.toProjectiveRealization_globalObserve
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonGibbsGlobalObservationData W)
    (A : (W.system D.sourceScale).Configuration) :
    D.toProjectiveRealization.globalObserve A = D.globalObserve A := by
  funext x
  rfl

/-- Gauge-valued global field data with exact values at the canonical edge
coordinates. -/
structure FiniteWilsonGibbsCanonicalGaugeFieldData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  sourceScale : W.index
  globalObserve :
    (W.system sourceScale).Configuration →
      EuclideanFourSpace → (W.system sourceScale).Gauge
  globalObserve_measurable : Measurable globalObserve
  globalObserve_edge :
    ∀ (A : (W.system sourceScale).Configuration)
      (e : (W.system sourceScale).Edge),
      globalObserve A
        (fun i => if i = 0 then
          ((Fintype.equivFin (W.system sourceScale).Edge e).val : ℝ)
        else 0) = A e

/-- Gauge-valued field data as general global-observation data. -/
noncomputable def FiniteWilsonGibbsCanonicalGaugeFieldData.toGlobalObservationData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonGibbsCanonicalGaugeFieldData W) :
    FiniteWilsonGibbsGlobalObservationData W where
  fieldValue := fun _ => (W.system D.sourceScale).Gauge
  fieldValueMeasurableSpace := fun _ => (W.system D.sourceScale).gaugeMeasurableSpace
  sourceScale := D.sourceScale
  globalObserve := D.globalObserve
  globalObserve_measurable := D.globalObserve_measurable

/-- The concrete single-source projective realization generated from the one
gauge-valued global field. -/
noncomputable def FiniteWilsonGibbsCanonicalGaugeFieldData.realization
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonGibbsCanonicalGaugeFieldData W) :
    FiniteWilsonGibbsSingleSourceProjectiveRealization W :=
  D.toGlobalObservationData.toProjectiveRealization

/-- The generated realization has exact canonical edge observation. -/
noncomputable def
    FiniteWilsonGibbsCanonicalGaugeFieldData.toCanonicalEdgeObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonGibbsCanonicalGaugeFieldData W) :
    FiniteWilsonGibbsCanonicalEdgeObservation D.realization where
  fieldValue_eq_gauge := fun _ => rfl
  globalObserve_edge := by
    intro A e
    change D.globalObserve A
      (finiteWilsonCanonicalEdgePoint D.realization e) = A e
    exact D.globalObserve_edge A e

/-- The canonical gauge field generates faithful global observation. -/
def FiniteWilsonGibbsCanonicalGaugeFieldData.toFaithfulGlobalObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonGibbsCanonicalGaugeFieldData W) :
    FiniteWilsonGibbsFaithfulGlobalObservation D.realization :=
  D.toCanonicalEdgeObservation.toFaithfulGlobalObservation

/-- The canonical gauge field generates the finite interaction witness. -/
noncomputable def FiniteWilsonGibbsCanonicalGaugeFieldData.toInteractionWitness
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonGibbsCanonicalGaugeFieldData W)
    [Nontrivial (W.system D.realization.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (D.realization.fieldValue x)] :
    FiniteWilsonGibbsCylinderInteractionWitness D.realization :=
  D.toCanonicalEdgeObservation.toInteractionWitness

end

end MathlibAnalytic
end MGAP4D
