import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonSingleLinkCoordinates
import Mathlib.MeasureTheory.Constructions.Pi

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The singleton subtype containing the selected physical link. -/
abbrev CompactOrientedGaugeWilsonSystem.SelectedLinkEdge
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) : Type :=
  {e : L.geometry.Edge // e = target}

instance compactOriented_selectedLinkEdge_unique
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) :
    Unique (L.SelectedLinkEdge target) where
  default := ⟨target, rfl⟩
  uniq e := by
    apply Subtype.ext
    exact e.2

/-- Product normalized Haar measure on all links except the selected one. -/
noncomputable def CompactOrientedGaugeWilsonSystem.offLinkHaarMeasure
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) :
    Measure (L.OffLinkConfiguration target) := by
  classical
  exact Measure.pi (fun _ : L.OffLinkEdge target =>
    normalizedCompactHaar L.Gauge)

/-- Canonical measurable one-link coordinate decomposition obtained by first
splitting the finite product into the selected-link subtype and its complement,
then identifying the singleton product with the gauge group itself. -/
noncomputable def
    CompactOrientedGaugeWilsonSystem.canonicalSingleLinkCoordinatesMeasurableEquiv
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) :
    L.Configuration ≃ᵐ
      L.Gauge × L.OffLinkConfiguration target := by
  classical
  exact
    (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : L.geometry.Edge => L.Gauge)
        (fun e => e = target)).trans
      ((MeasurableEquiv.piUnique
          (fun _ : L.SelectedLinkEdge target => L.Gauge)).prodCongr
        (MeasurableEquiv.refl (L.OffLinkConfiguration target)))

/-- The canonical one-link coordinate decomposition preserves product
normalized Haar measure. -/
theorem compact_oriented_canonicalSingleLinkCoordinates_measurePreserving
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) :
    MeasurePreserving
      (L.canonicalSingleLinkCoordinatesMeasurableEquiv target)
      L.configurationHaarMeasure
      ((normalizedCompactHaar L.Gauge).prod
        (L.offLinkHaarMeasure target)) := by
  classical
  letI : Fintype (L.SelectedLinkEdge target) := Fintype.ofFinite _
  letI : Fintype (L.OffLinkEdge target) := Fintype.ofFinite _
  let μ : Measure L.Gauge := normalizedCompactHaar L.Gauge
  let selectedMeasure : Measure
      (L.SelectedLinkEdge target → L.Gauge) :=
    Measure.pi (fun _ : L.SelectedLinkEdge target => μ)
  let offMeasure : Measure (L.OffLinkConfiguration target) :=
    L.offLinkHaarMeasure target
  letI : IsProbabilityMeasure selectedMeasure := by
    dsimp [selectedMeasure, μ]
    infer_instance
  letI : IsProbabilityMeasure offMeasure := by
    dsimp [offMeasure, CompactOrientedGaugeWilsonSystem.offLinkHaarMeasure, μ]
    infer_instance
  have hSplit : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : L.geometry.Edge => L.Gauge)
        (fun e => e = target))
      (Measure.pi (fun _ : L.geometry.Edge => μ))
      (selectedMeasure.prod offMeasure) := by
    simpa [selectedMeasure, offMeasure,
      CompactOrientedGaugeWilsonSystem.offLinkHaarMeasure] using
      (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
        (fun _ : L.geometry.Edge => μ)
        (fun e => e = target))
  have hSelected : MeasurePreserving
      (MeasurableEquiv.piUnique
        (fun _ : L.SelectedLinkEdge target => L.Gauge))
      selectedMeasure μ := by
    simpa [selectedMeasure] using
      (MeasureTheory.measurePreserving_piUnique
        (fun _ : L.SelectedLinkEdge target => μ))
  have hProduct : MeasurePreserving
      ((MeasurableEquiv.piUnique
        (fun _ : L.SelectedLinkEdge target => L.Gauge)).prodCongr
          (MeasurableEquiv.refl (L.OffLinkConfiguration target)))
      (selectedMeasure.prod offMeasure)
      (μ.prod offMeasure) := by
    exact hSelected.prod (MeasurePreserving.id offMeasure)
  simpa [CompactOrientedGaugeWilsonSystem.canonicalSingleLinkCoordinatesMeasurableEquiv,
    CompactOrientedGaugeWilsonSystem.configurationHaarMeasure,
    μ, offMeasure] using hSplit.trans hProduct

/-- Exact pushforward factorization of physical-link product Haar measure into
the selected link and all off-link variables. -/
theorem compact_oriented_map_canonicalSingleLinkCoordinates_configurationHaarMeasure
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) :
    Measure.map (L.canonicalSingleLinkCoordinatesMeasurableEquiv target)
        L.configurationHaarMeasure =
      (normalizedCompactHaar L.Gauge).prod
        (L.offLinkHaarMeasure target) :=
  (compact_oriented_canonicalSingleLinkCoordinates_measurePreserving
    L target).map_eq

end

end MathlibAnalytic
end MGAP4D
