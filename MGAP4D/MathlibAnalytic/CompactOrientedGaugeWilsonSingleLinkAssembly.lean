import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonSingleLinkCanonicalCoordinates

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Assemble a physical-link configuration from one selected link value and an
off-link configuration. -/
def CompactOrientedGaugeWilsonSystem.singleLinkAssemble
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (g : L.Gauge)
    (Aoff : L.OffLinkConfiguration target) : L.Configuration :=
  (L.singleLinkCoordinatesMeasurableEquiv target).symm (g, Aoff)

@[simp] theorem compact_oriented_singleLinkAssemble_target
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (g : L.Gauge)
    (Aoff : L.OffLinkConfiguration target) :
    L.singleLinkAssemble target g Aoff target = g := by
  have h :=
    (L.singleLinkCoordinatesMeasurableEquiv target).apply_symm_apply
      (g, Aoff)
  exact congrArg Prod.fst h

@[simp] theorem compact_oriented_singleLinkAssemble_offLink
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (g : L.Gauge)
    (Aoff : L.OffLinkConfiguration target)
    (e : L.OffLinkEdge target) :
    L.singleLinkAssemble target g Aoff e.1 = Aoff e := by
  have h :=
    (L.singleLinkCoordinatesMeasurableEquiv target).apply_symm_apply
      (g, Aoff)
  exact congrFun (congrArg Prod.snd h) e

/-- Every physical-link configuration is assembled from its selected-link and
off-link coordinates. -/
theorem compact_oriented_singleLinkAssemble_coordinates
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (A : L.Configuration) :
    L.singleLinkAssemble target (A target)
        (L.singleLinkCoordinatesMeasurableEquiv target A).2 = A := by
  exact
    (L.singleLinkCoordinatesMeasurableEquiv target).symm_apply_apply A

/-- Replacing the selected link of an assembled configuration replaces only
the selected coordinate. -/
theorem compact_oriented_replaceLink_singleLinkAssemble
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (g h : L.Gauge)
    (Aoff : L.OffLinkConfiguration target) :
    L.replaceLink (L.singleLinkAssemble target g Aoff) target h =
      L.singleLinkAssemble target h Aoff := by
  apply (L.singleLinkCoordinatesMeasurableEquiv target).injective
  rw [compact_oriented_singleLinkCoordinates_replaceLink]
  exact
    (L.singleLinkCoordinatesMeasurableEquiv target).apply_symm_apply
      (h, Aoff)

end

end MathlibAnalytic
end MGAP4D
