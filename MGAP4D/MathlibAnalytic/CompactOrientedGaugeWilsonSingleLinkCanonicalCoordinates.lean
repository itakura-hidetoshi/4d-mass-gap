import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonSingleLinkHaarFactorization

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical measurable coordinate split records the selected link value
in its first component. -/
@[simp] theorem compact_oriented_canonicalSingleLinkCoordinates_apply_fst
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (A : L.Configuration) :
    (L.canonicalSingleLinkCoordinatesMeasurableEquiv target A).1 =
      A target := by
  change A ((default : L.SelectedLinkEdge target).1) = A target
  rw [(default : L.SelectedLinkEdge target).2]

/-- The second component of the canonical coordinate split is restriction to
all off-link variables. -/
@[simp] theorem compact_oriented_canonicalSingleLinkCoordinates_apply_snd
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (A : L.Configuration)
    (e : L.OffLinkEdge target) :
    (L.canonicalSingleLinkCoordinatesMeasurableEquiv target A).2 e =
      A e.1 := by
  rfl

/-- The canonical and direct one-link coordinate decompositions agree
pointwise. -/
theorem compact_oriented_canonicalSingleLinkCoordinates_eq_direct
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) :
    L.canonicalSingleLinkCoordinatesMeasurableEquiv target =
      L.singleLinkCoordinatesMeasurableEquiv target := by
  apply MeasurableEquiv.ext
  funext A
  apply Prod.ext
  · simp
  · funext e
    simp

/-- In canonical one-link coordinates, replacing the selected link changes
only the first component. -/
theorem compact_oriented_canonicalSingleLinkCoordinates_replaceLink
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (A : L.Configuration)
    (g : L.Gauge) :
    L.canonicalSingleLinkCoordinatesMeasurableEquiv target
        (L.replaceLink A target g) =
      (g, (L.canonicalSingleLinkCoordinatesMeasurableEquiv target A).2) := by
  rw [compact_oriented_canonicalSingleLinkCoordinates_eq_direct,
    compact_oriented_singleLinkCoordinates_replaceLink]

end

end MathlibAnalytic
end MGAP4D
