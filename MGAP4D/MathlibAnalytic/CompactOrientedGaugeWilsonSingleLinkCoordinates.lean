import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathDensityBalance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Physical links other than one selected target link. -/
abbrev CompactOrientedGaugeWilsonSystem.OffLinkEdge
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) : Type :=
  {e : L.geometry.Edge // e ≠ target}

/-- Configuration of all physical links except one selected target link. -/
abbrev CompactOrientedGaugeWilsonSystem.OffLinkConfiguration
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) : Type :=
  L.OffLinkEdge target → L.Gauge

/-- Split a physical-link configuration into the selected link value and all
off-link values. -/
noncomputable def CompactOrientedGaugeWilsonSystem.singleLinkCoordinatesEquiv
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) :
    L.Configuration ≃
      L.Gauge × L.OffLinkConfiguration target := by
  classical
  exact
    { toFun := fun A => (A target, fun e => A e.1)
      invFun := fun z e =>
        if h : e = target then z.1 else z.2 ⟨e, h⟩
      left_inv := by
        intro A
        funext e
        by_cases h : e = target
        · subst e
          simp
        · simp [h]
      right_inv := by
        rintro ⟨g, Aoff⟩
        apply Prod.ext
        · simp
        · funext e
          simp [e.2] }

/-- The single-link coordinate split is a measurable equivalence for the
finite product Borel structures. -/
noncomputable def
    CompactOrientedGaugeWilsonSystem.singleLinkCoordinatesMeasurableEquiv
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge) :
    L.Configuration ≃ᵐ
      L.Gauge × L.OffLinkConfiguration target where
  toEquiv := L.singleLinkCoordinatesEquiv target
  measurable_toFun := by
    apply Measurable.prodMk
    · exact measurable_pi_apply target
    · refine measurable_pi_lambda _ ?_
      intro e
      exact measurable_pi_apply e.1
  measurable_invFun := by
    refine measurable_pi_lambda _ ?_
    intro e
    by_cases h : e = target
    · subst e
      simpa [CompactOrientedGaugeWilsonSystem.singleLinkCoordinatesEquiv]
        using (measurable_fst : Measurable
          (fun z : L.Gauge × L.OffLinkConfiguration target => z.1))
    · simpa [CompactOrientedGaugeWilsonSystem.singleLinkCoordinatesEquiv, h]
        using
          ((measurable_pi_apply (⟨e, h⟩ : L.OffLinkEdge target)).comp
            (measurable_snd : Measurable
              (fun z : L.Gauge × L.OffLinkConfiguration target => z.2)))

@[simp] theorem compact_oriented_singleLinkCoordinatesMeasurableEquiv_apply_fst
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (A : L.Configuration) :
    (L.singleLinkCoordinatesMeasurableEquiv target A).1 = A target :=
  rfl

@[simp] theorem compact_oriented_singleLinkCoordinatesMeasurableEquiv_apply_snd
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (A : L.Configuration)
    (e : L.OffLinkEdge target) :
    (L.singleLinkCoordinatesMeasurableEquiv target A).2 e = A e.1 :=
  rfl

/-- In single-link coordinates, replacing the selected link changes only the
first coordinate. -/
theorem compact_oriented_singleLinkCoordinates_replaceLink
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (A : L.Configuration)
    (g : L.Gauge) :
    L.singleLinkCoordinatesMeasurableEquiv target
        (L.replaceLink A target g) =
      (g, (L.singleLinkCoordinatesMeasurableEquiv target A).2) := by
  apply Prod.ext
  · simp
  · funext e
    simp [CompactOrientedGaugeWilsonSystem.replaceLink, e.2]

end

end MathlibAnalytic
end MGAP4D
