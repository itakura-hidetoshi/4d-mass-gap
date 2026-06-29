import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathPairing

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Membership in an off-link measurable set is constant on every off-link
fiber. -/
theorem compact_oriented_mem_offLinkMeasurableSet_iff_of_agreeOffLink
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (s : Set L.Configuration)
    (hs : MeasurableSet[L.offLinkMeasurableSpace target] s)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B target) :
    A ∈ s ↔ B ∈ s := by
  rw [MeasurableSpace.measurableSet_comap] at hs
  rcases hs with ⟨t, ht, rfl⟩
  change L.offLinkRestriction target A ∈ t ↔
    L.offLinkRestriction target B ∈ t
  have hRestriction :
      L.offLinkRestriction target A =
        L.offLinkRestriction target B := by
    funext e
    exact hAgree e.1 e.2
  rw [hRestriction]

/-- The indicator of an off-link measurable set is constant on off-link
fibers. -/
theorem compact_oriented_indicator_offLinkFiberConstant
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (s : Set L.Configuration)
    (hs : MeasurableSet[L.offLinkMeasurableSpace target] s) :
    L.OffLinkFiberConstant target
      (s.indicator fun _ : L.Configuration => (1 : ℝ)) := by
  intro A B hAgree
  have hMem :=
    compact_oriented_mem_offLinkMeasurableSet_iff_of_agreeOffLink
      L target s hs A B hAgree
  by_cases hA : A ∈ s
  · have hB : B ∈ s := hMem.mp hA
    simp [Set.indicator_apply, hA, hB]
  · have hB : B ∉ s := by
      intro h
      exact hA (hMem.mpr h)
    simp [Set.indicator_apply, hA, hB]

/-- Exact Haar conditional expectation fixes indicators of off-link measurable
sets. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_indicator_offLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (s : Set C.base.Configuration)
    (hs : MeasurableSet[C.base.offLinkMeasurableSpace target] s) :
    C.singleLinkHeatBathProjection target
        (s.indicator fun _ : C.base.Configuration => (1 : ℝ)) =
      s.indicator fun _ : C.base.Configuration => (1 : ℝ) :=
  continuous_compact_oriented_singleLinkHeatBathProjection_fixes
    C target _
    (compact_oriented_indicator_offLinkFiberConstant
      C.base target s hs)

/-- The exact compact Haar heat-bath projection satisfies the defining
conditional-expectation integral identity on every off-link measurable set,
for strongly measurable uniformly bounded observables. -/
theorem continuous_compact_oriented_setIntegral_singleLinkHeatBathProjection_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ A, |f A| ≤ M)
    (s : Set C.base.Configuration)
    (hs : MeasurableSet[C.base.offLinkMeasurableSpace target] s) :
    ∫ A in s, C.singleLinkHeatBathProjection target f A
        ∂C.gibbsMeasure =
      ∫ A in s, f A ∂C.gibbsMeasure := by
  let g : C.base.Configuration → ℝ :=
    s.indicator fun _ => (1 : ℝ)
  have hsAmbient : MeasurableSet s :=
    (compact_oriented_offLinkMeasurableSpace_le C.base target) s hs
  have hg : StronglyMeasurable g :=
    stronglyMeasurable_const.indicator hsAmbient
  have hgBound : ∀ A, |g A| ≤ (1 : ℝ) := by
    intro A
    by_cases hA : A ∈ s
    · simp [g, Set.indicator_apply, hA]
    · simp [g, Set.indicator_apply, hA]
  have hPair :=
    continuous_compact_oriented_singleLinkHeatBathProjection_gibbsPairing_symm
      C target f g hf hg M 1 hM0 zero_le_one hM hgBound
  have hFix : C.singleLinkHeatBathProjection target g = g := by
    exact
      continuous_compact_oriented_singleLinkHeatBathProjection_indicator_offLink
        C target s hs
  rw [hFix] at hPair
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal at hPair
  have hLeft :
      (∫ A,
        C.singleLinkHeatBathProjection target f A * g A
        ∂C.gibbsMeasure) =
        ∫ A in s, C.singleLinkHeatBathProjection target f A
          ∂C.gibbsMeasure := by
    rw [← integral_indicator hsAmbient]
    apply integral_congr_ae
    filter_upwards [] with A
    by_cases hA : A ∈ s
    · simp [g, Set.indicator_apply, hA]
    · simp [g, Set.indicator_apply, hA]
  have hRight :
      (∫ A, f A * g A ∂C.gibbsMeasure) =
        ∫ A in s, f A ∂C.gibbsMeasure := by
    rw [← integral_indicator hsAmbient]
    apply integral_congr_ae
    filter_upwards [] with A
    by_cases hA : A ∈ s
    · simp [g, Set.indicator_apply, hA]
    · simp [g, Set.indicator_apply, hA]
  rw [hLeft, hRight] at hPair
  exact hPair

end

end MathlibAnalytic
end MGAP4D
