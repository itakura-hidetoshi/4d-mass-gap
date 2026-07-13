import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedGaugeWilsonSystem
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonSingleLink
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A signed oriented plaquette touches a physical positive link when one of
its four boundary incidences uses that link, independently of traversal
orientation. -/
def CompactOrientedGaugeWilsonSystem.PlaquetteTouchesEdge
    (L : CompactOrientedGaugeWilsonSystem)
    (p : L.geometry.Plaquette)
    (e : L.geometry.Edge) : Prop :=
  ∃ k : Fin 4, (L.geometry.boundary p k).edge = e

/-- Plaquettes simultaneously incident to a target link and a source link. -/
noncomputable def CompactOrientedGaugeWilsonSystem.sharedPlaquettes
    (L : CompactOrientedGaugeWilsonSystem)
    (target source : L.geometry.Edge) :
    Finset L.geometry.Plaquette := by
  classical
  exact Finset.univ.filter fun p =>
    L.PlaquetteTouchesEdge p target ∧
      L.PlaquetteTouchesEdge p source

@[simp] theorem compact_oriented_mem_sharedPlaquettes_iff
    (L : CompactOrientedGaugeWilsonSystem)
    (target source : L.geometry.Edge)
    (p : L.geometry.Plaquette) :
    p ∈ L.sharedPlaquettes target source ↔
      L.PlaquetteTouchesEdge p target ∧
        L.PlaquetteTouchesEdge p source := by
  classical
  simp [CompactOrientedGaugeWilsonSystem.sharedPlaquettes]

/-- One signed boundary factor depends only on the value of its underlying
physical link. -/
theorem compact_oriented_stepValue_congr
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (step : FiniteOrientedBoundaryStep L.geometry.Edge)
    (h : A step.edge = B step.edge) :
    L.stepValue A step = L.stepValue B step := by
  cases step with
  | mk edge orientation =>
      cases orientation <;>
        simp [CompactOrientedGaugeWilsonSystem.stepValue,
          FiniteOrientedFourDimensionalPlaquetteGeometry.stepValue, h]

/-- Oriented plaquette holonomy is determined by the four physical boundary
link values. -/
theorem compact_oriented_plaquetteHolonomy_congr
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (p : L.geometry.Plaquette)
    (h : ∀ k : Fin 4,
      A (L.geometry.boundary p k).edge =
        B (L.geometry.boundary p k).edge) :
    L.plaquetteHolonomy A p = L.plaquetteHolonomy B p := by
  change
    L.stepValue A (L.geometry.boundary p 0) *
          L.stepValue A (L.geometry.boundary p 1) *
        L.stepValue A (L.geometry.boundary p 2) *
      L.stepValue A (L.geometry.boundary p 3) =
    L.stepValue B (L.geometry.boundary p 0) *
          L.stepValue B (L.geometry.boundary p 1) *
        L.stepValue B (L.geometry.boundary p 2) *
      L.stepValue B (L.geometry.boundary p 3)
  rw [compact_oriented_stepValue_congr L A B
      (L.geometry.boundary p 0) (h 0),
    compact_oriented_stepValue_congr L A B
      (L.geometry.boundary p 1) (h 1),
    compact_oriented_stepValue_congr L A B
      (L.geometry.boundary p 2) (h 2),
    compact_oriented_stepValue_congr L A B
      (L.geometry.boundary p 3) (h 3)]

/-- Changing a link not used by a plaquette leaves that plaquette holonomy
unchanged. -/
theorem compact_oriented_replaceLink_plaquetteHolonomy_eq_of_not_touches
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge)
    (u v : L.Gauge)
    (p : L.geometry.Plaquette)
    (hNot : ¬ L.PlaquetteTouchesEdge p target) :
    L.plaquetteHolonomy (L.replaceLink A target u) p =
      L.plaquetteHolonomy (L.replaceLink A target v) p := by
  apply compact_oriented_plaquetteHolonomy_congr
  intro k
  have hEdge : (L.geometry.boundary p k).edge ≠ target := by
    intro hk
    exact hNot ⟨k, hk⟩
  simp [CompactOrientedGaugeWilsonSystem.replaceLink, hEdge]

/-- The corresponding plaquette energy is unchanged as well. -/
theorem compact_oriented_replaceLink_plaquetteEnergy_eq_of_not_touches
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge)
    (u v : L.Gauge)
    (p : L.geometry.Plaquette)
    (hNot : ¬ L.PlaquetteTouchesEdge p target) :
    L.plaquetteEnergy
        (L.plaquetteHolonomy (L.replaceLink A target u) p) =
      L.plaquetteEnergy
        (L.plaquetteHolonomy (L.replaceLink A target v) p) := by
  rw [compact_oriented_replaceLink_plaquetteHolonomy_eq_of_not_touches
    L A target u v p hNot]

/-- If two backgrounds agree away from `source`, then after inserting the same
target value every plaquette not touching `source` has the same energy. -/
theorem compact_oriented_replaceLink_plaquetteEnergy_eq_of_agreeOffLink_not_touches
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.geometry.Edge)
    (u : L.Gauge)
    (p : L.geometry.Plaquette)
    (hAgree : L.AgreeOffLink A B source)
    (hNotSource : ¬ L.PlaquetteTouchesEdge p source) :
    L.plaquetteEnergy
        (L.plaquetteHolonomy (L.replaceLink A target u) p) =
      L.plaquetteEnergy
        (L.plaquetteHolonomy (L.replaceLink B target u) p) := by
  apply congrArg L.plaquetteEnergy
  apply compact_oriented_plaquetteHolonomy_congr
  intro k
  by_cases hTarget : (L.geometry.boundary p k).edge = target
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, hTarget]
  · have hSource : (L.geometry.boundary p k).edge ≠ source := by
      intro hk
      exact hNotSource ⟨k, hk⟩
    simp [CompactOrientedGaugeWilsonSystem.replaceLink, hTarget,
      hAgree _ hSource]

/-- The four-term response of one plaquette when the background is changed at
`source` and the resampled target value is changed from `u` to `v`. -/
def CompactOrientedGaugeWilsonSystem.sourceResponseOscillationTerm
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target : L.geometry.Edge)
    (u v : L.Gauge)
    (p : L.geometry.Plaquette) : ℝ :=
  (L.plaquetteEnergy
      (L.plaquetteHolonomy (L.replaceLink A target u) p) -
    L.plaquetteEnergy
      (L.plaquetteHolonomy (L.replaceLink B target u) p)) -
  (L.plaquetteEnergy
      (L.plaquetteHolonomy (L.replaceLink A target v) p) -
    L.plaquetteEnergy
      (L.plaquetteHolonomy (L.replaceLink B target v) p))

/-- Every non-shared plaquette contributes exactly zero to the conditional
background-response oscillation. -/
theorem compact_oriented_sourceResponseOscillationTerm_eq_zero_of_not_shared
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.geometry.Edge)
    (u v : L.Gauge)
    (p : L.geometry.Plaquette)
    (hAgree : L.AgreeOffLink A B source)
    (hNotShared : p ∉ L.sharedPlaquettes target source) :
    L.sourceResponseOscillationTerm A B target u v p = 0 := by
  have hNotBoth :
      ¬ (L.PlaquetteTouchesEdge p target ∧
        L.PlaquetteTouchesEdge p source) := by
    intro hBoth
    exact hNotShared
      ((compact_oriented_mem_sharedPlaquettes_iff
        L target source p).2 hBoth)
  by_cases hTarget : L.PlaquetteTouchesEdge p target
  · have hSource : ¬ L.PlaquetteTouchesEdge p source := by
      intro hs
      exact hNotBoth ⟨hTarget, hs⟩
    have hu :=
      compact_oriented_replaceLink_plaquetteEnergy_eq_of_agreeOffLink_not_touches
        L A B target source u p hAgree hSource
    have hv :=
      compact_oriented_replaceLink_plaquetteEnergy_eq_of_agreeOffLink_not_touches
        L A B target source v p hAgree hSource
    simp [CompactOrientedGaugeWilsonSystem.sourceResponseOscillationTerm,
      hu, hv]
  · have hAuAv :=
      compact_oriented_replaceLink_plaquetteEnergy_eq_of_not_touches
        L A target u v p hTarget
    have hBuBv :=
      compact_oriented_replaceLink_plaquetteEnergy_eq_of_not_touches
        L B target u v p hTarget
    simp [CompactOrientedGaugeWilsonSystem.sourceResponseOscillationTerm,
      hAuAv, hBuBv]

/-- The oscillation of the Wilson-action response to a one-source background
change is supported exactly on plaquettes shared by target and source. -/
theorem compact_oriented_wilsonAction_sourceResponse_oscillation_eq_sum_shared
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.geometry.Edge)
    (u v : L.Gauge)
    (hAgree : L.AgreeOffLink A B source) :
    (L.wilsonAction (L.replaceLink A target u) -
        L.wilsonAction (L.replaceLink B target u)) -
      (L.wilsonAction (L.replaceLink A target v) -
        L.wilsonAction (L.replaceLink B target v)) =
      ∑ p ∈ L.sharedPlaquettes target source,
        L.sourceResponseOscillationTerm A B target u v p := by
  classical
  unfold CompactOrientedGaugeWilsonSystem.wilsonAction
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _hp hNotShared
  exact compact_oriented_sourceResponseOscillationTerm_eq_zero_of_not_shared
    L A B target source u v p hAgree hNotShared

private theorem compact_oriented_abs_sum_le_sum_abs
    {ι : Type*}
    (s : Finset ι)
    (f : ι → ℝ) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have haBounds := abs_le.mp (le_rfl : |f a| ≤ |f a|)
      have hsBounds := abs_le.mp ih
      apply abs_le.mpr
      constructor <;> linarith

/-- If every plaquette energy lies in `[0, energyBound]`, then one shared
plaquette contributes at most `2 * energyBound` to the four-term oscillation. -/
theorem compact_oriented_sourceResponseOscillationTerm_abs_le
    (L : CompactOrientedGaugeWilsonSystem)
    (energyBound : ℝ)
    (hEnergyBound_nonneg : 0 ≤ energyBound)
    (hEnergy_le : ∀ g : L.Gauge, L.plaquetteEnergy g ≤ energyBound)
    (A B : L.Configuration)
    (target : L.geometry.Edge)
    (u v : L.Gauge)
    (p : L.geometry.Plaquette) :
    |L.sourceResponseOscillationTerm A B target u v p| ≤
      2 * energyBound := by
  unfold CompactOrientedGaugeWilsonSystem.sourceResponseOscillationTerm
  have ha0 := L.plaquetteEnergy_nonneg
    (L.plaquetteHolonomy (L.replaceLink A target u) p)
  have hb0 := L.plaquetteEnergy_nonneg
    (L.plaquetteHolonomy (L.replaceLink B target u) p)
  have hc0 := L.plaquetteEnergy_nonneg
    (L.plaquetteHolonomy (L.replaceLink A target v) p)
  have hd0 := L.plaquetteEnergy_nonneg
    (L.plaquetteHolonomy (L.replaceLink B target v) p)
  have ha := hEnergy_le
    (L.plaquetteHolonomy (L.replaceLink A target u) p)
  have hb := hEnergy_le
    (L.plaquetteHolonomy (L.replaceLink B target u) p)
  have hc := hEnergy_le
    (L.plaquetteHolonomy (L.replaceLink A target v) p)
  have hd := hEnergy_le
    (L.plaquetteHolonomy (L.replaceLink B target v) p)
  apply abs_le.mpr
  constructor <;> linarith [hEnergyBound_nonneg]

/-- Shared-plaquette cardinality controls the complete Wilson-action response
oscillation. -/
theorem compact_oriented_wilsonAction_sourceResponse_oscillation_abs_le_shared
    (L : CompactOrientedGaugeWilsonSystem)
    (energyBound : ℝ)
    (hEnergyBound_nonneg : 0 ≤ energyBound)
    (hEnergy_le : ∀ g : L.Gauge, L.plaquetteEnergy g ≤ energyBound)
    (A B : L.Configuration)
    (target source : L.geometry.Edge)
    (u v : L.Gauge)
    (hAgree : L.AgreeOffLink A B source) :
    |(L.wilsonAction (L.replaceLink A target u) -
        L.wilsonAction (L.replaceLink B target u)) -
      (L.wilsonAction (L.replaceLink A target v) -
        L.wilsonAction (L.replaceLink B target v))| ≤
      2 * ((L.sharedPlaquettes target source).card : ℝ) * energyBound := by
  rw [compact_oriented_wilsonAction_sourceResponse_oscillation_eq_sum_shared
    L A B target source u v hAgree]
  calc
    |∑ p ∈ L.sharedPlaquettes target source,
        L.sourceResponseOscillationTerm A B target u v p| ≤
      ∑ p ∈ L.sharedPlaquettes target source,
        |L.sourceResponseOscillationTerm A B target u v p| :=
      compact_oriented_abs_sum_le_sum_abs
        (L.sharedPlaquettes target source)
        (L.sourceResponseOscillationTerm A B target u v)
    _ ≤ ∑ _p ∈ L.sharedPlaquettes target source,
        2 * energyBound := by
      apply Finset.sum_le_sum
      intro p _hp
      exact compact_oriented_sourceResponseOscillationTerm_abs_le
        L energyBound hEnergyBound_nonneg hEnergy_le A B target u v p
    _ = 2 * ((L.sharedPlaquettes target source).card : ℝ) *
        energyBound := by
      simp [nsmul_eq_mul]
      ring

/-- The same shared-plaquette estimate for the logarithmic Gibbs weights. -/
theorem compact_oriented_gibbsExponent_sourceResponse_oscillation_abs_le_shared
    (L : CompactOrientedGaugeWilsonSystem)
    (energyBound : ℝ)
    (hEnergyBound_nonneg : 0 ≤ energyBound)
    (hEnergy_le : ∀ g : L.Gauge, L.plaquetteEnergy g ≤ energyBound)
    (A B : L.Configuration)
    (target source : L.geometry.Edge)
    (u v : L.Gauge)
    (hAgree : L.AgreeOffLink A B source) :
    |(L.gibbsExponent (L.replaceLink A target u) -
        L.gibbsExponent (L.replaceLink B target u)) -
      (L.gibbsExponent (L.replaceLink A target v) -
        L.gibbsExponent (L.replaceLink B target v))| ≤
      L.beta *
        (2 * ((L.sharedPlaquettes target source).card : ℝ) * energyBound) := by
  have hAction :=
    compact_oriented_wilsonAction_sourceResponse_oscillation_abs_le_shared
      L energyBound hEnergyBound_nonneg hEnergy_le
      A B target source u v hAgree
  have hRewrite :
      (L.gibbsExponent (L.replaceLink A target u) -
          L.gibbsExponent (L.replaceLink B target u)) -
        (L.gibbsExponent (L.replaceLink A target v) -
          L.gibbsExponent (L.replaceLink B target v)) =
      -L.beta *
        ((L.wilsonAction (L.replaceLink A target u) -
            L.wilsonAction (L.replaceLink B target u)) -
          (L.wilsonAction (L.replaceLink A target v) -
            L.wilsonAction (L.replaceLink B target v))) := by
    unfold CompactOrientedGaugeWilsonSystem.gibbsExponent
    ring
  rw [hRewrite, abs_mul, abs_neg, abs_of_nonneg L.beta_nonneg]
  exact mul_le_mul_of_nonneg_left hAction L.beta_nonneg

end

end MathlibAnalytic
end MGAP4D
