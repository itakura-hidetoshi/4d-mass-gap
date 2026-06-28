import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Replace one physical positive-link value in a compact oriented configuration. -/
def CompactOrientedGaugeWilsonSystem.replaceLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge)
    (g : L.Gauge) : L.Configuration := by
  classical
  exact fun e => if e = target then g else A e

@[simp] theorem compact_oriented_replaceLink_same
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge)
    (g : L.Gauge) :
    L.replaceLink A target g target = g := by
  simp [CompactOrientedGaugeWilsonSystem.replaceLink]

@[simp] theorem compact_oriented_replaceLink_of_ne
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target e : L.geometry.Edge)
    (g : L.Gauge)
    (h : e ≠ target) :
    L.replaceLink A target g e = A e := by
  simp [CompactOrientedGaugeWilsonSystem.replaceLink, h]

@[simp] theorem compact_oriented_replaceLink_current
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge) :
    L.replaceLink A target (A target) = A := by
  funext e
  by_cases h : e = target
  · subst e
    simp
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, h]

/-- Agreement of compact oriented configurations away from one physical link. -/
def CompactOrientedGaugeWilsonSystem.AgreeOffLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (source : L.geometry.Edge) : Prop :=
  ∀ e : L.geometry.Edge, e ≠ source → A e = B e

/-- Replacing the exceptional link erases every difference confined to it. -/
theorem compact_oriented_replaceLink_eq_of_agreeOffLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target : L.geometry.Edge)
    (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B target) :
    L.replaceLink A target g = L.replaceLink B target g := by
  funext e
  by_cases h : e = target
  · subst e
    simp
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, h, hAgree e h]

/-- The physical-link replacement map is continuous in the inserted compact
Gauge value. -/
theorem continuous_compact_oriented_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Continuous (fun g : C.base.Gauge => C.base.replaceLink A target g) := by
  classical
  apply continuous_pi
  intro e
  by_cases h : e = target
  · subst e
    simpa [CompactOrientedGaugeWilsonSystem.replaceLink] using
      (continuous_id : Continuous (fun g : C.base.Gauge => g))
  · simpa [CompactOrientedGaugeWilsonSystem.replaceLink, h] using
      (continuous_const : Continuous (fun _ : C.base.Gauge => A e))

/-- Logarithmic one-link conditional Gibbs weight. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkGibbsExponent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ :=
  C.base.gibbsExponent (C.base.replaceLink A target g)

/-- The one-link Gibbs exponent is continuous. -/
theorem continuous_compact_oriented_singleLinkGibbsExponent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Continuous (C.singleLinkGibbsExponent A target) :=
  (continuous_compact_oriented_gibbsExponent C).comp
    (continuous_compact_oriented_replaceLink C A target)

/-- The one-link exponential Gibbs density is integrable against normalized
compact Haar measure. -/
theorem continuous_compact_oriented_singleLinkBoltzmannIntegrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Integrable
      (fun g : C.base.Gauge => Real.exp (C.singleLinkGibbsExponent A target g))
      (normalizedCompactHaar C.base.Gauge) := by
  exact
    (Real.continuous_exp.comp
      (continuous_compact_oriented_singleLinkGibbsExponent C A target)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- One-link conditional partition function. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  ∫ g : C.base.Gauge,
    Real.exp (C.singleLinkGibbsExponent A target g)
      ∂normalizedCompactHaar C.base.Gauge

/-- Every compact one-link conditional partition function is positive. -/
theorem continuous_compact_oriented_singleLinkPartitionFunction_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    0 < C.singleLinkPartitionFunction A target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
  exact integral_exp_pos
    (continuous_compact_oriented_singleLinkBoltzmannIntegrable C A target)

/-- Exact compact-Haar one-link conditional Gibbs probability measure. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : Measure C.base.Gauge :=
  (normalizedCompactHaar C.base.Gauge).tilted
    (C.singleLinkGibbsExponent A target)

/-- The exact compact-Haar one-link conditional law is a probability measure. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalMeasure
  exact MeasureTheory.isProbabilityMeasure_tilted
    (continuous_compact_oriented_singleLinkBoltzmannIntegrable C A target)

/-- The compact one-link conditional exponent depends only on off-target data. -/
theorem continuous_compact_oriented_singleLinkGibbsExponent_eq_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B target) :
    C.singleLinkGibbsExponent A target =
      C.singleLinkGibbsExponent B target := by
  funext g
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkGibbsExponent
  rw [compact_oriented_replaceLink_eq_of_agreeOffLink
    C.base A B target g hAgree]

/-- The exact compact-Haar conditional law is constant on every off-target
configuration fiber. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B target) :
    C.singleLinkConditionalMeasure A target =
      C.singleLinkConditionalMeasure B target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalMeasure
  rw [continuous_compact_oriented_singleLinkGibbsExponent_eq_of_agreeOffLink
    C A B target hAgree]

end
end MathlibAnalytic
end MGAP4D
