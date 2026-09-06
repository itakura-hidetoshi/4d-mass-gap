import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkConditional
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonRemoteCancellation

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Adding a constant to an integrable logarithmic density does not change
its normalized exponential tilt. -/
theorem tilted_add_const_normalization_eq
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ)
    (c : ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) μ) :
    μ.tilted (fun x => f x + c) = μ.tilted f := by
  haveI : IsProbabilityMeasure (μ.tilted f) :=
    MeasureTheory.isProbabilityMeasure_tilted hf
  have hTilt :=
    MeasureTheory.tilted_tilted (μ := μ) hf (fun _ : α => c)
  have hConst :
      (μ.tilted f).tilted (fun _ : α => c) = μ.tilted f :=
    MeasureTheory.tilted_const (μ.tilted f) c
  have hAdd :
      μ.tilted (f + fun _ : α => c) = μ.tilted f :=
    hTilt.symm.trans hConst
  calc
    μ.tilted (fun x => f x + c) =
        μ.tilted (f + fun _ : α => c) := by
      apply MeasureTheory.tilted_congr
      filter_upwards with x
      rfl
    _ = μ.tilted f := hAdd

/-- The part of the one-link logarithmic Gibbs weight that depends on the
inserted target variable. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkLocalGibbsExponent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ :=
  -C.base.beta *
    C.base.targetLocalPlaquetteAction
      (C.base.replaceLink A target g) target

/-- The part of the one-link logarithmic Gibbs weight that is independent of
the inserted target variable. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkRemoteGibbsConstant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  -C.base.beta * C.base.targetRemotePlaquetteAction A target

/-- Exact decomposition of the one-link Gibbs exponent into its target-local
variable-dependent part and a target-remote constant. -/
theorem continuous_compact_oriented_singleLinkGibbsExponent_eq_local_add_remote
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.base.gibbsExponent (C.base.replaceLink A target g) =
      C.singleLinkLocalGibbsExponent A target g +
        C.singleLinkRemoteGibbsConstant A target := by
  unfold CompactOrientedGaugeWilsonSystem.gibbsExponent
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkLocalGibbsExponent
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkRemoteGibbsConstant
  rw [compact_oriented_wilsonAction_replaceLink_eq_local_add_remote]
  ring

/-- A modification of a source link outside the target plaquette neighborhood
does not change the variable-dependent local part of the target one-link
Gibbs exponent. -/
theorem continuous_compact_oriented_singleLinkLocalGibbsExponent_eq_of_not_neighbor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target source : C.base.geometry.Edge)
    (g : C.base.Gauge)
    (hNotNeighbor : source ∉ C.base.plaquetteNeighbors target)
    (hAgree : C.base.AgreeOffLink A B source) :
    C.singleLinkLocalGibbsExponent A target g =
      C.singleLinkLocalGibbsExponent B target g := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkLocalGibbsExponent
  rw [compact_oriented_targetLocalPlaquetteAction_replaceLink_eq_of_not_neighbor
    C.base A B target source g hNotNeighbor hAgree]

/-- For configurations differing only at a remote source link, the two raw
one-link Gibbs exponents may differ, but only by a constant independent of the
inserted target value. -/
theorem continuous_compact_oriented_singleLinkGibbsExponent_eq_add_remoteConstant_of_not_neighbor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target source : C.base.geometry.Edge)
    (g : C.base.Gauge)
    (hNotNeighbor : source ∉ C.base.plaquetteNeighbors target)
    (hAgree : C.base.AgreeOffLink A B source) :
    C.base.gibbsExponent (C.base.replaceLink A target g) =
      C.base.gibbsExponent (C.base.replaceLink B target g) +
        (C.singleLinkRemoteGibbsConstant A target -
          C.singleLinkRemoteGibbsConstant B target) := by
  rw [continuous_compact_oriented_singleLinkGibbsExponent_eq_local_add_remote,
    continuous_compact_oriented_singleLinkGibbsExponent_eq_local_add_remote,
    continuous_compact_oriented_singleLinkLocalGibbsExponent_eq_of_not_neighbor
      C A B target source g hNotNeighbor hAgree]
  ring

/-- Exact normalized one-link conditional laws are insensitive to a change of
one source link outside the target plaquette neighborhood.  The remote change
need not preserve the raw Gibbs exponent: its target-independent contribution
cancels in normalization. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_not_neighbor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target source : C.base.geometry.Edge)
    (hNotNeighbor : source ∉ C.base.plaquetteNeighbors target)
    (hAgree : C.base.AgreeOffLink A B source) :
    C.singleLinkConditionalMeasure A target =
      C.singleLinkConditionalMeasure B target := by
  let c : ℝ :=
    C.singleLinkRemoteGibbsConstant A target -
      C.singleLinkRemoteGibbsConstant B target
  have hExp : ∀ g : C.base.Gauge,
      C.base.gibbsExponent (C.base.replaceLink A target g) =
        C.base.gibbsExponent (C.base.replaceLink B target g) + c := by
    intro g
    exact
      continuous_compact_oriented_singleLinkGibbsExponent_eq_add_remoteConstant_of_not_neighbor
        C A B target source g hNotNeighbor hAgree
  have hIntegrable :
      Integrable
        (fun g : C.base.Gauge =>
          Real.exp (C.base.gibbsExponent
            (C.base.replaceLink B target g)))
        (normalizedCompactHaar C.base.Gauge) := by
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor] using
      (continuous_compact_oriented_singleLinkBoltzmannIntegrable C B target)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalMeasure
  calc
    (normalizedCompactHaar C.base.Gauge).tilted
        (fun g => C.base.gibbsExponent (C.base.replaceLink A target g)) =
      (normalizedCompactHaar C.base.Gauge).tilted
        (fun g => C.base.gibbsExponent (C.base.replaceLink B target g) + c) := by
      apply MeasureTheory.tilted_congr
      filter_upwards with g
      exact hExp g
    _ = (normalizedCompactHaar C.base.Gauge).tilted
        (fun g => C.base.gibbsExponent (C.base.replaceLink B target g)) := by
      exact tilted_add_const_normalization_eq
        (normalizedCompactHaar C.base.Gauge)
        (fun g => C.base.gibbsExponent (C.base.replaceLink B target g))
        c hIntegrable

/-- Concrete remote replacement form of conditional locality, ready for the
same-color heat-bath commutation step. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_replaceLink_eq_of_not_neighbor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target source : C.base.geometry.Edge)
    (v : C.base.Gauge)
    (hNotNeighbor : source ∉ C.base.plaquetteNeighbors target) :
    C.singleLinkConditionalMeasure (C.base.replaceLink A source v) target =
      C.singleLinkConditionalMeasure A target := by
  apply continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_not_neighbor
    C (C.base.replaceLink A source v) A target source hNotNeighbor
  intro e he
  exact compact_oriented_replaceLink_other C.base A source e v he

end
end MathlibAnalytic
end MGAP4D
