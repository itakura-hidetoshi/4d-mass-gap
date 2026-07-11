import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsCanonicalGaugeFieldRealization

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Canonical edge point before packaging a realization. -/
noncomputable def finiteWilsonCanonicalEdgePointAt
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (e : (W.system s).Edge) : EuclideanFourSpace :=
  fun i => if i = 0 then ((Fintype.equivFin (W.system s).Edge e).val : ℝ) else 0

/-- The canonical edge placement is injective. -/
theorem finiteWilsonCanonicalEdgePointAt_injective
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index) :
    Function.Injective (finiteWilsonCanonicalEdgePointAt W s) := by
  intro e f hef
  apply (Fintype.equivFin (W.system s).Edge).injective
  apply Fin.ext
  have h0 := congrFun hef (0 : Fin 4)
  simp [finiteWilsonCanonicalEdgePointAt] at h0
  exact_mod_cast h0

/-- The unique edge represented by a point in the canonical finite image. -/
noncomputable def finiteWilsonCanonicalEdgeAt
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (x : EuclideanFourSpace)
    (hx : ∃ e : (W.system s).Edge,
      finiteWilsonCanonicalEdgePointAt W s e = x) :
    (W.system s).Edge :=
  Classical.choose hx

/-- Selecting at the canonical point of an edge returns that edge. -/
theorem finiteWilsonCanonicalEdgeAt_edgePoint
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (e : (W.system s).Edge) :
    finiteWilsonCanonicalEdgeAt W s
      (finiteWilsonCanonicalEdgePointAt W s e) ⟨e, rfl⟩ = e := by
  apply finiteWilsonCanonicalEdgePointAt_injective W s
  exact Classical.choose_spec
    (show ∃ f : (W.system s).Edge,
      finiteWilsonCanonicalEdgePointAt W s f =
        finiteWilsonCanonicalEdgePointAt W s e from ⟨e, rfl⟩)

/-- Gauge-valued global observation: link value on the canonical edge image and
identity away from that image. -/
noncomputable def finiteWilsonCanonicalGaugeGlobalObserve
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (A : (W.system s).Configuration) :
    EuclideanFourSpace → (W.system s).Gauge :=
  fun x =>
    if hx : ∃ e : (W.system s).Edge,
        finiteWilsonCanonicalEdgePointAt W s e = x then
      A (finiteWilsonCanonicalEdgeAt W s x hx)
    else
      1

/-- The canonical global observation reads every physical link exactly. -/
theorem finiteWilsonCanonicalGaugeGlobalObserve_edge
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (A : (W.system s).Configuration)
    (e : (W.system s).Edge) :
    finiteWilsonCanonicalGaugeGlobalObserve W s A
      (finiteWilsonCanonicalEdgePointAt W s e) = A e := by
  rw [finiteWilsonCanonicalGaugeGlobalObserve]
  simp only [dif_pos ⟨e, rfl⟩]
  rw [finiteWilsonCanonicalEdgeAt_edgePoint]

/-- Package the explicit global field as canonical gauge-field data. -/
noncomputable def finiteWilsonCanonicalGaugeFieldData
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Countable (W.system s).Configuration]
    [MeasurableSingletonClass (W.system s).Configuration] :
    FiniteWilsonGibbsCanonicalGaugeFieldData W where
  sourceScale := s
  globalObserve := finiteWilsonCanonicalGaugeGlobalObserve W s
  globalObserve_measurable := measurable_of_countable _
  globalObserve_edge := by
    intro A e
    exact finiteWilsonCanonicalGaugeGlobalObserve_edge W s A e

/-- The explicit canonical global field yields faithful observation. -/
def finiteWilsonCanonicalGaugeField_faithful
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Countable (W.system s).Configuration]
    [MeasurableSingletonClass (W.system s).Configuration] :
    FiniteWilsonGibbsFaithfulGlobalObservation
      (finiteWilsonCanonicalGaugeFieldData W s).realization :=
  (finiteWilsonCanonicalGaugeFieldData W s).toFaithfulGlobalObservation

end

end MathlibAnalytic
end MGAP4D
