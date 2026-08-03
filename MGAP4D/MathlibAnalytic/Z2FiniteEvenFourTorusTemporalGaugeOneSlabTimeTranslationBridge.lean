import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricTimeTranslation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTemporalGaugeOneSlabTransfer

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The upper boundary edge of a geometric one-slab link is exactly the actual
one-step time translation of its lower boundary edge. -/
theorem finiteEvenFourTorusSpatialLink_upperEdge_eq_timeTranslation
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusSpatialLinkTimeTranslation H e =
      finiteEvenFourTorusEdgeTimeTranslationEquiv H
        (finiteEvenFourTorusSpatialLinkEdge H e) :=
  rfl

/-- The one-slab transfer acts between copies of the same canonical spatial
slice Hilbert space because the upper geometric slice is identified with the
lower one by the actual one-step torus time translation. -/
theorem finiteEvenFourTorusZ2OneSlabTransfer_has_actual_geometric_time_step
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ∃ T : FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
        FiniteEvenFourTorusZ2SliceHilbert H,
      T = finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy := by
  exact ⟨finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
    H β energyIdentity energyNontrivial hβ hEnergy, rfl⟩

end

end MathlibAnalytic
end MGAP4D
