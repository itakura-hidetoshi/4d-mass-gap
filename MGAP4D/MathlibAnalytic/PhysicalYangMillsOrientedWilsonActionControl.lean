import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedLatticeEmbedding
import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeObservableDomination

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The affine-renormalized signed Wilson action used as a nonnegative control
observable on each physical positive-link configuration space. -/
def ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.renormalizedWilsonActionObservable
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding)
    (scale offset : ℕ → ENNReal)
    (n : ℕ)
    (U : (E.system n).base.Configuration) : ENNReal :=
  scale n * ENNReal.ofReal ((E.system n).base.wilsonAction U) + offset n

/-- A finite uniform first-moment bound for the affine-renormalized signed
Wilson actions under the orientation-correct finite-volume Gibbs laws. -/
structure ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.WilsonActionControlMomentBound
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding)
    (scale offset : ℕ → ENNReal) where
  momentBound : ENNReal
  momentBound_ne_top : momentBound ≠ ⊤
  uniform_lintegral_le :
    ∀ n,
      ∫⁻ U,
        E.renormalizedWilsonActionObservable scale offset n U
        ∂((E.system n).gibbsProbabilityMeasure :
          Measure (E.system n).base.Configuration) ≤ momentBound

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.WilsonActionControlMomentBound

/-- Expose the signed Wilson action as the generic lattice observable consumed
by the physical compactness spine. -/
def toLatticeObservableMomentBound
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {scale offset : ℕ → ENNReal}
    (M : E.WilsonActionControlMomentBound scale offset) :
    E.toLatticeEmbedding.LatticeObservableMomentBound :=
  { observable := fun n U =>
      E.renormalizedWilsonActionObservable scale offset n U
    momentBound := M.momentBound
    momentBound_ne_top := M.momentBound_ne_top
    uniform_lintegral_le := M.uniform_lintegral_le }

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.WilsonActionControlMomentBound

/-- A deterministic interpolation estimate comparing a physical coercive
functional with the affine-renormalized signed Wilson action. -/
structure ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.WilsonActionControlsFunctional
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal) : Prop where
  pointwise_le :
    ∀ n U,
      Phi.toFun (E.interpolate n U) ≤
        E.renormalizedWilsonActionObservable scale offset n U

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.WilsonActionControlsFunctional

/-- Combine signed-action moments with deterministic physical coercivity. -/
def toLatticeObservableDomination
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (D : E.WilsonActionControlsFunctional Phi scale offset)
    (M : E.WilsonActionControlMomentBound scale offset) :
    E.toLatticeEmbedding.LatticeObservableDominatesFunctional
      Phi M.toLatticeObservableMomentBound :=
  { pointwise_le := D.pointwise_le }

/-- Signed Wilson-action domination and a finite uniform Gibbs expectation imply
tightness of the interpolated orientation-correct laws. -/
theorem isTight
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (D : E.WilsonActionControlsFunctional Phi scale offset)
    (M : E.WilsonActionControlMomentBound scale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  (D.toLatticeObservableDomination M).isTight

/-- The oriented Wilson action-control receipts produce a physical continuum
weak limit by Markov compact containment and Prokhorov extraction. -/
noncomputable def toWeakLimit
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (D : E.WilsonActionControlsFunctional Phi scale offset)
    (M : E.WilsonActionControlMomentBound scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  (D.toLatticeObservableDomination M).toWeakLimit

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.WilsonActionControlsFunctional

/-- Public orientation-correct weak-limit constructor from signed Wilson action
control. -/
noncomputable def
    continuous_compact_oriented_gauge_wilson_weak_limit_of_actionControl
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (D : E.WilsonActionControlsFunctional Phi scale offset)
    (M : E.WilsonActionControlMomentBound scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  D.toWeakLimit M

end

end MathlibAnalytic
end MGAP4D
