import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeObservableDomination

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The affine-renormalized Wilson action used as a nonnegative lattice control
observable. The scale and offset may depend on the lattice spacing/volume index. -/
def ContinuousCompactGaugeWilsonPhysicalEmbedding.renormalizedWilsonActionObservable
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (scale offset : ℕ → ENNReal)
    (n : ℕ)
    (U : (E.system n).base.Configuration) : ENNReal :=
  scale n * ENNReal.ofReal ((E.system n).base.wilsonAction U) + offset n

/-- A finite uniform expectation receipt for affine-renormalized Wilson actions
under the original finite-volume Gibbs probability laws. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionControlMomentBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (scale offset : ℕ → ENNReal) where
  momentBound : ENNReal
  momentBound_ne_top : momentBound ≠ ⊤
  uniform_lintegral_le :
    ∀ n,
      ∫⁻ U,
        E.renormalizedWilsonActionObservable scale offset n U
        ∂((E.system n).gibbsProbabilityMeasure :
          Measure (E.system n).base.Configuration) ≤ momentBound

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionControlMomentBound

/-- Forget the Wilson origin and expose the renormalized action as the generic
uniformly integrable lattice observable. -/
def toLatticeObservableMomentBound
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {scale offset : ℕ → ENNReal}
    (M : E.WilsonActionControlMomentBound scale offset) :
    E.LatticeObservableMomentBound :=
  { observable := fun n U =>
      E.renormalizedWilsonActionObservable scale offset n U
    momentBound := M.momentBound
    momentBound_ne_top := M.momentBound_ne_top
    uniform_lintegral_le := M.uniform_lintegral_le }

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionControlMomentBound

/-- A deterministic estimate comparing the interpolated physical coercive
functional with an affine-renormalized finite-lattice Wilson action. -/
structure ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionControlsFunctional
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal) : Prop where
  pointwise_le :
    ∀ n U,
      Phi.toFun (E.interpolate n U) ≤
        E.renormalizedWilsonActionObservable scale offset n U

namespace ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionControlsFunctional

/-- Combine the deterministic interpolation estimate with the Wilson-action
moment receipt to obtain generic lattice-observable domination. -/
def toLatticeObservableDomination
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (D : E.WilsonActionControlsFunctional Phi scale offset)
    (M : E.WilsonActionControlMomentBound scale offset) :
    E.LatticeObservableDominatesFunctional Phi
      M.toLatticeObservableMomentBound :=
  { pointwise_le := D.pointwise_le }

/-- Renormalized Wilson-action domination and a finite uniform Gibbs expectation
imply tightness of the interpolated Wilson laws. -/
theorem isTight
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (D : E.WilsonActionControlsFunctional Phi scale offset)
    (M : E.WilsonActionControlMomentBound scale offset) :
    IsTightMeasureSet E.toLatticeEmbedding.embeddedMeasureSet :=
  (D.toLatticeObservableDomination M).isTight

/-- The concrete Wilson-action control receipts produce a physical continuum
weak limit, preserving zero lattice spacing and infinite physical volume along
the Prokhorov subsequence. -/
noncomputable def toWeakLimit
    {E : ContinuousCompactGaugeWilsonPhysicalEmbedding}
    {Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional}
    {scale offset : ℕ → ENNReal}
    (D : E.WilsonActionControlsFunctional Phi scale offset)
    (M : E.WilsonActionControlMomentBound scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  (D.toLatticeObservableDomination M).toWeakLimit

end ContinuousCompactGaugeWilsonPhysicalEmbedding.WilsonActionControlsFunctional

/-- Public constructor from the two remaining concrete Wilson analytic
receipts: deterministic physical coercivity and a uniform action expectation. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_actionControl
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (scale offset : ℕ → ENNReal)
    (D : E.WilsonActionControlsFunctional Phi scale offset)
    (M : E.WilsonActionControlMomentBound scale offset) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  D.toWeakLimit M

end

end MathlibAnalytic
end MGAP4D
