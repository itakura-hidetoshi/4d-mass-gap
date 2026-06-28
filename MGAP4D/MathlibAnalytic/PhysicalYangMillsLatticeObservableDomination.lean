import MGAP4D.MathlibAnalytic.PhysicalYangMillsCoerciveFunctionalLimit

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A nonnegative observable on every varying finite lattice configuration
space, together with one finite uniform expectation bound. -/
structure PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeObservableMomentBound
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) where
  observable : ∀ n, E.LatticeConfiguration n → ENNReal
  momentBound : ENNReal
  momentBound_ne_top : momentBound ≠ ⊤
  uniform_lintegral_le :
    ∀ n,
      ∫⁻ u, observable n u
        ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n)) ≤ momentBound

/-- A deterministic interpolation estimate saying that one lattice observable
controls the physical coercive functional pointwise at every scale. -/
structure PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeObservableDominatesFunctional
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding)
    (Phi : E.PhysicalCoerciveFunctional)
    (O : E.LatticeObservableMomentBound) : Prop where
  pointwise_le :
    ∀ n u, Phi.toFun (E.interpolate n u) ≤ O.observable n u

namespace PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeObservableDominatesFunctional

/-- Pointwise domination transfers the uniform observable moment bound to the
physical coercive functional. -/
def toLatticeCoerciveFunctionalMomentBound
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    {Phi : E.PhysicalCoerciveFunctional}
    {O : E.LatticeObservableMomentBound}
    (D : E.LatticeObservableDominatesFunctional Phi O) :
    E.LatticeCoerciveFunctionalMomentBound Phi :=
  { momentBound := O.momentBound
    momentBound_ne_top := O.momentBound_ne_top
    uniform_lattice_lintegral_le := by
      intro n
      exact
        (lintegral_mono fun u => D.pointwise_le n u).trans
          (O.uniform_lintegral_le n) }

/-- A uniformly integrable dominating lattice observable implies tightness of
the interpolated physical laws. -/
theorem isTight
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    {Phi : E.PhysicalCoerciveFunctional}
    {O : E.LatticeObservableMomentBound}
    (D : E.LatticeObservableDominatesFunctional Phi O) :
    IsTightMeasureSet E.embeddedMeasureSet :=
  D.toLatticeCoerciveFunctionalMomentBound.isTight

/-- A physical coercive functional controlled by a uniformly integrable lattice
observable produces a physical continuum weak limit. -/
noncomputable def toWeakLimit
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    {Phi : E.PhysicalCoerciveFunctional}
    {O : E.LatticeObservableMomentBound}
    (D : E.LatticeObservableDominatesFunctional Phi O) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  physical_yang_mills_weak_limit_of_latticeCoerciveFunctionalMomentBound
    E Phi D.toLatticeCoerciveFunctionalMomentBound

end PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeObservableDominatesFunctional

/-- The same observable receipt specialized to continuous compact-gauge Wilson
Gibbs laws. -/
abbrev ContinuousCompactGaugeWilsonPhysicalEmbedding.LatticeObservableMomentBound
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding) :=
  E.toLatticeEmbedding.LatticeObservableMomentBound

/-- Wilson specialization of deterministic observable domination. -/
abbrev ContinuousCompactGaugeWilsonPhysicalEmbedding.LatticeObservableDominatesFunctional
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (O : E.LatticeObservableMomentBound) :=
  E.toLatticeEmbedding.LatticeObservableDominatesFunctional Phi O

/-- Continuous compact-gauge Wilson weak limit obtained from a dominating
finite-lattice observable with a finite uniform expectation bound. -/
noncomputable def
    continuous_compact_gauge_wilson_weak_limit_of_latticeObservableDomination
    (E : ContinuousCompactGaugeWilsonPhysicalEmbedding)
    (Phi : E.toLatticeEmbedding.PhysicalCoerciveFunctional)
    (O : E.LatticeObservableMomentBound)
    (D : E.LatticeObservableDominatesFunctional Phi O) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  D.toWeakLimit

end

end MathlibAnalytic
end MGAP4D
