import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeObservableDomination

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A finite lattice observable bounded by one finite constant at every scale
and every configuration. Probability normalization turns this deterministic
bound into a uniform expectation estimate automatically. -/
structure PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeObservableUniformPointwiseBound
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) where
  observable : ∀ n, E.LatticeConfiguration n → ENNReal
  bound : ENNReal
  bound_ne_top : bound ≠ ⊤
  pointwise_le : ∀ n u, observable n u ≤ bound

namespace PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeObservableUniformPointwiseBound

/-- A uniform pointwise bound implies the corresponding uniform first-moment
bound because every lattice law is a probability measure. -/
def toLatticeObservableMomentBound
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (B : E.LatticeObservableUniformPointwiseBound) :
    E.LatticeObservableMomentBound :=
  { observable := B.observable
    momentBound := B.bound
    momentBound_ne_top := B.bound_ne_top
    uniform_lintegral_le := by
      intro n
      calc
        ∫⁻ u, B.observable n u
            ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n)) ≤
            ∫⁻ _u, B.bound
              ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n)) :=
          lintegral_mono (B.pointwise_le n)
        _ = B.bound := by simp }

/-- A uniformly bounded lattice observable dominating a physical coercive
functional implies tightness of the embedded laws. -/
theorem isTight
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    {Phi : E.PhysicalCoerciveFunctional}
    (B : E.LatticeObservableUniformPointwiseBound)
    (D : E.LatticeObservableDominatesFunctional
      Phi B.toLatticeObservableMomentBound) :
    IsTightMeasureSet E.embeddedMeasureSet :=
  D.isTight

/-- The deterministic pointwise-bound route produces a physical weak limit. -/
noncomputable def toWeakLimit
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    {Phi : E.PhysicalCoerciveFunctional}
    (B : E.LatticeObservableUniformPointwiseBound)
    (D : E.LatticeObservableDominatesFunctional
      Phi B.toLatticeObservableMomentBound) :
    PhysicalFourDimensionalYangMillsWeakLimit :=
  D.toWeakLimit

end PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeObservableUniformPointwiseBound

end

end MathlibAnalytic
end MGAP4D
