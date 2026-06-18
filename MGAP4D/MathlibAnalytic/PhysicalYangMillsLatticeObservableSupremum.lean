import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeObservableDomination

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

structure PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeObservableFiniteSupremum
    (E : PhysicalFourDimensionalYangMillsLatticeEmbedding) where
  observable : ∀ n, E.LatticeConfiguration n → ENNReal
  supremum_ne_top :
    (⨆ n,
      ∫⁻ u, observable n u
        ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n))) ≠ ⊤

namespace PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeObservableFiniteSupremum

def toLatticeObservableMomentBound
    {E : PhysicalFourDimensionalYangMillsLatticeEmbedding}
    (S : E.LatticeObservableFiniteSupremum) :
    E.LatticeObservableMomentBound :=
  { observable := S.observable
    momentBound :=
      ⨆ n,
        ∫⁻ u, S.observable n u
          ∂(E.latticeMeasure n : Measure (E.LatticeConfiguration n))
    momentBound_ne_top := S.supremum_ne_top
    uniform_lintegral_le := fun n =>
      le_iSup
        (fun k =>
          ∫⁻ u, S.observable k u
            ∂(E.latticeMeasure k : Measure (E.LatticeConfiguration k))) n }

end PhysicalFourDimensionalYangMillsLatticeEmbedding.LatticeObservableFiniteSupremum

end

end MathlibAnalytic
end MGAP4D
