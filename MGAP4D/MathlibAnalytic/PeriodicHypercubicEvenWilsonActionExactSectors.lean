import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOpenHalfDisjointness
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonActionSectorDecomposition

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

noncomputable def periodicHypercubicEvenNegativeWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
    propositionIndicator
      (periodicHypercubicEvenStrictNegativePlaquette p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p))

end

end MathlibAnalytic
end MGAP4D
