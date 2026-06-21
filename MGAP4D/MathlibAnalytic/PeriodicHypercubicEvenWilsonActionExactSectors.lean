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

theorem periodicHypercubicEvenNegativeResidualWilsonAction_eq_negativeWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenNegativeResidualWilsonAction H N A =
      periodicHypercubicEvenNegativeWilsonAction H N A := by
  classical
  unfold periodicHypercubicEvenNegativeResidualWilsonAction
  unfold periodicHypercubicEvenNegativeWilsonAction
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hneg : periodicHypercubicEvenStrictNegativePlaquette p
  · have hnpos : ¬ periodicHypercubicEvenStrictPositivePlaquette p :=
      periodicHypercubicEvenStrictNegativePlaquette_not_strictPositivePlaquette
        H p hneg
    simp [propositionIndicator, hneg, hnpos]
  · simp [propositionIndicator, hneg]

end

end MathlibAnalytic
end MGAP4D
