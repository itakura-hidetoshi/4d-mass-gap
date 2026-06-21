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

theorem periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_exact_sector_decomposition
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.wilsonAction A =
      periodicHypercubicEvenPositiveWilsonAction H N A +
      periodicHypercubicEvenNegativeWilsonAction H N A +
      periodicHypercubicEvenCrossingWilsonAction H N A := by
  rw [periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_sector_decomposition]
  rw [periodicHypercubicEvenNegativeResidualWilsonAction_eq_negativeWilsonAction]

end

end MathlibAnalytic
end MGAP4D
