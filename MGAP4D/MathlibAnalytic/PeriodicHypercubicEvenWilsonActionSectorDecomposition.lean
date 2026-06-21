import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCrossingPlaquette
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- An exact three-sector decomposition of a finite sum. The second predicate
is tested only after the first has failed, so no disjointness hypothesis is
needed. -/
theorem finset_sum_eq_first_add_secondResidual_add_neither
    {ι M : Type*} [AddCommMonoid M]
    (s : Finset ι) (first second : ι → Prop)
    [DecidablePred first] [DecidablePred second]
    (f : ι → M) :
    (∑ i ∈ s, f i) =
      (∑ i ∈ s.filter first, f i) +
      (∑ i ∈ s.filter (fun i => ¬ first i ∧ second i), f i) +
      (∑ i ∈ s.filter (fun i => ¬ first i ∧ ¬ second i), f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hFirst : first a
      · simp [ha, hFirst, ih, add_assoc, add_comm, add_left_comm]
      · by_cases hSecond : second a
        · simp [ha, hFirst, hSecond, ih, add_assoc, add_comm, add_left_comm]
        · simp [ha, hFirst, hSecond, ih, add_assoc, add_comm, add_left_comm]

/-- Positive-open-half contribution to the periodic `SU(N)` Wilson action. -/
noncomputable def periodicHypercubicEvenPositiveWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ := by
  classical
  exact
    ∑ p ∈ Finset.univ.filter periodicHypercubicEvenStrictPositivePlaquette,
      specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p)

/-- Negative-open-half contribution after removing any plaquette already
classified as strictly positive. -/
noncomputable def periodicHypercubicEvenNegativeResidualWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ := by
  classical
  exact
    ∑ p ∈ Finset.univ.filter (fun p =>
        ¬ periodicHypercubicEvenStrictPositivePlaquette p ∧
          periodicHypercubicEvenStrictNegativePlaquette p),
      specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p)

/-- Crossing-plane contribution to the periodic `SU(N)` Wilson action. -/
noncomputable def periodicHypercubicEvenCrossingWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ := by
  classical
  exact
    ∑ p ∈ Finset.univ.filter periodicHypercubicEvenCrossingPlaquette,
      specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p)

/-- The actual even-periodic `SU(N)` Wilson action is exactly the sum of its
positive, negative-residual, and crossing-plane plaquette sectors. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_sector_decomposition
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
      periodicHypercubicEvenNegativeResidualWilsonAction H N A +
      periodicHypercubicEvenCrossingWilsonAction H N A := by
  classical
  rw [periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction]
  simpa [periodicHypercubicEvenPositiveWilsonAction,
    periodicHypercubicEvenNegativeResidualWilsonAction,
    periodicHypercubicEvenCrossingWilsonAction,
    periodicHypercubicEvenCrossingPlaquette,
    periodicHypercubicEvenCrossingSupport,
    periodicHypercubicEvenStrictPositivePlaquette,
    periodicHypercubicEvenStrictNegativePlaquette] using
    (finset_sum_eq_first_add_secondResidual_add_neither
      (s := (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)))
      (first := periodicHypercubicEvenStrictPositivePlaquette)
      (second := periodicHypercubicEvenStrictNegativePlaquette)
      (f := fun p => specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p)))

end

end MathlibAnalytic
end MGAP4D
