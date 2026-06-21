import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCrossingPlaquette
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

noncomputable def finsetFilterByProp
    {ι : Type*} (s : Finset ι) (p : ι → Prop) : Finset ι := by
  classical
  exact s.filter p

theorem finset_sum_eq_first_add_secondResidual_add_neither
    {ι M : Type*} [AddCommMonoid M]
    (s : Finset ι) (first second : ι → Prop) (f : ι → M) :
    (∑ i ∈ s, f i) =
      (∑ i ∈ finsetFilterByProp s first, f i) +
      (∑ i ∈ finsetFilterByProp s (fun i => ¬ first i ∧ second i), f i) +
      (∑ i ∈ finsetFilterByProp s (fun i => ¬ first i ∧ ¬ second i), f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finsetFilterByProp]
  | @insert a s ha ih =>
      by_cases hFirst : first a
      · simp [finsetFilterByProp, ha, hFirst, ih,
          add_assoc, add_comm, add_left_comm]
      · by_cases hSecond : second a
        · simp [finsetFilterByProp, ha, hFirst, hSecond, ih,
            add_assoc, add_comm, add_left_comm]
        · simp [finsetFilterByProp, ha, hFirst, hSecond, ih,
            add_assoc, add_comm, add_left_comm]

noncomputable def periodicHypercubicEvenPositiveWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ finsetFilterByProp
      (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H))
      periodicHypercubicEvenStrictPositivePlaquette,
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy A p)

noncomputable def periodicHypercubicEvenNegativeResidualWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ finsetFilterByProp
      (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H))
      (fun p =>
        ¬ periodicHypercubicEvenStrictPositivePlaquette p ∧
          periodicHypercubicEvenStrictNegativePlaquette p),
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy A p)

noncomputable def periodicHypercubicEvenCrossingWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ finsetFilterByProp
      (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H))
      (fun p =>
        ¬ periodicHypercubicEvenStrictPositivePlaquette p ∧
          ¬ periodicHypercubicEvenStrictNegativePlaquette p),
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy A p)

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
  rw [periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction]
  simpa [periodicHypercubicEvenPositiveWilsonAction,
    periodicHypercubicEvenNegativeResidualWilsonAction,
    periodicHypercubicEvenCrossingWilsonAction] using
    (finset_sum_eq_first_add_secondResidual_add_neither
      (s := (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)))
      (first := periodicHypercubicEvenStrictPositivePlaquette)
      (second := periodicHypercubicEvenStrictNegativePlaquette)
      (f := fun p => specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p)))

end
end MathlibAnalytic
end MGAP4D
