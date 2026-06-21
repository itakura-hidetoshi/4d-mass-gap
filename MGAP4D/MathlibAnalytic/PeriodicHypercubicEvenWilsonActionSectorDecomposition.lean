import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCrossingPlaquette
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

/-- The value `x` on a proposition and zero off it, with classical
proposition decidability hidden inside one stable definition. -/
noncomputable def propositionIndicator
    {M : Type*} [Zero M] (p : Prop) (x : M) : M := by
  classical
  exact if p then x else 0

/-- Exact decomposition of a finite sum into the first sector, the residual
second sector, and the sector belonging to neither predicate. -/
theorem finset_sum_eq_first_add_secondResidual_add_neither
    {ι M : Type*} [AddCommMonoid M]
    (s : Finset ι) (first second : ι → Prop) (f : ι → M) :
    (∑ i ∈ s, f i) =
      (∑ i ∈ s, propositionIndicator (first i) (f i)) +
      (∑ i ∈ s,
        propositionIndicator (¬ first i ∧ second i) (f i)) +
      (∑ i ∈ s,
        propositionIndicator (¬ first i ∧ ¬ second i) (f i)) := by
  classical
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hFirst : first i
  · simp [propositionIndicator, hFirst]
  · by_cases hSecond : second i
    · simp [propositionIndicator, hFirst, hSecond]
    · simp [propositionIndicator, hFirst, hSecond]

/-- Positive-open-half contribution to the periodic `SU(N)` Wilson action. -/
noncomputable def periodicHypercubicEvenPositiveWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
    propositionIndicator
      (periodicHypercubicEvenStrictPositivePlaquette p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p))

/-- Negative-open-half contribution after removing plaquettes already in the
strictly positive sector. -/
noncomputable def periodicHypercubicEvenNegativeResidualWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
    propositionIndicator
      (¬ periodicHypercubicEvenStrictPositivePlaquette p ∧
        periodicHypercubicEvenStrictNegativePlaquette p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p))

/-- Crossing-plane contribution, namely the residual sector in neither strict
open half-torus. -/
noncomputable def periodicHypercubicEvenCrossingWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
    propositionIndicator
      (¬ periodicHypercubicEvenStrictPositivePlaquette p ∧
        ¬ periodicHypercubicEvenStrictNegativePlaquette p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p))

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
