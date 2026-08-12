import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingHalfSectors

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private theorem real_exp_neg_mul_finset_sum_eq_prod
    {ι : Type*}
    (s : Finset ι)
    (beta : ℝ)
    (f : ι → ℝ) :
    Real.exp (-beta * ∑ i ∈ s, f i) =
      ∏ i ∈ s, Real.exp (-beta * f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      rw [show -beta * (f a + ∑ i ∈ s, f i) =
          (-beta * f a) + (-beta * ∑ i ∈ s, f i) by ring]
      rw [Real.exp_add, ih]

/-- The actual one-plaquette factor appearing in the full positive-boundary
temporal Wilson product.  Plaquettes outside the positive-boundary temporal
sector contribute the literal multiplicative unit. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H) : ℝ :=
  if periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p then
    Real.exp
      (-beta * specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p))
  else
    1

/-- The positive-boundary temporal Wilson Boltzmann weight is exactly the
finite product of its actual plaquette factors over the full plaquette type.
No crossing plaquette is discarded: inactive plaquettes contribute the degree-
zero multiplicative unit through the sector indicator. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_eq_prod_plaquetteFactor
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight H N beta A =
      ∏ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor
          H N beta A p := by
  classical
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction
  rw [real_exp_neg_mul_finset_sum_eq_prod]
  apply Finset.prod_congr rfl
  intro p _hp
  by_cases hpositive : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p
  · simp [periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor,
      propositionIndicator, hpositive]
  · simp [periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor,
      propositionIndicator, hpositive]

/-- On an active positive-boundary temporal plaquette, the product factor is
exactly its physical one-plaquette Wilson Boltzmann factor. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor_eq_of_positiveBoundary
    {H N : ℕ}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor
        H N beta A p =
      Real.exp
        (-beta * specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A p)) := by
  simp [periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor, hp]

/-- Outside the positive-boundary temporal sector, the corresponding product
factor is exactly one. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor_eq_one_of_not_positiveBoundary
    {H N : ℕ}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : ¬ periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor
        H N beta A p = 1 := by
  simp [periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor, hp]

end

end MathlibAnalytic
end MGAP4D