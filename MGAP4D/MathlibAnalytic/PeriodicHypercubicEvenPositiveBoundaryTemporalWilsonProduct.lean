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

noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H) : ℝ :=
  Real.exp
    (-beta * propositionIndicator
      (periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p)))

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
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor
  exact real_exp_neg_mul_finset_sum_eq_prod
    (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)) beta
    (fun p => propositionIndicator
      (periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p)))

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
  simp [periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor,
    propositionIndicator, hp]

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
  simp [periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor,
    propositionIndicator, hp]

end

end MathlibAnalytic
end MGAP4D