import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsSectorFactorization
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonCrossingKernel
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exponentiating a negative scalar multiple of a finite list sum produces the
product of the corresponding exponential factors. -/
theorem real_exp_neg_mul_list_sum_eq_map_exp_prod
    (beta : ℝ) (xs : List ℝ) :
    Real.exp (-beta * xs.sum) =
      (xs.map fun x => Real.exp (-beta * x)).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons, List.prod_cons]
      rw [show -beta * (x + xs.sum) =
          (-beta * x) + (-beta * xs.sum) by ring]
      rw [Real.exp_add, ih]

/-- Canonical list of Wilson energies of all crossing plaquettes on the even
periodic four-dimensional lattice. -/
noncomputable def periodicHypercubicEvenCrossingWilsonPlaquetteEnergyTerms
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : List ℝ :=
  (periodicHypercubicEvenCrossingPlaquetteList H).map fun p =>
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy A p.1)

/-- Summing the canonical crossing-plaquette energy list recovers exactly the
crossing sector of the physical Wilson action. -/
theorem periodicHypercubicEvenCrossingWilsonPlaquetteEnergyTerms_sum
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenCrossingWilsonPlaquetteEnergyTerms H N A).sum =
      periodicHypercubicEvenCrossingWilsonAction H N A := by
  classical
  calc
    (periodicHypercubicEvenCrossingWilsonPlaquetteEnergyTerms H N A).sum =
        ∑ p : PeriodicHypercubicEvenCrossingPlaquetteLabel H,
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p.1) := by
      simp [periodicHypercubicEvenCrossingWilsonPlaquetteEnergyTerms,
        periodicHypercubicEvenCrossingPlaquetteList]
    _ = ∑ p ∈ {p : PeriodicHypercubicEvenPlaquette H |
          periodicHypercubicEvenCrossingPlaquette p}.toFinset,
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p) := by
      symm
      exact Finset.sum_toFinset_eq_subtype
        periodicHypercubicEvenCrossingPlaquette
        (fun p : PeriodicHypercubicEvenPlaquette H =>
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p))
    _ = periodicHypercubicEvenCrossingWilsonAction H N A := by
      simp [periodicHypercubicEvenCrossingWilsonAction,
        propositionIndicator,
        periodicHypercubicEvenCrossingPlaquette,
        periodicHypercubicEvenCrossingSupport,
        periodicHypercubicEvenStrictPositivePlaquette,
        periodicHypercubicEvenStrictNegativePlaquette]

/-- The genuine crossing-sector Wilson Boltzmann weight is exactly the finite
product of one-plaquette Wilson central functions over the canonical crossing
plaquette list. -/
theorem periodicHypercubicEvenCrossingWilsonBoltzmannWeight_eq_plaquetteList_product
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenCrossingWilsonBoltzmannWeight H N beta A =
      ((periodicHypercubicEvenCrossingPlaquetteList H).map fun p =>
        specialUnitaryWilsonBoltzmannCentralFunction N beta
          (periodicHypercubicPlaquetteHolonomy A p.1)).prod := by
  unfold periodicHypercubicEvenCrossingWilsonBoltzmannWeight
  rw [← periodicHypercubicEvenCrossingWilsonPlaquetteEnergyTerms_sum H N A]
  rw [real_exp_neg_mul_list_sum_eq_map_exp_prod]
  simp [periodicHypercubicEvenCrossingWilsonPlaquetteEnergyTerms,
    List.map_map, specialUnitaryWilsonBoltzmannCentralFunction,
    Function.comp_def]

/-- Fintype-product form of the exact crossing-sector Wilson Boltzmann
factorization. -/
theorem periodicHypercubicEvenCrossingWilsonBoltzmannWeight_eq_plaquette_product
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenCrossingWilsonBoltzmannWeight H N beta A =
      ∏ p : PeriodicHypercubicEvenCrossingPlaquetteLabel H,
        specialUnitaryWilsonBoltzmannCentralFunction N beta
          (periodicHypercubicPlaquetteHolonomy A p.1) := by
  rw [periodicHypercubicEvenCrossingWilsonBoltzmannWeight_eq_plaquetteList_product]
  simp [periodicHypercubicEvenCrossingPlaquetteList]

end

end MathlibAnalytic
end MGAP4D
