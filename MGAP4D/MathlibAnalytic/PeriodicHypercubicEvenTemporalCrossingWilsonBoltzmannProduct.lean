import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCrossingWilsonBoltzmannProduct
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCrossingWilsonActionSpatialTemporal

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Finite label type of the time-containing crossing plaquettes. -/
abbrev PeriodicHypercubicEvenTemporalCrossingPlaquetteLabel (H : ℕ) : Type :=
  {p : PeriodicHypercubicEvenPlaquette H //
    periodicHypercubicEvenTemporalCrossingPlaquette p}

noncomputable instance periodicHypercubicEvenTemporalCrossingPlaquetteLabelFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenTemporalCrossingPlaquetteLabel H) := by
  classical
  exact Subtype.fintype periodicHypercubicEvenTemporalCrossingPlaquette

/-- Canonical finite ordered list of all time-containing crossing plaquettes. -/
noncomputable def periodicHypercubicEvenTemporalCrossingPlaquetteList
    (H : ℕ) : List (PeriodicHypercubicEvenTemporalCrossingPlaquetteLabel H) := by
  classical
  exact Finset.univ.toList

@[simp]
theorem periodicHypercubicEvenTemporalCrossingPlaquette_mem_list
    (H : ℕ) (p : PeriodicHypercubicEvenTemporalCrossingPlaquetteLabel H) :
    p ∈ periodicHypercubicEvenTemporalCrossingPlaquetteList H := by
  classical
  simp [periodicHypercubicEvenTemporalCrossingPlaquetteList]

/-- Canonical list of Wilson energies in the temporal crossing sector. -/
noncomputable def periodicHypercubicEvenTemporalCrossingWilsonPlaquetteEnergyTerms
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : List ℝ :=
  (periodicHypercubicEvenTemporalCrossingPlaquetteList H).map fun p =>
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy A p.1)

/-- Summing the temporal crossing energy list recovers exactly the temporal
crossing Wilson action. -/
theorem periodicHypercubicEvenTemporalCrossingWilsonPlaquetteEnergyTerms_sum
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenTemporalCrossingWilsonPlaquetteEnergyTerms
      H N A).sum =
      periodicHypercubicEvenTemporalCrossingWilsonAction H N A := by
  classical
  calc
    (periodicHypercubicEvenTemporalCrossingWilsonPlaquetteEnergyTerms
      H N A).sum =
        ∑ p : PeriodicHypercubicEvenTemporalCrossingPlaquetteLabel H,
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p.1) := by
      simp [periodicHypercubicEvenTemporalCrossingWilsonPlaquetteEnergyTerms,
        periodicHypercubicEvenTemporalCrossingPlaquetteList]
    _ = ∑ p ∈ {p : PeriodicHypercubicEvenPlaquette H |
          periodicHypercubicEvenTemporalCrossingPlaquette p}.toFinset,
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p) := by
      symm
      exact Finset.sum_toFinset_eq_subtype
        periodicHypercubicEvenTemporalCrossingPlaquette
        (fun p : PeriodicHypercubicEvenPlaquette H =>
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p))
    _ = periodicHypercubicEvenTemporalCrossingWilsonAction H N A := by
      unfold periodicHypercubicEvenTemporalCrossingWilsonAction
      have hfilter :
          {p : PeriodicHypercubicEvenPlaquette H |
            periodicHypercubicEvenTemporalCrossingPlaquette p}.toFinset =
            (Finset.univ.filter fun p : PeriodicHypercubicEvenPlaquette H =>
              periodicHypercubicEvenTemporalCrossingPlaquette p) := by
        ext p
        simp
      rw [hfilter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases htemporal : periodicHypercubicEvenTemporalCrossingPlaquette p <;>
        simp [propositionIndicator, htemporal]

/-- The temporal crossing Wilson Boltzmann weight is the finite product of
one-plaquette Wilson central functions over the canonical temporal crossing
list. -/
theorem periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight_eq_plaquetteList_product
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight H N beta A =
      ((periodicHypercubicEvenTemporalCrossingPlaquetteList H).map fun p =>
        specialUnitaryWilsonBoltzmannCentralFunction N beta
          (periodicHypercubicPlaquetteHolonomy A p.1)).prod := by
  unfold periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight
  rw [← periodicHypercubicEvenTemporalCrossingWilsonPlaquetteEnergyTerms_sum
    H N A]
  rw [real_exp_neg_mul_list_sum_eq_map_exp_prod]
  simp [periodicHypercubicEvenTemporalCrossingWilsonPlaquetteEnergyTerms,
    List.map_map, specialUnitaryWilsonBoltzmannCentralFunction,
    Function.comp_def]

/-- Fintype-product form of the exact temporal crossing Wilson Boltzmann
factorization. -/
theorem periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight_eq_plaquette_product
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight H N beta A =
      ∏ p : PeriodicHypercubicEvenTemporalCrossingPlaquetteLabel H,
        specialUnitaryWilsonBoltzmannCentralFunction N beta
          (periodicHypercubicPlaquetteHolonomy A p.1) := by
  rw [periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight_eq_plaquetteList_product]
  simp [periodicHypercubicEvenTemporalCrossingPlaquetteList]

end

end MathlibAnalytic
end MGAP4D