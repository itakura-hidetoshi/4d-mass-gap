import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingHalfSectors
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The literal finite set of all positive-boundary temporal plaquettes. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes
    (H : ℕ) : Finset (PeriodicHypercubicEvenPlaquette H) :=
  (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)).filter
    periodicHypercubicEvenPositiveBoundaryTemporalPlaquette

@[simp]
theorem periodicHypercubicEven_mem_positiveBoundaryTemporalPlaquettes
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H ↔
      periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p := by
  simp [periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes]

/-- The four canonical temporal companions form an embedded four-element block
inside the actual positive-boundary temporal plaquette set. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionEmbedding
    (H : ℕ) : Fin 4 ↪ PeriodicHypercubicEvenPlaquette H where
  toFun := periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H
  inj' := by
    intro i j hij
    apply periodicHypercubicEvenPrimarySpatialPlaquetteEdge_injective H
    apply Prod.ext
    · exact congrArg Prod.fst hij
    · have haxis := congrArg periodicHypercubicPlaquetteSecondAxis hij
      simpa using haxis

/-- The literal selected four-companion plaquette set. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet
    (H : ℕ) : Finset (PeriodicHypercubicEvenPlaquette H) :=
  Finset.univ.map
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionEmbedding H)

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet_card
    (H : ℕ) :
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H).card = 4 := by
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet]

@[simp]
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_mem_set
    (H : ℕ) (k : Fin 4) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k ∈
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H := by
  classical
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionEmbedding]

/-- The selected four-companion block is genuinely contained in the full
positive-boundary temporal sector. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet_subset_positiveBoundary
    (H : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H ⊆
      periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H := by
  classical
  intro p hp
  rw [periodicHypercubicEven_mem_positiveBoundaryTemporalPlaquettes]
  rcases Finset.mem_map.mp hp with ⟨k, _hk, rfl⟩
  exact periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_positiveBoundary H k

/-- The unselected positive-boundary temporal plaquettes, as a literal Finset
complement of the four canonical companions. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes
    (H : ℕ) : Finset (PeriodicHypercubicEvenPlaquette H) :=
  periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H \
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H

/-- The positive-boundary temporal Wilson action is the literal finite sum over
its positive-boundary temporal plaquettes; proposition indicators disappear. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_eq_sum
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A =
      ∑ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A p) := by
  classical
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction
  unfold periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hpositive : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p
  · simp [propositionIndicator, hpositive]
  · simp [propositionIndicator, hpositive]

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

/-- Literal one-plaquette Wilson factor on a positive-boundary temporal
plaquette. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H) : ℝ :=
  Real.exp
    (-beta * specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy A p))

/-- The complete positive-boundary temporal Boltzmann weight is exactly the
finite product of its literal one-plaquette Wilson factors. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_eq_prod
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight H N beta A =
      ∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor
          H N beta A p := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_eq_sum]
  exact real_exp_neg_mul_finset_sum_eq_prod
    (periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H) beta
    (fun p => specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy A p))

/-- Every literal positive-boundary temporal plaquette factor is the standard
one-plaquette Wilson central function. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor_eq_centralFunction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor H N beta A p =
      specialUnitaryWilsonBoltzmannCentralFunction N beta
        (periodicHypercubicPlaquetteHolonomy A p) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
