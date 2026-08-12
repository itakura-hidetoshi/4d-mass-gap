import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonCompletedPositiveFactor
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonProduct
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelRKHSFeature
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private theorem positiveBoundaryTemporalWilsonResidualProductTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

/-- The selected four-companion Wilson action is exactly the finite sum over
its embedded four-element plaquette block. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonAction_eq_sum
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonAction H A =
      ∑ p ∈ periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H,
        specialUnitaryWilsonPlaquetteEnergy 2
          (periodicHypercubicPlaquetteHolonomy A p) := by
  classical
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionEmbedding,
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonAction]
  ring

/-- The formerly algebraic positive-boundary residual action is the literal
sum over every positive-boundary temporal plaquette except the four selected
companions.  No residual interaction is discarded. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualAction_eq_sum_residualPlaquettes
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualAction H A =
      ∑ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H,
        specialUnitaryWilsonPlaquetteEnergy 2
          (periodicHypercubicPlaquetteHolonomy A p) := by
  classical
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualAction
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_eq_sum]
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonAction_eq_sum]
  exact
    (Finset.sum_sdiff_eq_sub
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet_subset_positiveBoundary H)
      (f := fun p =>
        specialUnitaryWilsonPlaquetteEnergy 2
          (periodicHypercubicPlaquetteHolonomy A p))).symm

private theorem real_exp_neg_mul_finset_sum_eq_prod_residual
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

/-- The residual Boltzmann weight is a literal product over all unselected
positive-boundary temporal plaquettes. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight_eq_prod_residualPlaquettes
    (H : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight H beta A =
      ∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H,
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor
          H 2 beta A p := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualAction_eq_sum_residualPlaquettes]
  exact real_exp_neg_mul_finset_sum_eq_prod_residual
    (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H) beta
    (fun p => specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicPlaquetteHolonomy A p))

/-- The four selected-companion weight is exactly the product over the embedded
four-element companion Finset. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight_eq_prod_selectedPlaquettes
    (H : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight H beta A =
      ∏ p ∈ periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H,
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor
          H 2 beta A p := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonAction_eq_sum]
  exact real_exp_neg_mul_finset_sum_eq_prod_residual
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H) beta
    (fun p => specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicPlaquetteHolonomy A p))

/-- The full positive-boundary temporal weight is the product of the literal
residual block and literal selected four-companion block. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_eq_residualProduct_mul_selectedProduct
    (H : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight H 2 beta A =
      (∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H,
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor
          H 2 beta A p) *
      (∏ p ∈ periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionSet H,
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor
          H 2 beta A p) := by
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_eq_residual_mul_fourCompanion]
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight_eq_prod_residualPlaquettes]
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonWeight_eq_prod_selectedPlaquettes]

/-- In boundary-fibered coordinates, every literal positive-boundary temporal
Wilson plaquette factor is exactly the corresponding relative Wilson kernel
between its shared-boundary leg and its positive-half open path. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor_boundaryFibered_eq_relativeKernel
    {H N : ℕ}
    (hH : 0 < H)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) p =
      specialUnitaryWilsonRelativeKernel N beta
        (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
        (periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x p) := by
  have hpositive : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p :=
    (periodicHypercubicEven_mem_positiveBoundaryTemporalPlaquettes p).1 hp
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor_eq_centralFunction]
  rw [specialUnitaryWilsonBoltzmannCentralFunction_eq_trace]
  rw [specialUnitaryWilsonRelativeKernel_eq_trace]
  rw [periodicHypercubicEvenPositiveBoundaryTemporal_normalizedTrace_boundaryFibered_eq_relativeKernel
    hH b x y p hpositive]
  rfl

/-- The full positive-boundary temporal Wilson factor in boundary/open-half
coordinates is an exact finite product of relative Wilson kernels.  The
negative-half coordinate disappears from every factor. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_boundaryFibered_eq_relativeKernelProduct
    {H N : ℕ}
    (hH : 0 < H)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) =
      ∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H,
        specialUnitaryWilsonRelativeKernel N beta
          (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
          (periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x p) := by
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_eq_prod]
  apply Finset.prod_congr rfl
  intro p hp
  exact periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor_boundaryFibered_eq_relativeKernel
    hH beta b x y p hp

/-- The residual positive-boundary temporal factor has the same exact relative
kernel product description, but only over the literal unselected complement. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight_boundaryFibered_eq_relativeKernelProduct
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight H beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) =
      ∏ p ∈ periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H,
        specialUnitaryWilsonRelativeKernel 2 beta
          (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
          (periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x p) := by
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualWeight_eq_prod_residualPlaquettes]
  apply Finset.prod_congr rfl
  intro p hp
  have hfull : p ∈ periodicHypercubicEvenPositiveBoundaryTemporalPlaquettes H := by
    exact Finset.mem_of_mem_sdiff hp
  exact periodicHypercubicEvenPositiveBoundaryTemporalWilsonPlaquetteFactor_boundaryFibered_eq_relativeKernel
    hH beta b x y p hfull

end

end MathlibAnalytic
end MGAP4D
