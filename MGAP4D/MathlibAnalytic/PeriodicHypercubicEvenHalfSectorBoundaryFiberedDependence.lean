import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenHalfSectorEdgeSupport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryFiberedWilsonGibbsDensityHalfTemporal

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Changing the negative-half input does not affect an assembled edge whose
side is not negative. -/
theorem FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble_eq_of_side_ne_negative
    {Edge Value : Type*} [Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (b : P.BoundaryConfiguration Value)
    (x : P.OpenHalfConfiguration Value)
    (y₁ y₂ : P.OpenHalfConfiguration Value)
    (e : Edge)
    (hne : P.side e ≠ ReflectionEdgeSide.negative) :
    P.boundaryFiberedAssemble b x y₁ e =
      P.boundaryFiberedAssemble b x y₂ e := by
  by_cases hpos : P.side e = ReflectionEdgeSide.positive
  · simp [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble, hpos]
  · by_cases hneg : P.side e = ReflectionEdgeSide.negative
    · exact (hne hneg).elim
    · simp [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
        hpos, hneg]

/-- Changing the positive-half input does not affect an assembled edge whose
side is not positive. -/
theorem FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble_eq_of_side_ne_positive
    {Edge Value : Type*} [Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (b : P.BoundaryConfiguration Value)
    (x₁ x₂ : P.OpenHalfConfiguration Value)
    (y : P.OpenHalfConfiguration Value)
    (e : Edge)
    (hne : P.side e ≠ ReflectionEdgeSide.positive) :
    P.boundaryFiberedAssemble b x₁ y e =
      P.boundaryFiberedAssemble b x₂ y e := by
  by_cases hpos : P.side e = ReflectionEdgeSide.positive
  · exact (hne hpos).elim
  · by_cases hneg : P.side e = ReflectionEdgeSide.negative
    · simp [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
        hpos, hneg]
    · simp [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
        hpos, hneg]

/-- A plaquette whose four physical boundary links are never negative has
boundary-fibered holonomy independent of the negative-half input. -/
theorem periodicHypercubicEvenPlaquetteHolonomy_boundaryFiberedAssemble_independent_y_of_side_ne_negative
    {H : ℕ} {Gauge : Type} [Group Gauge]
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Gauge)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge)
    (y₁ y₂ : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hside : ∀ k : Fin 4,
      (periodicHypercubicEvenEdgeOrbitPartition H).side
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge ≠
        ReflectionEdgeSide.negative) :
    periodicHypercubicPlaquetteHolonomy
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₁) p =
      periodicHypercubicPlaquetteHolonomy
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₂) p := by
  have hvalue (k : Fin 4) :
      (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₁
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge =
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₂
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge :=
    (periodicHypercubicEvenEdgeOrbitPartition H).
      boundaryFiberedAssemble_eq_of_side_ne_negative
        b x y₁ y₂ _ (hside k)
  have hstep (k : Fin 4) :
      periodicHypercubicStepValue
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x y₁)
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k) =
        periodicHypercubicStepValue
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x y₂)
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k) := by
    cases horientation :
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p k).orientation <;>
      simp [periodicHypercubicStepValue, horientation, hvalue k]
  unfold periodicHypercubicPlaquetteHolonomy
  rw [hstep 0, hstep 1, hstep 2, hstep 3]

/-- A plaquette whose four physical boundary links are never positive has
boundary-fibered holonomy independent of the positive-half input. -/
theorem periodicHypercubicEvenPlaquetteHolonomy_boundaryFiberedAssemble_independent_x_of_side_ne_positive
    {H : ℕ} {Gauge : Type} [Group Gauge]
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Gauge)
    (x₁ x₂ : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge)
    (y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hside : ∀ k : Fin 4,
      (periodicHypercubicEvenEdgeOrbitPartition H).side
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge ≠
        ReflectionEdgeSide.positive) :
    periodicHypercubicPlaquetteHolonomy
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x₁ y) p =
      periodicHypercubicPlaquetteHolonomy
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x₂ y) p := by
  have hvalue (k : Fin 4) :
      (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x₁ y
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge =
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x₂ y
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge :=
    (periodicHypercubicEvenEdgeOrbitPartition H).
      boundaryFiberedAssemble_eq_of_side_ne_positive
        b x₁ x₂ y _ (hside k)
  have hstep (k : Fin 4) :
      periodicHypercubicStepValue
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x₁ y)
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k) =
        periodicHypercubicStepValue
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x₂ y)
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k) := by
    cases horientation :
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p k).orientation <;>
      simp [periodicHypercubicStepValue, horientation, hvalue k]
  unfold periodicHypercubicPlaquetteHolonomy
  rw [hstep 0, hstep 1, hstep 2, hstep 3]

/-- The strict-positive Wilson action in boundary-fibered coordinates is
independent of the negative-half input. -/
theorem periodicHypercubicEvenPositiveWilsonAction_boundaryFiberedAssemble_independent_y
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y₁ y₂ : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPositiveWilsonAction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₁) =
      periodicHypercubicEvenPositiveWilsonAction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₂) := by
  classical
  unfold periodicHypercubicEvenPositiveWilsonAction
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hpositive : periodicHypercubicEvenStrictPositivePlaquette p
  · have hholonomy :=
      periodicHypercubicEvenPlaquetteHolonomy_boundaryFiberedAssemble_independent_y_of_side_ne_negative
        b x y₁ y₂ p (fun k => by
          rw [periodicHypercubicEvenStrictPositivePlaquette_boundaryStep_side_positive
            p hpositive k]
          decide)
    rw [hholonomy]
  · simp [propositionIndicator, hpositive]

/-- The positive-boundary temporal action is independent of the negative-half
input. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_boundaryFiberedAssemble_independent_y
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y₁ y₂ : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₁) =
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₂) := by
  classical
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hpositive :
      periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p
  · have hholonomy :=
      periodicHypercubicEvenPlaquetteHolonomy_boundaryFiberedAssemble_independent_y_of_side_ne_negative
        b x y₁ y₂ p
        (periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_boundaryStep_side_ne_negative
          p hpositive)
    rw [hholonomy]
  · simp [propositionIndicator, hpositive]

/-- The strict-negative Wilson action in boundary-fibered coordinates is
independent of the positive-half input. -/
theorem periodicHypercubicEvenNegativeWilsonAction_boundaryFiberedAssemble_independent_x
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x₁ x₂ y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenNegativeWilsonAction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x₁ y) =
      periodicHypercubicEvenNegativeWilsonAction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x₂ y) := by
  classical
  unfold periodicHypercubicEvenNegativeWilsonAction
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hnegative : periodicHypercubicEvenStrictNegativePlaquette p
  · have hholonomy :=
      periodicHypercubicEvenPlaquetteHolonomy_boundaryFiberedAssemble_independent_x_of_side_ne_positive
        b x₁ x₂ y p (fun k => by
          rw [periodicHypercubicEvenStrictNegativePlaquette_boundaryStep_side_negative
            p hnegative k]
          decide)
    rw [hholonomy]
  · simp [propositionIndicator, hnegative]

/-- The negative-boundary temporal action is independent of the positive-half
input. -/
theorem periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction_boundaryFiberedAssemble_independent_x
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x₁ x₂ y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x₁ y) =
      periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x₂ y) := by
  classical
  unfold periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hnegative :
      periodicHypercubicEvenNegativeBoundaryTemporalPlaquette p
  · have hholonomy :=
      periodicHypercubicEvenPlaquetteHolonomy_boundaryFiberedAssemble_independent_x_of_side_ne_positive
        b x₁ x₂ y p
        (periodicHypercubicEvenNegativeBoundaryTemporalPlaquette_boundaryStep_side_ne_positive
          p hnegative)
    rw [hholonomy]
  · simp [propositionIndicator, hnegative]

/-- The completed positive Wilson amplitude depends only on the shared boundary
and positive-half coordinates. -/
theorem periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_boundaryFiberedAssemble_independent_y
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y₁ y₂ : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₁) =
      periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₂) := by
  unfold periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
  rw [periodicHypercubicEvenPositiveWilsonAction_boundaryFiberedAssemble_independent_y
    H N b x y₁ y₂]
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_boundaryFiberedAssemble_independent_y
    H N b x y₁ y₂]

/-- The completed negative Wilson amplitude depends only on the shared boundary
and negative-half coordinates. -/
theorem periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude_boundaryFiberedAssemble_independent_x
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x₁ x₂ y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x₁ y) =
      periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x₂ y) := by
  unfold periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenNegativeBoundaryTemporalWilsonBoltzmannWeight
  rw [periodicHypercubicEvenNegativeWilsonAction_boundaryFiberedAssemble_independent_x
    H N b x₁ x₂ y]
  rw [periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction_boundaryFiberedAssemble_independent_x
    H N b x₁ x₂ y]

end

end MathlibAnalytic
end MGAP4D
