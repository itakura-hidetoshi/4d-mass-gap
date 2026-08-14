import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenHalfSectorBoundaryFiberedDependence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On a positive-side edge, the boundary-fibered assembly depends only on the
positive open-half coordinate.  In particular it is independent of both the
shared boundary coordinate and the negative open-half coordinate. -/
theorem FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble_eq_of_side_positive
    {Edge : Type} {Value : Type*} [Fintype Edge]
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (b₁ b₂ : P.BoundaryConfiguration Value)
    (x : P.OpenHalfConfiguration Value)
    (y₁ y₂ : P.OpenHalfConfiguration Value)
    (e : Edge)
    (hpos : P.side e = ReflectionEdgeSide.positive) :
    P.boundaryFiberedAssemble b₁ x y₁ e =
      P.boundaryFiberedAssemble b₂ x y₂ e := by
  simp [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble, hpos]

/-- A plaquette all of whose physical links lie on the positive side has the
same boundary-fibered holonomy for every shared-boundary and negative-half
coordinate, once its positive open-half coordinate is fixed. -/
theorem periodicHypercubicEvenPlaquetteHolonomy_boundaryFiberedAssemble_independent_boundary_y_of_side_positive
    {H : ℕ} {Gauge : Type} [Group Gauge]
    (b₁ b₂ : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Gauge)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge)
    (y₁ y₂ : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hside : ∀ k : Fin 4,
      (periodicHypercubicEvenEdgeOrbitPartition H).side
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge =
        ReflectionEdgeSide.positive) :
    periodicHypercubicPlaquetteHolonomy
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b₁ x y₁) p =
      periodicHypercubicPlaquetteHolonomy
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b₂ x y₂) p := by
  have hvalue (k : Fin 4) :
      (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b₁ x y₁
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge =
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b₂ x y₂
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge :=
    FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble_eq_of_side_positive
      (periodicHypercubicEvenEdgeOrbitPartition H)
      b₁ b₂ x y₁ y₂ _ (hside k)
  have hstep (k : Fin 4) :
      periodicHypercubicStepValue
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b₁ x y₁)
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k) =
        periodicHypercubicStepValue
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b₂ x y₂)
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k) := by
    cases horientation :
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p k).orientation <;>
      simp [periodicHypercubicStepValue, horientation, hvalue k]
  unfold periodicHypercubicPlaquetteHolonomy
  rw [hstep 0, hstep 1, hstep 2, hstep 3]

/-- The strict-positive Wilson action in boundary-fibered coordinates depends
only on the positive open-half coordinate. -/
theorem periodicHypercubicEvenPositiveWilsonAction_boundaryFiberedAssemble_independent_boundary_y
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b₁ b₂ : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (y₁ y₂ : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPositiveWilsonAction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b₁ x y₁) =
      periodicHypercubicEvenPositiveWilsonAction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b₂ x y₂) := by
  classical
  unfold periodicHypercubicEvenPositiveWilsonAction
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hpositive : periodicHypercubicEvenStrictPositivePlaquette p
  · have hholonomy :=
      periodicHypercubicEvenPlaquetteHolonomy_boundaryFiberedAssemble_independent_boundary_y_of_side_positive
        b₁ b₂ x y₁ y₂ p (fun k =>
          periodicHypercubicEvenStrictPositivePlaquette_boundaryStep_side_positive
            p hpositive k)
    rw [hholonomy]
  · simp [propositionIndicator, hpositive]

/-- Consequently the strict-positive Wilson Boltzmann amplitude is a function
of the positive open-half coordinate alone. -/
theorem periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude_boundaryFiberedAssemble_independent_boundary_y
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b₁ b₂ : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (y₁ y₂ : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b₁ x y₁) =
      periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b₂ x y₂) := by
  unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
  rw [periodicHypercubicEvenPositiveWilsonAction_boundaryFiberedAssemble_independent_boundary_y
    H N b₁ b₂ x y₁ y₂]

end

end MathlibAnalytic
end MGAP4D
