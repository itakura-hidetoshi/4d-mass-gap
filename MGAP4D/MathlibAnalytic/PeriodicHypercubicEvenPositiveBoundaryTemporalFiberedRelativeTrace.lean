import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalRelativeTraceFactorization
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedCoordinates

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

private theorem periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg_boundaryFibered_independent
    {H N : ℕ}
    (hH : 0 < H)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x₁ y₁ x₂ y₂ :
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x₁ y₁) p =
      periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x₂ y₂) p := by
  have hpattern :=
    periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_exact_edge_pattern
      hH p hp
  unfold periodicHypercubicEvenPositiveBoundaryTemporalExactEdgePattern at hpattern
  rcases hpattern with hprimary | hantipodal
  · unfold periodicHypercubicEvenPositiveBoundaryTemporalPrimaryEdgePattern at hprimary
    let s := periodicHypercubicBoundaryStep
      (PeriodicHypercubicEvenSideLength H) p (3 : Fin 4)
    have hvalue :
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x₁ y₁ s.edge =
          (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x₂ y₂ s.edge := by
      rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
        b x₁ y₁ ⟨s.edge, hprimary.2.2.2.2⟩]
      rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
        b x₂ y₂ ⟨s.edge, hprimary.2.2.2.2⟩]
    have hstep :
        periodicHypercubicStepValue
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x₁ y₁) s =
          periodicHypercubicStepValue
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x₂ y₂) s := by
      cases horientation : s.orientation <;>
        simp [periodicHypercubicStepValue, horientation, hvalue]
    simp [periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg,
      hprimary.1, s, hstep]
  · unfold periodicHypercubicEvenPositiveBoundaryTemporalAntipodalEdgePattern at hantipodal
    have hbaseNe : (p.1 0).val ≠ 0 := by omega
    let s := periodicHypercubicBoundaryStep
      (PeriodicHypercubicEvenSideLength H) p (1 : Fin 4)
    have hvalue :
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x₁ y₁ s.edge =
          (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x₂ y₂ s.edge := by
      rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
        b x₁ y₁ ⟨s.edge, hantipodal.2.2.1⟩]
      rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
        b x₂ y₂ ⟨s.edge, hantipodal.2.2.1⟩]
    have hstep :
        periodicHypercubicStepValue
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x₁ y₁) s =
          periodicHypercubicStepValue
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x₂ y₂) s := by
      cases horientation : s.orientation <;>
        simp [periodicHypercubicStepValue, horientation, hvalue]
    simp [periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg,
      hbaseNe, s, hstep]

private theorem periodicHypercubicEvenPositiveBoundaryTemporalOpenPath_boundaryFibered_independent
    {H N : ℕ}
    (hH : 0 < H)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (b₁ b₂ : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (y₁ y₂ : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPositiveBoundaryTemporalOpenPath
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b₁ x y₁) p =
      periodicHypercubicEvenPositiveBoundaryTemporalOpenPath
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b₂ x y₂) p := by
  have hpattern :=
    periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_exact_edge_pattern
      hH p hp
  unfold periodicHypercubicEvenPositiveBoundaryTemporalExactEdgePattern at hpattern
  have hstep (k : Fin 4)
      (hk : (periodicHypercubicEvenEdgeOrbitPartition H).side
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k).edge =
        ReflectionEdgeSide.positive) :
      periodicHypercubicStepValue
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b₁ x y₁)
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k) =
        periodicHypercubicStepValue
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b₂ x y₂)
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p k) := by
    let s := periodicHypercubicBoundaryStep
      (PeriodicHypercubicEvenSideLength H) p k
    have hvalue :
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b₁ x y₁ s.edge =
          (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b₂ x y₂ s.edge := by
      rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_positive
        b₁ x y₁ ⟨s.edge, hk⟩]
      rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_positive
        b₂ x y₂ ⟨s.edge, hk⟩]
    cases horientation : s.orientation <;>
      simp [periodicHypercubicStepValue, horientation, hvalue, s]
  rcases hpattern with hprimary | hantipodal
  · unfold periodicHypercubicEvenPositiveBoundaryTemporalPrimaryEdgePattern at hprimary
    have h0 := hstep 0 hprimary.2.1
    have h1 := hstep 1 hprimary.2.2.1
    have h2 := hstep 2 hprimary.2.2.2.1
    simp [periodicHypercubicEvenPositiveBoundaryTemporalOpenPath,
      hprimary.1, h0, h1, h2]
  · unfold periodicHypercubicEvenPositiveBoundaryTemporalAntipodalEdgePattern at hantipodal
    have hbaseNe : (p.1 0).val ≠ 0 := by omega
    have h0 := hstep 0 hantipodal.2.1
    have h2 := hstep 2 hantipodal.2.2.2.1
    have h3 := hstep 3 hantipodal.2.2.2.2
    simp [periodicHypercubicEvenPositiveBoundaryTemporalOpenPath,
      hbaseNe, h0, h2, h3]

/-- Canonical shared-boundary leg of a positive-boundary temporal plaquette.
Dummy open-half coordinates are set to the group identity; the independence
theorem above shows that this loses no information. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg
    {H N : ℕ}
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (p : PeriodicHypercubicEvenPlaquette H) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
      b (fun _ => 1) (fun _ => 1)) p

/-- Canonical positive-half three-edge path of a positive-boundary temporal
plaquette.  Dummy shared-boundary and negative-half coordinates are set to the
group identity. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath
    {H N : ℕ}
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (p : PeriodicHypercubicEvenPlaquette H) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  periodicHypercubicEvenPositiveBoundaryTemporalOpenPath
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
      (fun _ => 1) x (fun _ => 1)) p

/-- On actual boundary-fibered coordinates, the selected boundary leg is
exactly the canonical function of the shared-boundary coordinate alone. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg_boundaryFibered_eq
    {H N : ℕ}
    (hH : 0 < H)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) :
    periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) p =
      periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p := by
  exact periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg_boundaryFibered_independent
    hH p hp b x y (fun _ => 1) (fun _ => 1)

/-- On actual boundary-fibered coordinates, the cyclic three-edge open path is
exactly the canonical function of the positive-half coordinate alone. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalOpenPath_boundaryFibered_eq
    {H N : ℕ}
    (hH : 0 < H)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) :
    periodicHypercubicEvenPositiveBoundaryTemporalOpenPath
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) p =
      periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x p := by
  exact periodicHypercubicEvenPositiveBoundaryTemporalOpenPath_boundaryFibered_independent
    hH p hp x b (fun _ => 1) y (fun _ => 1)

/-- Exact boundary/open-half factorization of one positive-boundary temporal
plaquette normalized trace in boundary-fibered coordinates.

The negative-half coordinate disappears completely:
`tr_norm U_p(b,x,y) = K(g_boundary(b), h_open(x))`. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporal_normalizedTrace_boundaryFibered_eq_relativeKernel
    {H N : ℕ}
    (hH : 0 < H)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) :
    normalizedSpecialUnitaryRealTrace N
        (periodicHypercubicPlaquetteHolonomy
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) p) =
      specialUnitaryNormalizedTraceRelativeKernel N
        (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p)
        (periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x p) := by
  rw [periodicHypercubicEvenPositiveBoundaryTemporal_normalizedTrace_eq_relativeKernel
    hH _ p hp]
  rw [periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg_boundaryFibered_eq
    hH b x y p hp]
  rw [periodicHypercubicEvenPositiveBoundaryTemporalOpenPath_boundaryFibered_eq
    hH b x y p hp]

/-- The positive-boundary temporal normalized trace is independent of the
negative-half coordinate once shared boundary and positive half are fixed. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporal_normalizedTrace_boundaryFibered_independent_negative
    {H N : ℕ}
    (hH : 0 < H)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x y₁ y₂ : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) :
    normalizedSpecialUnitaryRealTrace N
        (periodicHypercubicPlaquetteHolonomy
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y₁) p) =
      normalizedSpecialUnitaryRealTrace N
        (periodicHypercubicPlaquetteHolonomy
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y₂) p) := by
  rw [periodicHypercubicEvenPositiveBoundaryTemporal_normalizedTrace_boundaryFibered_eq_relativeKernel
    hH b x y₁ p hp]
  rw [periodicHypercubicEvenPositiveBoundaryTemporal_normalizedTrace_boundaryFibered_eq_relativeKernel
    hH b x y₂ p hp]

end

end MathlibAnalytic
end MGAP4D
