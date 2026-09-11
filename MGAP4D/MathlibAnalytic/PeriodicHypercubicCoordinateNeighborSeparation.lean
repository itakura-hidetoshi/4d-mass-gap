import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalSpatialCovariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicIncidentOtherEdgeClassification
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Explicit coordinate neighbors of a periodic physical link.  A neighbor is
one of the three non-target boundary links of one of the six canonical
coordinate plaquettes incident to the target. -/
noncomputable def periodicHypercubicCoordinateNeighbors
    (n : ℕ) [NeZero n]
    (target : PeriodicHypercubicEdge n) :
    Finset (PeriodicHypercubicEdge n) := by
  classical
  exact Finset.univ.filter fun source =>
    ∃ nu : PeriodicHypercubicOtherAxis target.2,
      ∃ otherSide : Bool,
        ∃ slot : Fin 3,
          periodicHypercubicIncidentOtherEdge
            n target nu otherSide slot = source

@[simp] theorem periodicHypercubic_mem_coordinateNeighbors_iff
    (n : ℕ) [NeZero n]
    (target source : PeriodicHypercubicEdge n) :
    source ∈ periodicHypercubicCoordinateNeighbors n target ↔
      ∃ nu : PeriodicHypercubicOtherAxis target.2,
        ∃ otherSide : Bool,
          ∃ slot : Fin 3,
            periodicHypercubicIncidentOtherEdge
              n target nu otherSide slot = source := by
  classical
  unfold periodicHypercubicCoordinateNeighbors
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every active plaquette neighbor is one of the explicitly enumerated
coordinate neighbors.  This is the local geometric bridge used below. -/
theorem periodicHypercubicActiveNeighbors_subset_coordinateNeighbors
    (n : ℕ) [NeZero n]
    (target : PeriodicHypercubicEdge n) :
    periodicHypercubicActiveNeighbors n target ⊆
      periodicHypercubicCoordinateNeighbors n target := by
  classical
  intro source hSource
  have hActive :=
    (periodicHypercubic_mem_activeNeighbors_iff
      n target source).mp hSource
  rcases hActive with ⟨⟨p, hTarget, hSourceTouch⟩, hNe⟩
  have hpMem :=
    periodicHypercubicPlaquette_mem_incidentPlaquettes_of_touches
      n p target hTarget
  unfold periodicHypercubicIncidentPlaquettes at hpMem
  rcases Finset.mem_image.mp hpMem with
    ⟨data, _hData, hpEq⟩
  rcases data with ⟨nu, otherSide⟩
  subst p
  rcases
      periodicHypercubicIncidentPlaquette_other_edge_classification
        n target source nu otherSide hSourceTouch hNe with
    ⟨slot, hSlot⟩
  exact
    (periodicHypercubic_mem_coordinateNeighbors_iff
      n target source).2
      ⟨nu, otherSide, slot, hSlot⟩

/-- One coordinate-neighbor support expansion. -/
noncomputable def periodicHypercubicCoordinateNeighborExpansion
    (n : ℕ) [NeZero n]
    (seed : Finset (PeriodicHypercubicEdge n)) :
    Finset (PeriodicHypercubicEdge n) := by
  classical
  exact seed ∪ seed.biUnion (periodicHypercubicCoordinateNeighbors n)

/-- The coordinate-neighbor ball reached from `seed` in at most `m` explicit
coordinate plaquette steps. -/
noncomputable def periodicHypercubicCoordinateNeighborBall
    (n : ℕ) [NeZero n]
    (seed : Finset (PeriodicHypercubicEdge n)) :
    ℕ → Finset (PeriodicHypercubicEdge n)
  | 0 => seed
  | m + 1 =>
      periodicHypercubicCoordinateNeighborExpansion n
        (periodicHypercubicCoordinateNeighborBall n seed m)

@[simp] theorem periodicHypercubicCoordinateNeighborBall_zero
    (n : ℕ) [NeZero n]
    (seed : Finset (PeriodicHypercubicEdge n)) :
    periodicHypercubicCoordinateNeighborBall n seed 0 = seed := rfl

@[simp] theorem periodicHypercubicCoordinateNeighborBall_succ
    (n : ℕ) [NeZero n]
    (seed : Finset (PeriodicHypercubicEdge n))
    (m : ℕ) :
    periodicHypercubicCoordinateNeighborBall n seed (m + 1) =
      periodicHypercubicCoordinateNeighborExpansion n
        (periodicHypercubicCoordinateNeighborBall n seed m) := rfl

/-- Membership in one coordinate expansion is retained membership or one
explicit coordinate-neighbor step from a retained link. -/
theorem periodicHypercubic_mem_coordinateNeighborExpansion_iff
    (n : ℕ) [NeZero n]
    (seed : Finset (PeriodicHypercubicEdge n))
    (source : PeriodicHypercubicEdge n) :
    source ∈ periodicHypercubicCoordinateNeighborExpansion n seed ↔
      source ∈ seed ∨
        ∃ target ∈ seed,
          source ∈ periodicHypercubicCoordinateNeighbors n target := by
  classical
  simp [periodicHypercubicCoordinateNeighborExpansion]

/-- One abstract active-neighbor expansion of the periodic `Z₂` Wilson system is
contained in the explicit coordinate-neighbor expansion. -/
theorem
    z2PeriodicHypercubicOrientedWilsonSystem_activeExpansion_subset_coordinateExpansion
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (seed : Finset (PeriodicHypercubicEdge n)) :
    FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighborExpansion
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) seed ⊆
      periodicHypercubicCoordinateNeighborExpansion n seed := by
  classical
  intro source hSource
  have hExpansion :=
    (finite_oriented_mem_activePlaquetteNeighborExpansion_iff
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
      seed source).mp hSource
  apply
    (periodicHypercubic_mem_coordinateNeighborExpansion_iff
      n seed source).2
  rcases hExpansion with hSeed | ⟨target, hTarget, hNeighbor⟩
  · exact Or.inl hSeed
  · apply Or.inr
    refine ⟨target, hTarget, ?_⟩
    apply
      periodicHypercubicActiveNeighbors_subset_coordinateNeighbors
        n target
    rw [← z2PeriodicHypercubicOrientedWilsonSystem_activeNeighbors_eq
      n beta hBeta target]
    exact hNeighbor

/-- Every abstract active-neighbor ball is contained in the coordinate-neighbor
ball of the same radius. -/
theorem
    z2PeriodicHypercubicOrientedWilsonSystem_activeBall_subset_coordinateBall
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (seed : Finset (PeriodicHypercubicEdge n))
    (m : ℕ) :
    FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighborBall
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) seed m ⊆
      periodicHypercubicCoordinateNeighborBall n seed m := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
      intro source hSource
      change source ∈
        FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighborExpansion
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          (FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighborBall
            (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
            seed m) at hSource
      change source ∈
        periodicHypercubicCoordinateNeighborExpansion n
          (periodicHypercubicCoordinateNeighborBall n seed m)
      have hCoordinateStep :=
        z2PeriodicHypercubicOrientedWilsonSystem_activeExpansion_subset_coordinateExpansion
          n beta hBeta
          (FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighborBall
            (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
            seed m)
          hSource
      have hCases :=
        (periodicHypercubic_mem_coordinateNeighborExpansion_iff
          n
          (FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighborBall
            (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
            seed m)
          source).mp hCoordinateStep
      apply
        (periodicHypercubic_mem_coordinateNeighborExpansion_iff
          n (periodicHypercubicCoordinateNeighborBall n seed m)
          source).2
      rcases hCases with hOld | ⟨target, hTarget, hNeighbor⟩
      · exact Or.inl (ih hOld)
      · exact Or.inr ⟨target, ih hTarget, hNeighbor⟩

/-- Two periodic link supports are coordinate-neighbor separated by at least
`d` when the right support avoids every coordinate ball of radius `m < d`
centered at the left support. -/
def periodicHypercubicCoordinateNeighborSeparatedAtLeast
    (n : ℕ) [NeZero n]
    (left right : Finset (PeriodicHypercubicEdge n))
    (d : ℕ) : Prop :=
  ∀ target : PeriodicHypercubicEdge n,
    target ∈ left →
      ∀ source : PeriodicHypercubicEdge n,
        source ∈ right →
          ∀ m : ℕ,
            m < d →
              source ∉
                periodicHypercubicCoordinateNeighborBall n {target} m

/-- Coordinate-neighbor separation implies the abstract active-neighbor
separation required by the Green covariance theorem. -/
theorem
    z2PeriodicHypercubicOrientedWilsonSystem_activeSeparated_of_coordinateSeparated
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (left right : Finset (PeriodicHypercubicEdge n))
    (d : ℕ)
    (hSeparated :
      periodicHypercubicCoordinateNeighborSeparatedAtLeast
        n left right d) :
    FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighborSeparatedAtLeast
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
      left right d := by
  intro target hTarget source hSource m hm hActive
  apply hSeparated target hTarget source hSource m hm
  exact
    z2PeriodicHypercubicOrientedWilsonSystem_activeBall_subset_coordinateBall
      n beta hBeta {target} m hActive

/-- Canonical finite-volume spatial covariance decay for two periodic `Z₂`
plaquettes under explicit coordinate-neighbor separation. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_of_coordinateSeparated
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEdge n))
    (hStrict :
      FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) hEdge < 1)
    (d : ℕ)
    (hSeparated :
      periodicHypercubicCoordinateNeighborSeparatedAtLeast n
        (periodicHypercubicPlaquetteEdges n sourcePlaquette)
        (periodicHypercubicPlaquetteEdges n targetPlaquette) d) :
    |FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          sourcePlaquette)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          targetPlaquette)| ≤
      16 *
        (FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) hEdge ^ d /
          (1 -
            FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
              (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) hEdge)) := by
  apply
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail
      n beta hBeta sourcePlaquette targetPlaquette hEdge hStrict d
  exact
    z2PeriodicHypercubicOrientedWilsonSystem_activeSeparated_of_coordinateSeparated
      n beta hBeta
      (periodicHypercubicPlaquetteEdges n sourcePlaquette)
      (periodicHypercubicPlaquetteEdges n targetPlaquette)
      d hSeparated

end

end MathlibAnalytic
end MGAP4D
