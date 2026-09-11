import MGAP4D.MathlibAnalytic.PeriodicHypercubicL1SpatialCovariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Closed-form periodic `L¹` distance between the base vertices of two
plaquettes. -/
def periodicHypercubicPlaquetteBaseL1Distance
    (n : ℕ)
    (source target : PeriodicHypercubicPlaquette n) : ℕ :=
  periodicHypercubicVertexL1Distance n source.1 target.1

/-- Symmetry of the closed-form periodic vertex `L¹` distance. -/
theorem periodicHypercubicVertexL1Distance_symm
    (n : ℕ)
    (x y : PeriodicHypercubicVertex n) :
    periodicHypercubicVertexL1Distance n x y =
      periodicHypercubicVertexL1Distance n y x := by
  classical
  unfold periodicHypercubicVertexL1Distance
  apply Finset.sum_congr rfl
  intro i _hi
  have hneg : x i - y i = -(y i - x i) := by
    abel
  rw [hneg, ZMod.natAbs_valMinAbs_neg]

@[simp] theorem periodicHypercubicPlaquetteBaseL1Distance_self
    (n : ℕ)
    (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteBaseL1Distance n p p = 0 := by
  simp [periodicHypercubicPlaquetteBaseL1Distance]

/-- Symmetry of the plaquette-base periodic `L¹` distance. -/
theorem periodicHypercubicPlaquetteBaseL1Distance_symm
    (n : ℕ)
    (source target : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteBaseL1Distance n source target =
      periodicHypercubicPlaquetteBaseL1Distance n target source := by
  exact periodicHypercubicVertexL1Distance_symm n source.1 target.1

/-- The initial vertex of every physical boundary link lies within periodic
`L¹` distance one of the plaquette base vertex. -/
theorem periodicHypercubicPlaquetteBase_to_boundaryEdgeBaseL1Distance_le_one
    (n : ℕ) [NeZero n]
    (p : PeriodicHypercubicPlaquette n)
    (edge : PeriodicHypercubicEdge n)
    (hEdge : edge ∈ periodicHypercubicPlaquetteEdges n p) :
    periodicHypercubicVertexL1Distance n p.1 edge.1 ≤ 1 := by
  classical
  unfold periodicHypercubicPlaquetteEdges at hEdge
  rcases Finset.mem_image.mp hEdge with ⟨k, _hk, rfl⟩
  fin_cases k
  · simp [periodicHypercubicPhysicalBoundaryEdge]
  · simpa [periodicHypercubicPhysicalBoundaryEdge] using
      periodicHypercubicVertexL1Distance_shift_le_one
        n p.1 (periodicHypercubicPlaquetteFirstAxis p)
  · simpa [periodicHypercubicPhysicalBoundaryEdge] using
      periodicHypercubicVertexL1Distance_shift_le_one
        n p.1 (periodicHypercubicPlaquetteSecondAxis p)
  · simp [periodicHypercubicPhysicalBoundaryEdge]

/-- The reverse boundary-link-to-plaquette-base distance is also at most one. -/
theorem periodicHypercubicBoundaryEdgeBase_to_plaquetteBaseL1Distance_le_one
    (n : ℕ) [NeZero n]
    (p : PeriodicHypercubicPlaquette n)
    (edge : PeriodicHypercubicEdge n)
    (hEdge : edge ∈ periodicHypercubicPlaquetteEdges n p) :
    periodicHypercubicVertexL1Distance n edge.1 p.1 ≤ 1 := by
  rw [periodicHypercubicVertexL1Distance_symm]
  exact
    periodicHypercubicPlaquetteBase_to_boundaryEdgeBaseL1Distance_le_one
      n p edge hEdge

/-- The distance between two plaquette bases is bounded by the distance between
any chosen pair of boundary-link bases plus the two unit boundary margins. -/
theorem periodicHypercubicPlaquetteBaseL1Distance_le_two_add_edgeBaseL1Distance
    (n : ℕ) [NeZero n]
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (sourceEdge targetEdge : PeriodicHypercubicEdge n)
    (hSourceEdge :
      sourceEdge ∈ periodicHypercubicPlaquetteEdges n sourcePlaquette)
    (hTargetEdge :
      targetEdge ∈ periodicHypercubicPlaquetteEdges n targetPlaquette) :
    periodicHypercubicPlaquetteBaseL1Distance n
        sourcePlaquette targetPlaquette ≤
      2 + periodicHypercubicEdgeBaseL1Distance n sourceEdge targetEdge := by
  have hOuter :=
    periodicHypercubicVertexL1Distance_triangle n
      sourcePlaquette.1 sourceEdge.1 targetPlaquette.1
  have hInner :=
    periodicHypercubicVertexL1Distance_triangle n
      sourceEdge.1 targetEdge.1 targetPlaquette.1
  have hSourceRadius :=
    periodicHypercubicPlaquetteBase_to_boundaryEdgeBaseL1Distance_le_one
      n sourcePlaquette sourceEdge hSourceEdge
  have hTargetRadius :=
    periodicHypercubicBoundaryEdgeBase_to_plaquetteBaseL1Distance_le_one
      n targetPlaquette targetEdge hTargetEdge
  unfold periodicHypercubicPlaquetteBaseL1Distance
  unfold periodicHypercubicEdgeBaseL1Distance
  omega

/-- Two plaquettes are base-vertex separated at scale `d` when their periodic
base `L¹` distance is at least `2d + 2`.  The additive two pays for the two
boundary-link base offsets. -/
def periodicHypercubicPlaquetteBaseL1SeparatedAtLeast
    (n : ℕ)
    (source target : PeriodicHypercubicPlaquette n)
    (d : ℕ) : Prop :=
  2 * d + 2 ≤
    periodicHypercubicPlaquetteBaseL1Distance n source target

/-- Plaquette-base separation implies the pairwise boundary-link separation
required by the coordinate-neighbor covariance theorem. -/
theorem periodicHypercubicEdgeBaseL1SeparatedAtLeast_of_plaquetteBaseL1Separated
    (n : ℕ) [NeZero n]
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (d : ℕ)
    (hSeparated :
      periodicHypercubicPlaquetteBaseL1SeparatedAtLeast n
        sourcePlaquette targetPlaquette d) :
    periodicHypercubicEdgeBaseL1SeparatedAtLeast n
      (periodicHypercubicPlaquetteEdges n sourcePlaquette)
      (periodicHypercubicPlaquetteEdges n targetPlaquette) d := by
  intro sourceEdge hSourceEdge targetEdge hTargetEdge
  have hBridge :=
    periodicHypercubicPlaquetteBaseL1Distance_le_two_add_edgeBaseL1Distance
      n sourcePlaquette targetPlaquette sourceEdge targetEdge
      hSourceEdge hTargetEdge
  unfold periodicHypercubicPlaquetteBaseL1SeparatedAtLeast at hSeparated
  omega

/-- Canonical finite-volume periodic `Z₂` plaquette covariance decay from a
single closed-form lower bound on the two plaquette base vertices. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_of_plaquetteBaseL1Separated
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEdge n))
    (hStrict :
      FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) hEdge < 1)
    (d : ℕ)
    (hSeparated :
      periodicHypercubicPlaquetteBaseL1SeparatedAtLeast n
        sourcePlaquette targetPlaquette d) :
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
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_of_edgeBaseL1Separated
      n beta hBeta sourcePlaquette targetPlaquette hEdge hStrict d
  exact
    periodicHypercubicEdgeBaseL1SeparatedAtLeast_of_plaquetteBaseL1Separated
      n sourcePlaquette targetPlaquette d hSeparated

end

end MathlibAnalytic
end MGAP4D
