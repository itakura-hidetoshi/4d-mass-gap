import MGAP4D.MathlibAnalytic.PeriodicHypercubicCoordinateNeighborSeparation
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Closed-form periodic `L¹` distance between two vertices.  Each coordinate
uses the shortest integer representative of its difference modulo `n`. -/
def periodicHypercubicVertexL1Distance
    (n : ℕ)
    (x y : PeriodicHypercubicVertex n) : ℕ :=
  ∑ i : PeriodicHypercubicAxis,
    (y i - x i).valMinAbs.natAbs

/-- Periodic `L¹` distance between the initial vertices of two physical links. -/
def periodicHypercubicEdgeBaseL1Distance
    (n : ℕ)
    (target source : PeriodicHypercubicEdge n) : ℕ :=
  periodicHypercubicVertexL1Distance n target.1 source.1

@[simp] theorem periodicHypercubicVertexL1Distance_self
    (n : ℕ)
    (x : PeriodicHypercubicVertex n) :
    periodicHypercubicVertexL1Distance n x x = 0 := by
  simp [periodicHypercubicVertexL1Distance]

@[simp] theorem periodicHypercubicEdgeBaseL1Distance_self
    (n : ℕ)
    (target : PeriodicHypercubicEdge n) :
    periodicHypercubicEdgeBaseL1Distance n target target = 0 := by
  simp [periodicHypercubicEdgeBaseL1Distance]

/-- The shortest periodic representative of one positive unit has absolute
value at most one, including the degenerate side-length-one case. -/
theorem zmod_natAbs_valMinAbs_one_le_one
    (n : ℕ) [NeZero n] :
    ((1 : ZMod n).valMinAbs.natAbs) ≤ 1 := by
  rw [ZMod.valMinAbs_natAbs_eq_min]
  calc
    min (ZMod.val (1 : ZMod n)) (n - ZMod.val (1 : ZMod n)) ≤
        ZMod.val (1 : ZMod n) := min_le_left _ _
    _ = 1 % n := ZMod.val_one_eq_one_mod n
    _ ≤ 1 := Nat.mod_le 1 n

/-- A positive unit coordinate translation changes periodic vertex `L¹`
distance from the original vertex by at most one. -/
theorem periodicHypercubicVertexL1Distance_shift_le_one
    (n : ℕ) [NeZero n]
    (x : PeriodicHypercubicVertex n)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicVertexL1Distance n x
      (periodicHypercubicShift n x mu) ≤ 1 := by
  classical
  unfold periodicHypercubicVertexL1Distance
  unfold periodicHypercubicShift periodicHypercubicUnit
  simp only [Pi.add_apply, add_sub_cancel_left]
  calc
    (∑ i : PeriodicHypercubicAxis,
      ((if i = mu then 1 else 0 : ZMod n).valMinAbs.natAbs)) =
        ((1 : ZMod n).valMinAbs.natAbs) := by
          rw [Finset.sum_eq_single mu]
          · simp
          · intro i _hi hne
            simp [hne]
          · simp
    _ ≤ 1 := zmod_natAbs_valMinAbs_one_le_one n

/-- A negative unit coordinate translation changes periodic vertex `L¹`
distance from the original vertex by at most one. -/
theorem periodicHypercubicVertexL1Distance_unshift_le_one
    (n : ℕ) [NeZero n]
    (x : PeriodicHypercubicVertex n)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicVertexL1Distance n x
      (periodicHypercubicUnshift n x mu) ≤ 1 := by
  classical
  unfold periodicHypercubicVertexL1Distance
  unfold periodicHypercubicUnshift periodicHypercubicUnit
  simp only [Pi.sub_apply, sub_sub_cancel_left]
  calc
    (∑ i : PeriodicHypercubicAxis,
      ((-(if i = mu then 1 else 0 : ZMod n)).valMinAbs.natAbs)) =
        ((-(1 : ZMod n)).valMinAbs.natAbs) := by
          rw [Finset.sum_eq_single mu]
          · simp
          · intro i _hi hne
            simp [hne]
          · simp
    _ = ((1 : ZMod n).valMinAbs.natAbs) :=
      ZMod.natAbs_valMinAbs_neg (1 : ZMod n)
    _ ≤ 1 := zmod_natAbs_valMinAbs_one_le_one n

/-- Triangle inequality for the closed-form periodic vertex `L¹` distance. -/
theorem periodicHypercubicVertexL1Distance_triangle
    (n : ℕ)
    (x y z : PeriodicHypercubicVertex n) :
    periodicHypercubicVertexL1Distance n x z ≤
      periodicHypercubicVertexL1Distance n x y +
        periodicHypercubicVertexL1Distance n y z := by
  classical
  unfold periodicHypercubicVertexL1Distance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _hi
  have hDecomp :
      z i - x i = (y i - x i) + (z i - y i) := by
    abel
  rw [hDecomp]
  exact le_trans
    (ZMod.natAbs_valMinAbs_add_le (y i - x i) (z i - y i))
    (Int.natAbs_add_le _ _)

/-- Triangle inequality for link-base periodic `L¹` distance. -/
theorem periodicHypercubicEdgeBaseL1Distance_triangle
    (n : ℕ)
    (a b c : PeriodicHypercubicEdge n) :
    periodicHypercubicEdgeBaseL1Distance n a c ≤
      periodicHypercubicEdgeBaseL1Distance n a b +
        periodicHypercubicEdgeBaseL1Distance n b c := by
  exact periodicHypercubicVertexL1Distance_triangle n a.1 b.1 c.1

/-- Every explicit coordinate neighbor changes the link-base periodic `L¹`
distance by at most two.  The only two-step case is the transverse edge on the
opposite side of an incident plaquette. -/
theorem periodicHypercubicEdgeBaseL1Distance_le_two_of_coordinateNeighbor
    (n : ℕ) [NeZero n]
    (target source : PeriodicHypercubicEdge n)
    (hNeighbor :
      source ∈ periodicHypercubicCoordinateNeighbors n target) :
    periodicHypercubicEdgeBaseL1Distance n target source ≤ 2 := by
  rcases
      (periodicHypercubic_mem_coordinateNeighbors_iff
        n target source).mp hNeighbor with
    ⟨nu, otherSide, slot, hSlot⟩
  rw [← hSlot]
  rcases target with ⟨x, mu⟩
  rcases nu with ⟨nu, hnu⟩
  cases otherSide
  · fin_cases slot
    · simp [periodicHypercubicEdgeBaseL1Distance,
        periodicHypercubicIncidentOtherEdge]
    · exact le_trans
        (periodicHypercubicVertexL1Distance_shift_le_one n x mu)
        (by omega)
    · exact le_trans
        (periodicHypercubicVertexL1Distance_shift_le_one n x nu)
        (by omega)
  · fin_cases slot
    · exact le_trans
        (periodicHypercubicVertexL1Distance_unshift_le_one n x nu)
        (by omega)
    · have hTriangle :=
        periodicHypercubicVertexL1Distance_triangle n x
          (periodicHypercubicUnshift n x nu)
          (periodicHypercubicShift n
            (periodicHypercubicUnshift n x nu) mu)
      have hFirst :=
        periodicHypercubicVertexL1Distance_unshift_le_one n x nu
      have hSecond :=
        periodicHypercubicVertexL1Distance_shift_le_one n
          (periodicHypercubicUnshift n x nu) mu
      change periodicHypercubicVertexL1Distance n x
        (periodicHypercubicShift n
          (periodicHypercubicUnshift n x nu) mu) ≤ 2
      omega
    · exact le_trans
        (periodicHypercubicVertexL1Distance_unshift_le_one n x nu)
        (by omega)

/-- Membership in a coordinate-neighbor ball of radius `m` forces the
closed-form link-base periodic `L¹` distance to be at most `2m`. -/
theorem periodicHypercubicEdgeBaseL1Distance_le_two_mul_of_mem_coordinateBall
    (n : ℕ) [NeZero n]
    (center source : PeriodicHypercubicEdge n)
    (m : ℕ)
    (hMem :
      source ∈ periodicHypercubicCoordinateNeighborBall n {center} m) :
    periodicHypercubicEdgeBaseL1Distance n center source ≤ 2 * m := by
  induction m generalizing source with
  | zero =>
      simp at hMem
      subst source
      simp
  | succ m ih =>
      rw [periodicHypercubicCoordinateNeighborBall_succ] at hMem
      have hCases :=
        (periodicHypercubic_mem_coordinateNeighborExpansion_iff
          n (periodicHypercubicCoordinateNeighborBall n {center} m)
          source).mp hMem
      rcases hCases with hOld | ⟨middle, hMiddle, hNeighbor⟩
      · have hBound := ih source hOld
        omega
      · have hCenterMiddle := ih middle hMiddle
        have hMiddleSource :=
          periodicHypercubicEdgeBaseL1Distance_le_two_of_coordinateNeighbor
            n middle source hNeighbor
        have hTriangle :=
          periodicHypercubicEdgeBaseL1Distance_triangle
            n center middle source
        omega

/-- Closed-form support separation at scale `d`: every left-right pair of
boundary links has periodic base-vertex `L¹` distance at least `2d`. -/
def periodicHypercubicEdgeBaseL1SeparatedAtLeast
    (n : ℕ)
    (left right : Finset (PeriodicHypercubicEdge n))
    (d : ℕ) : Prop :=
  ∀ target : PeriodicHypercubicEdge n,
    target ∈ left →
      ∀ source : PeriodicHypercubicEdge n,
        source ∈ right →
          2 * d ≤ periodicHypercubicEdgeBaseL1Distance n target source

/-- A closed-form periodic `L¹` lower bound implies coordinate-neighbor graph
separation at the same scale. -/
theorem periodicHypercubicCoordinateNeighborSeparatedAtLeast_of_edgeBaseL1Separated
    (n : ℕ) [NeZero n]
    (left right : Finset (PeriodicHypercubicEdge n))
    (d : ℕ)
    (hSeparated :
      periodicHypercubicEdgeBaseL1SeparatedAtLeast n left right d) :
    periodicHypercubicCoordinateNeighborSeparatedAtLeast n left right d := by
  intro target hTarget source hSource m hm hMem
  have hUpper :=
    periodicHypercubicEdgeBaseL1Distance_le_two_mul_of_mem_coordinateBall
      n target source m hMem
  have hLower := hSeparated target hTarget source hSource
  omega

/-- Canonical finite-volume spatial covariance decay for two periodic `Z₂`
plaquettes from a closed-form periodic link-base `L¹` separation hypothesis. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_of_edgeBaseL1Separated
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEdge n))
    (hStrict :
      FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) hEdge < 1)
    (d : ℕ)
    (hSeparated :
      periodicHypercubicEdgeBaseL1SeparatedAtLeast n
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
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_of_coordinateSeparated
      n beta hBeta sourcePlaquette targetPlaquette hEdge hStrict d
  exact
    periodicHypercubicCoordinateNeighborSeparatedAtLeast_of_edgeBaseL1Separated
      n
      (periodicHypercubicPlaquetteEdges n sourcePlaquette)
      (periodicHypercubicPlaquetteEdges n targetPlaquette)
      d hSeparated

end

end MathlibAnalytic
end MGAP4D
