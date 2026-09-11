import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteBaseL1SpatialCovariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical graph-decay radius extracted from the closed-form periodic
`L¹` distance between two plaquette bases.  Natural subtraction truncates the
radius to zero when the two-unit boundary margin is unavailable. -/
def periodicHypercubicPlaquetteBaseL1DecayRadius
    (n : ℕ)
    (source target : PeriodicHypercubicPlaquette n) : ℕ :=
  (periodicHypercubicPlaquetteBaseL1Distance n source target - 2) / 2

/-- At base distance below two, the automatically selected decay radius is
zero. -/
theorem periodicHypercubicPlaquetteBaseL1DecayRadius_eq_zero_of_lt_two
    (n : ℕ)
    (source target : PeriodicHypercubicPlaquette n)
    (hDistance :
      periodicHypercubicPlaquetteBaseL1Distance n source target < 2) :
    periodicHypercubicPlaquetteBaseL1DecayRadius n source target = 0 := by
  unfold periodicHypercubicPlaquetteBaseL1DecayRadius
  omega

/-- Once the two-unit boundary margin is available, the automatically selected
radius satisfies the exact lower bound needed by plaquette-base separation. -/
theorem periodicHypercubicPlaquetteBaseL1DecayRadius_spec
    (n : ℕ)
    (source target : PeriodicHypercubicPlaquette n)
    (hDistance :
      2 ≤ periodicHypercubicPlaquetteBaseL1Distance n source target) :
    2 * periodicHypercubicPlaquetteBaseL1DecayRadius n source target + 2 ≤
      periodicHypercubicPlaquetteBaseL1Distance n source target := by
  unfold periodicHypercubicPlaquetteBaseL1DecayRadius
  omega

/-- At base distance at least two, the automatic radius provides the
plaquette-base separation certificate required by the previous layer. -/
theorem periodicHypercubicPlaquetteBaseL1SeparatedAtLeast_decayRadius
    (n : ℕ)
    (source target : PeriodicHypercubicPlaquette n)
    (hDistance :
      2 ≤ periodicHypercubicPlaquetteBaseL1Distance n source target) :
    periodicHypercubicPlaquetteBaseL1SeparatedAtLeast n source target
      (periodicHypercubicPlaquetteBaseL1DecayRadius n source target) := by
  unfold periodicHypercubicPlaquetteBaseL1SeparatedAtLeast
  exact
    periodicHypercubicPlaquetteBaseL1DecayRadius_spec
      n source target hDistance

/-- The automatically selected radius always gives coordinate-neighbor
separation.  For base distance below two the radius is zero, so the defining
quantification over smaller graph radii is empty. -/
theorem periodicHypercubicCoordinateNeighborSeparatedAtLeast_decayRadius
    (n : ℕ) [NeZero n]
    (source target : PeriodicHypercubicPlaquette n) :
    periodicHypercubicCoordinateNeighborSeparatedAtLeast n
      (periodicHypercubicPlaquetteEdges n source)
      (periodicHypercubicPlaquetteEdges n target)
      (periodicHypercubicPlaquetteBaseL1DecayRadius n source target) := by
  by_cases hDistance :
      2 ≤ periodicHypercubicPlaquetteBaseL1Distance n source target
  · apply
      periodicHypercubicCoordinateNeighborSeparatedAtLeast_of_edgeBaseL1Separated
        n
        (periodicHypercubicPlaquetteEdges n source)
        (periodicHypercubicPlaquetteEdges n target)
        (periodicHypercubicPlaquetteBaseL1DecayRadius n source target)
    apply
      periodicHypercubicEdgeBaseL1SeparatedAtLeast_of_plaquetteBaseL1Separated
        n source target
        (periodicHypercubicPlaquetteBaseL1DecayRadius n source target)
    exact
      periodicHypercubicPlaquetteBaseL1SeparatedAtLeast_decayRadius
        n source target hDistance
  · have hLt :
        periodicHypercubicPlaquetteBaseL1Distance n source target < 2 := by
      omega
    have hRadius :
        periodicHypercubicPlaquetteBaseL1DecayRadius n source target = 0 :=
      periodicHypercubicPlaquetteBaseL1DecayRadius_eq_zero_of_lt_two
        n source target hLt
    rw [hRadius]
    intro sourceEdge hSourceEdge targetEdge hTargetEdge m hm hMem
    omega

/-- Canonical finite-volume periodic `Z₂` plaquette covariance decay with the
exponent chosen automatically from the closed-form plaquette-base periodic
`L¹` distance.  No separate graph radius or geometric separation proof is
required from the caller. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_automaticL1
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEdge n))
    (hStrict :
      FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) hEdge < 1) :
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
            (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) hEdge ^
            periodicHypercubicPlaquetteBaseL1DecayRadius
              n sourcePlaquette targetPlaquette /
          (1 -
            FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
              (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) hEdge)) := by
  apply
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_of_coordinateSeparated
      n beta hBeta sourcePlaquette targetPlaquette hEdge hStrict
      (periodicHypercubicPlaquetteBaseL1DecayRadius
        n sourcePlaquette targetPlaquette)
  exact
    periodicHypercubicCoordinateNeighborSeparatedAtLeast_decayRadius
      n sourcePlaquette targetPlaquette

end

end MathlibAnalytic
end MGAP4D
