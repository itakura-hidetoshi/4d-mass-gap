import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinGreenCovarianceComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The separated-support Gibbs covariance estimate no longer needs an
independent Green covariance comparison certificate: the random-scan telescope
constructs it from the finite-volume Dobrushin data. -/
theorem finite_oriented_gibbsCovarianceReal_abs_le_of_separated
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (S : FiniteOrientedLatticeWilsonDobrushinActiveSupport D)
    {f g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (left right : Finset L.Edge)
    (hPSupport :
      ∀ target : L.Edge,
        target ∉ left → P.variation target = 0)
    (hQSupport :
      ∀ source : L.Edge,
        source ∉ right → Q.variation source = 0)
    (d : ℕ)
    (hSeparated :
      L.activePlaquetteNeighborSeparatedAtLeast left right d) :
    |L.gibbsCovarianceReal f g| ≤
      (∑ target : L.Edge, P.variation target) *
        (D.dobrushinCoefficient ^ d /
          (1 - D.dobrushinCoefficient)) *
            ∑ source : L.Edge, Q.variation source := by
  exact
    (finite_oriented_dobrushinGreenCovarianceComparison D hEdge)
      |>.gibbsCovarianceReal_abs_le_of_separated
        S P Q left right hPSupport hQSupport d hSeparated

/-- Two active-neighbor-separated periodic `Z₂` plaquettes satisfy the explicit
finite-volume spatial covariance estimate without supplying a separate
comparison certificate. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_greenTail_of_dobrushin
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta))
    (S : FiniteOrientedLatticeWilsonDobrushinActiveSupport D)
    (d : ℕ)
    (hSeparated :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        |>.activePlaquetteNeighborSeparatedAtLeast
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
        (D.dobrushinCoefficient ^ d /
          (1 - D.dobrushinCoefficient)) := by
  have hEdge : 0 < Fintype.card (PeriodicHypercubicEdge n) :=
    Fintype.card_pos_iff.mpr ⟨((fun _ => 0), 0)⟩
  exact
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_greenTail
      n beta hBeta sourcePlaquette targetPlaquette D S
        (finite_oriented_dobrushinGreenCovarianceComparison D hEdge)
        d hSeparated

end

end MathlibAnalytic
end MGAP4D
