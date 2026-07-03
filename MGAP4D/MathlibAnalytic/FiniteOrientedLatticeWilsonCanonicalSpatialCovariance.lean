import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonAutomaticSpatialCovariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A strict canonical Dobrushin coefficient supplies both the exact influence
matrix and its active geometric support, so the separated-support covariance
bound needs no independent matrix or support certificate. -/
theorem finite_oriented_canonical_gibbsCovarianceReal_abs_le_of_separated
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict : L.canonicalDobrushinCoefficient hEdge < 1)
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
        (L.canonicalDobrushinCoefficient hEdge ^ d /
          (1 - L.canonicalDobrushinCoefficient hEdge)) *
            ∑ source : L.Edge, Q.variation source := by
  let D :=
    finiteOrientedLatticeWilsonCanonicalDobrushinMatrixData
      L hEdge hStrict
  let S : FiniteOrientedLatticeWilsonDobrushinActiveSupport D :=
    finiteOrientedLatticeWilsonCanonicalDobrushinActiveSupport
      L hEdge hStrict
  have hBound :=
    finite_oriented_gibbsCovarianceReal_abs_le_of_separated
      D hEdge S P Q left right hPSupport hQSupport d hSeparated
  simpa [D, finiteOrientedLatticeWilsonCanonicalDobrushinMatrixData] using hBound

/-- Periodic `Z₂` plaquette covariance decay follows from strictness of the
canonical coefficient alone, apart from the explicit geometric separation
hypothesis. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEdge n))
    (hStrict :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        |>.canonicalDobrushinCoefficient hEdge < 1)
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
        (((z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          |>.canonicalDobrushinCoefficient hEdge) ^ d /
          (1 -
            (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
              |>.canonicalDobrushinCoefficient hEdge)) := by
  let D :=
    finiteOrientedLatticeWilsonCanonicalDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
      hEdge hStrict
  let S : FiniteOrientedLatticeWilsonDobrushinActiveSupport D :=
    finiteOrientedLatticeWilsonCanonicalDobrushinActiveSupport
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
      hEdge hStrict
  have hBound :=
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_greenTail_of_dobrushin
      n beta hBeta sourcePlaquette targetPlaquette D S d hSeparated
  simpa [D, finiteOrientedLatticeWilsonCanonicalDobrushinMatrixData] using hBound

end

end MathlibAnalytic
end MGAP4D
