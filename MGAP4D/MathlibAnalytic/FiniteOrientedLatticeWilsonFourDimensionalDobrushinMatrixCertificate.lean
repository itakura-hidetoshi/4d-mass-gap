import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalDobrushinMatrix
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonFourDimensionalDobrushinCertificate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def
    FiniteOrientedWilsonFourDimensionalIncidenceCertificate.canonicalDobrushinMatrixData_of_expRatioBound
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedWilsonFourDimensionalIncidenceCertificate L)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio : L.ActiveConditionalExpRatioBound R)
    (hThreshold :
      (Real.exp R - 1) / (Real.exp R + 1) < (18 : ℝ)⁻¹) :
    FiniteOrientedLatticeWilsonDobrushinMatrixData L :=
  finiteOrientedLatticeWilsonCanonicalDobrushinMatrixData
    L D.edgeCard_pos
      (D.canonicalDobrushinCoefficient_lt_one_of_expRatioBound
        R hR hRatio hThreshold)

noncomputable def z2PeriodicHypercubicOriented_canonicalDobrushinMatrixData
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio :
      FiniteOrientedLatticeWilsonSystem.ActiveConditionalExpRatioBound
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) R)
    (hThreshold :
      (Real.exp R - 1) / (Real.exp R + 1) < (18 : ℝ)⁻¹) :
    FiniteOrientedLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) :=
  FiniteOrientedWilsonFourDimensionalIncidenceCertificate.canonicalDobrushinMatrixData_of_expRatioBound
    (z2PeriodicHypercubicOrientedIncidenceCertificate n hn beta hBeta)
    R hR hRatio hThreshold

end
end MathlibAnalytic
end MGAP4D
