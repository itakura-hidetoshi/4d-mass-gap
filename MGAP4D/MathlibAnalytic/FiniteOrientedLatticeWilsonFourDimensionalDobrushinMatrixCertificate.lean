import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalDobrushinMatrix
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonFourDimensionalDobrushinCertificate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Four-dimensional incidence and likelihood-ratio control produce the full
proof-relevant oriented canonical Dobrushin matrix. -/
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

/-- The periodic orientation-correct `Z₂` system obtains its canonical
proof-relevant Dobrushin matrix from the exact four-dimensional incidence
certificate. -/
noncomputable def z2PeriodicHypercubicOriented_canonicalDobrushinMatrixData
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).ActiveConditionalExpRatioBound R)
    (hThreshold :
      (Real.exp R - 1) / (Real.exp R + 1) < (18 : ℝ)⁻¹) :
    FiniteOrientedLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) :=
  (z2PeriodicHypercubicOrientedIncidenceCertificate
    n hn beta hBeta).canonicalDobrushinMatrixData_of_expRatioBound
      R hR hRatio hThreshold

end
end MathlibAnalytic
end MGAP4D
