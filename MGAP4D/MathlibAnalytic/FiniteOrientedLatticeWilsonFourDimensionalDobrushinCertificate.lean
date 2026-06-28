import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalDobrushinCoefficient
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicOrientedWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem
    FiniteOrientedWilsonFourDimensionalIncidenceCertificate.canonicalDobrushinCoefficient_le_eighteen_mul
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedWilsonFourDimensionalIncidenceCertificate L)
    (eta : ℝ)
    (hEta : 0 ≤ eta)
    (hInfluence : ∀ (target source : L.Edge),
      source ∈ L.activePlaquetteNeighbors target →
        L.canonicalDobrushinInfluence target source ≤ eta) :
    L.canonicalDobrushinCoefficient D.edgeCard_pos ≤ 18 * eta := by
  simpa using
    (finite_oriented_canonicalDobrushinCoefficient_le_degree_mul
      L D.edgeCard_pos 18 eta hEta
      D.activeNeighborCard_le_eighteen hInfluence)

theorem
    FiniteOrientedWilsonFourDimensionalIncidenceCertificate.canonicalDobrushinCoefficient_lt_one_of_lt_inv_eighteen
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedWilsonFourDimensionalIncidenceCertificate L)
    (eta : ℝ)
    (hEta : 0 ≤ eta)
    (hInfluence : ∀ (target source : L.Edge),
      source ∈ L.activePlaquetteNeighbors target →
        L.canonicalDobrushinInfluence target source ≤ eta)
    (hThreshold : eta < (18 : ℝ)⁻¹) :
    L.canonicalDobrushinCoefficient D.edgeCard_pos < 1 := by
  apply finite_oriented_canonicalDobrushinCoefficient_lt_one_of_degree_mul_lt_one
    L D.edgeCard_pos 18 eta hEta
    D.activeNeighborCard_le_eighteen hInfluence
  norm_num at hThreshold ⊢
  linarith

theorem
    FiniteOrientedWilsonFourDimensionalIncidenceCertificate.canonicalDobrushinCoefficient_lt_one_of_expRatioBound
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedWilsonFourDimensionalIncidenceCertificate L)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio : L.ActiveConditionalExpRatioBound R)
    (hThreshold :
      (Real.exp R - 1) / (Real.exp R + 1) < (18 : ℝ)⁻¹) :
    L.canonicalDobrushinCoefficient D.edgeCard_pos < 1 := by
  let eta : ℝ := (Real.exp R - 1) / (Real.exp R + 1)
  have hEta : 0 ≤ eta :=
    expLikelihoodRatioTotalVariationBound_nonneg R hR
  apply D.canonicalDobrushinCoefficient_lt_one_of_lt_inv_eighteen eta hEta
  · intro target source hActive
    exact finite_oriented_canonicalDobrushinInfluence_le_expRatioBound_of_active
      L R hR hRatio target source hActive
  · exact hThreshold

theorem z2PeriodicHypercubicOriented_canonicalDobrushinCoefficient_lt_one
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
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).canonicalDobrushinCoefficient
        (z2PeriodicHypercubicOrientedIncidenceCertificate
          n hn beta hBeta).edgeCard_pos < 1 := by
  exact
    (z2PeriodicHypercubicOrientedIncidenceCertificate
      n hn beta hBeta).canonicalDobrushinCoefficient_lt_one_of_expRatioBound
        R hR hRatio hThreshold

end
end MathlibAnalytic
end MGAP4D
