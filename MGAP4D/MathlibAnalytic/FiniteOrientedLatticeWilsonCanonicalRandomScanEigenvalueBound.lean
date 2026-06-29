import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalTotalVariationContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem finite_oriented_randomScanHeatBathSweep_eigenvalue_abs_le_rate
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (eigenvalue : ℝ)
    (hEigen : L.randomScanHeatBathSweep f = eigenvalue • f)
    (hVariation : L.canonicalTotalVariation f ≠ 0) :
    |eigenvalue| ≤
      finiteOrientedLatticeWilsonDobrushinRandomScanRate L D := by
  have hContract :=
    finite_oriented_randomScanHeatBathSweep_canonicalTotalVariation_le_rate_mul
      L f D hEdge
  rw [hEigen, finite_oriented_canonicalTotalVariation_smul] at hContract
  have hVariationPos : 0 < L.canonicalTotalVariation f :=
    lt_of_le_of_ne
      (finite_oriented_canonicalTotalVariation_nonneg L f)
      (Ne.symm hVariation)
  nlinarith

theorem finite_oriented_centered_randomScanHeatBathSweep_eigenvalue_abs_le_rate
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (eigenvalue : ℝ)
    (hMean : L.gibbsExpectationReal f = 0)
    (hNonzero : f ≠ 0)
    (hEigen : L.randomScanHeatBathSweep f = eigenvalue • f) :
    |eigenvalue| ≤
      finiteOrientedLatticeWilsonDobrushinRandomScanRate L D := by
  apply finite_oriented_randomScanHeatBathSweep_eigenvalue_abs_le_rate
    L f D hEdge eigenvalue hEigen
  intro hVariation
  apply hNonzero
  exact
    finite_oriented_centered_observable_eq_zero_of_canonicalTotalVariation_eq_zero
      L f hMean hVariation

end
end MathlibAnalytic
end MGAP4D
