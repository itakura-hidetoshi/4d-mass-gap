import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalTotalVariationContraction
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalTotalVariationHomogeneity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every nonconstant eigenobservable of the concrete random-scan heat-bath
sweep has eigenvalue bounded in modulus by the Dobrushin random-scan rate. -/
theorem finite_lattice_randomScanHeatBathSweep_eigenvalue_abs_le_rate
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (λ : ℝ)
    (hEigen : L.randomScanHeatBathSweep f = λ • f)
    (hVariation : L.canonicalTotalVariation f ≠ 0) :
    |λ| ≤ finiteLatticeWilsonDobrushinRandomScanRate L D := by
  have hContract :=
    finite_lattice_randomScanHeatBathSweep_canonicalTotalVariation_le_rate_mul
      L f D hEdge
  rw [hEigen, finite_lattice_canonicalTotalVariation_smul] at hContract
  have hVariationPos : 0 < L.canonicalTotalVariation f :=
    lt_of_le_of_ne
      (finite_lattice_canonicalTotalVariation_nonneg L f)
      (Ne.symm hVariation)
  exact (mul_le_mul_right hVariationPos).mp hContract

/-- In particular, every nonzero Gibbs-centered eigenobservable has eigenvalue
bounded in modulus by the same strict Dobrushin rate. -/
theorem finite_lattice_centered_randomScanHeatBathSweep_eigenvalue_abs_le_rate
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (λ : ℝ)
    (hMean : L.gibbsExpectationReal f = 0)
    (hNonzero : f ≠ 0)
    (hEigen : L.randomScanHeatBathSweep f = λ • f) :
    |λ| ≤ finiteLatticeWilsonDobrushinRandomScanRate L D := by
  apply finite_lattice_randomScanHeatBathSweep_eigenvalue_abs_le_rate
    L f D hEdge λ hEigen
  intro hVariation
  apply hNonzero
  exact
    finite_lattice_centered_observable_eq_zero_of_canonicalTotalVariation_eq_zero
      L f hMean hVariation

end

end MathlibAnalytic
end MGAP4D
