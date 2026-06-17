import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalTotalVariationContraction
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinRandomScanScale

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Under a strict Dobrushin coefficient and a nonempty edge set, every fixed
observable of the concrete random-scan heat-bath sweep is constant. -/
theorem finite_lattice_randomScanHeatBathSweep_fixed_eq_const
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (hFix : L.randomScanHeatBathSweep f = f) :
    f = fun _ : L.Configuration => f default := by
  have hContract :=
    finite_lattice_randomScanHeatBathSweep_canonicalTotalVariation_le_rate_mul
      L f D hEdge
  rw [hFix] at hContract
  have hRateLt :
      finiteLatticeWilsonDobrushinRandomScanRate L D < 1 :=
    finite_lattice_dobrushinRandomScanRate_lt_one L D hEdge
  have hTotalNonneg : 0 ≤ L.canonicalTotalVariation f :=
    finite_lattice_canonicalTotalVariation_nonneg L f
  have hTotalZero : L.canonicalTotalVariation f = 0 := by
    nlinarith
  exact
    (finite_lattice_canonicalTotalVariation_eq_zero_iff_const L f).mp
      hTotalZero

/-- The centered fixed-point space of the concrete random-scan heat-bath sweep
is trivial. -/
theorem finite_lattice_centered_randomScanHeatBathSweep_fixed_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (hMean : L.gibbsExpectationReal f = 0)
    (hFix : L.randomScanHeatBathSweep f = f) :
    f = 0 := by
  have hConst :=
    finite_lattice_randomScanHeatBathSweep_fixed_eq_const
      L f D hEdge hFix
  have hTotal : L.canonicalTotalVariation f = 0 := by
    rw [hConst]
    exact finite_lattice_canonicalTotalVariation_const_eq_zero
      L (f default)
  exact
    finite_lattice_centered_observable_eq_zero_of_canonicalTotalVariation_eq_zero
      L f hMean hTotal

end

end MathlibAnalytic
end MGAP4D
