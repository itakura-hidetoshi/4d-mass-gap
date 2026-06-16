import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonRandomScanHeatBathSweep

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_lattice_single_link_heat_bath_operator_compile_smoke
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.Configuration → ℝ :=
  L.singleLinkHeatBathOperator e f

noncomputable def finite_lattice_random_scan_heat_bath_sweep_compile_smoke
    (f : L.Configuration → ℝ) :
    L.Configuration → ℝ :=
  L.randomScanHeatBathSweep f

variable (R : FiniteLatticeWilsonRandomScanHeatBathContractionData L)

noncomputable def finite_lattice_random_scan_to_sweep_data_compile_smoke :
    FiniteLatticeWilsonHeatBathSweepContractionData L :=
  R.toSweepContractionData

example : L.ExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_exactGap_heatBathPoincare_of_randomScanContraction L R

variable (F : FiniteLatticeWilsonApproximationFamily)
  (U : F.UniformRandomScanHeatBathContractionData)

example : F.UniformExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_uniform_exactGap_heatBathPoincare_of_randomScanContraction F U

end

end MathlibAnalytic
end MGAP4D
