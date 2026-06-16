import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonHeatBathSweepContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)
  (S : FiniteLatticeWilsonHeatBathSweepContractionData L)

example : L.ExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_exactGap_heatBathPoincare_of_sweepContraction L S

example (f : L.Configuration → ℝ) :
    (1 - S.contractionRate) * L.gibbsVarianceReal f ≤
      L.singleLinkHeatBathDirichletForm f :=
  finite_lattice_one_sub_sweepRate_mul_variance_le_dirichlet L S f

variable (F : FiniteLatticeWilsonApproximationFamily)
  (U : F.UniformHeatBathSweepContractionData)

noncomputable def finite_lattice_uniform_sweep_system_data_compile_smoke
    (i : F.index) :
    FiniteLatticeWilsonHeatBathSweepContractionData (F.system i) :=
  U.toSystemData i

example : F.UniformExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_uniform_exactGap_heatBathPoincare_of_sweepContraction F U

end

end MathlibAnalytic
end MGAP4D
