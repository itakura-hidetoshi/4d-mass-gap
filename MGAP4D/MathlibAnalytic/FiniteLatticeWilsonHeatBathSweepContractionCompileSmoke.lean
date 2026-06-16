import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonHeatBathSweepContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)
  (S : FiniteLatticeWilsonHeatBathSweepContractionData L)

example : L.ExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_exactGap_heatBathPoincare_of_sweepContraction L S

noncomputable def finite_lattice_sweep_to_approximate_tensorization_compile_smoke :
    FiniteLatticeWilsonSingleLinkApproximateTensorizationData L :=
  S.toApproximateTensorizationData

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
