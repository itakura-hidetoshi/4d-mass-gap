import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkApproximateTensorization

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)
  (T : FiniteLatticeWilsonSingleLinkApproximateTensorizationData L)

example : L.ExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_exactGap_heatBathPoincare_of_approximateTensorization L T

variable (F : FiniteLatticeWilsonApproximationFamily)
  (U : F.UniformSingleLinkApproximateTensorizationData)

noncomputable def finite_lattice_uniform_approximate_tensorization_system_data_compile_smoke
    (i : F.index) :
    FiniteLatticeWilsonSingleLinkApproximateTensorizationData (F.system i) :=
  U.toSystemData i

example : F.UniformExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_uniform_exactGap_heatBathPoincare_of_approximateTensorization F U

end

end MathlibAnalytic
end MGAP4D
