import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonGibbsRealVariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_lattice_gibbs_expectation_real_compile_smoke
    (f : L.Configuration → ℝ) : ℝ :=
  L.gibbsExpectationReal f

noncomputable def finite_lattice_gibbs_variance_real_compile_smoke
    (f : L.Configuration → ℝ) : ℝ :=
  L.gibbsVarianceReal f

theorem finite_lattice_gibbs_variance_nonneg_compile_smoke
    (f : L.Configuration → ℝ) :
    0 ≤ L.gibbsVarianceReal f :=
  finite_lattice_gibbsVarianceReal_nonneg L f

end

end MathlibAnalytic
end MGAP4D
