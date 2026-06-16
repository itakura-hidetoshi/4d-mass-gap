import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonGibbsRealVariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_lattice_gibbs_probability_real_compile_smoke
    (A : L.Configuration) : ℝ :=
  L.gibbsProbabilityReal A

noncomputable def finite_lattice_gibbs_expectation_real_compile_smoke
    (f : L.Configuration → ℝ) : ℝ :=
  L.gibbsExpectationReal f

theorem finite_lattice_gibbs_probability_nonneg_compile_smoke
    (A : L.Configuration) :
    0 ≤ L.gibbsProbabilityReal A :=
  finite_lattice_gibbsProbabilityReal_nonneg L A

end

end MathlibAnalytic
end MGAP4D
