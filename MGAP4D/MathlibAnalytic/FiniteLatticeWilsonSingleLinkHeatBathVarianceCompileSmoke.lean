import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathVariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_lattice_single_link_conditional_expectation_compile_smoke
    (f : L.Configuration → ℝ) (A : L.Configuration) (e : L.Edge) : ℝ :=
  L.singleLinkConditionalExpectation f A e

noncomputable def finite_lattice_single_link_conditional_variance_compile_smoke
    (f : L.Configuration → ℝ) (A : L.Configuration) (e : L.Edge) : ℝ :=
  L.singleLinkConditionalVariance f A e

theorem finite_lattice_single_link_conditional_variance_nonneg_compile_smoke
    (f : L.Configuration → ℝ) (A : L.Configuration) (e : L.Edge) :
    0 ≤ L.singleLinkConditionalVariance f A e :=
  finite_lattice_singleLinkConditionalVariance_nonneg L f A e

theorem finite_lattice_single_link_heat_bath_dirichlet_nonneg_compile_smoke
    (f : L.Configuration → ℝ) :
    0 ≤ L.singleLinkHeatBathDirichletForm f :=
  finite_lattice_singleLinkHeatBathDirichletForm_nonneg L f

variable (F : FiniteLatticeWilsonApproximationFamily)

example : Prop :=
  F.UniformExactGapSingleLinkHeatBathPoincare

end

end MathlibAnalytic
end MGAP4D
