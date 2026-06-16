import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFluctuationEnergy

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_lattice_single_link_local_energy_compile_smoke
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) : ℝ :=
  L.singleLinkConditionalFluctuationEnergy f A e

theorem finite_lattice_single_link_variance_energy_compile_smoke
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) :
    L.singleLinkConditionalVariance f A e =
      L.singleLinkConditionalFluctuationEnergy f A e :=
  finite_lattice_singleLinkConditionalVariance_eq_fluctuationEnergy
    L f A e

theorem finite_lattice_single_link_dirichlet_energy_compile_smoke
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathDirichletForm f =
      L.singleLinkHeatBathFluctuationDirichletForm f :=
  finite_lattice_singleLinkHeatBathDirichletForm_eq_fluctuationEnergy L f

end

end MathlibAnalytic
end MGAP4D
