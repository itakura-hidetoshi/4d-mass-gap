import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBath

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_lattice_single_link_replacement_compile_smoke
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) :
    L.Configuration :=
  L.replaceLink A e g

noncomputable def finite_lattice_single_link_conditional_pmf_compile_smoke
    (A : L.Configuration) (e : L.Edge) : PMF L.Gauge :=
  L.singleLinkConditionalPMF A e

theorem finite_lattice_single_link_conditional_pmf_apply_compile_smoke
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) :
    L.singleLinkConditionalPMF A e g =
      L.singleLinkBoltzmannWeight A e g *
        (L.singleLinkPartitionFunction A e)⁻¹ :=
  finite_lattice_singleLinkConditionalPMF_apply L A e g

end

end MathlibAnalytic
end MGAP4D
