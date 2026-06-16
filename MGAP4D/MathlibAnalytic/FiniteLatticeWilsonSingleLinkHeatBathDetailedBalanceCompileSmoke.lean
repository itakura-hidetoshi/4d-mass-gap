import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathDetailedBalance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

theorem finite_lattice_single_link_restore_compile_smoke
    (A : L.Configuration) (e : L.Edge) :
    L.replaceLink A e (A e) = A :=
  finite_lattice_replaceLink_original L A e

theorem finite_lattice_single_link_reversible_mass_compile_smoke
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) :
    L.gibbsPMF A * L.singleLinkConditionalPMF A e g =
      L.gibbsPMF (L.replaceLink A e g) *
        L.singleLinkConditionalPMF (L.replaceLink A e g) e (A e) :=
  finite_lattice_singleLinkHeatBath_reversible_mass L A e g

theorem finite_lattice_single_link_detailed_balance_real_compile_smoke
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) :
    L.gibbsProbabilityReal A *
        (L.singleLinkConditionalPMF A e g).toReal =
      L.gibbsProbabilityReal (L.replaceLink A e g) *
        (L.singleLinkConditionalPMF
          (L.replaceLink A e g) e (A e)).toReal :=
  finite_lattice_singleLinkHeatBath_detailedBalance_real L A e g

end

end MathlibAnalytic
end MGAP4D
