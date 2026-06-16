import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathGibbsSelfAdjoint

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_lattice_gibbs_pairing_compile_smoke
    (f g : L.Configuration → ℝ) : ℝ :=
  L.gibbsPairingReal f g

noncomputable def finite_lattice_single_link_update_swap_compile_smoke
    (e : L.Edge) :
    (L.Configuration × L.Gauge) ≃ (L.Configuration × L.Gauge) :=
  L.singleLinkUpdateSwapEquiv e

theorem finite_lattice_single_link_projection_self_adjoint_compile_smoke
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathProjectionLinearMap e f) g =
      L.gibbsPairingReal f
        (L.singleLinkHeatBathProjectionLinearMap e g) :=
  finite_lattice_singleLinkHeatBathProjection_gibbs_selfAdjoint L e f g

end

end MathlibAnalytic
end MGAP4D
