import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathPairingOrthogonality

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathProjectionLinearMap e f)
        (L.singleLinkHeatBathFluctuationLinearMap e g) = 0 :=
  finite_lattice_singleLinkHeatBath_projection_fluctuation_gibbsOrthogonal
    L e f g

end

end MathlibAnalytic
end MGAP4D
