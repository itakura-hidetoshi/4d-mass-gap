import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathPairingSymmetry
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFluctuationProjection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The exact conditional-expectation component is Gibbs-orthogonal to every
local fluctuation component. -/
theorem finite_lattice_singleLinkHeatBath_projection_fluctuation_gibbsOrthogonal
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathProjectionLinearMap e f)
        (L.singleLinkHeatBathFluctuationLinearMap e g) = 0 := by
  calc
    L.gibbsPairingReal
        (L.singleLinkHeatBathProjectionLinearMap e f)
        (L.singleLinkHeatBathFluctuationLinearMap e g) =
      L.gibbsPairingReal f
        (L.singleLinkHeatBathProjectionLinearMap e
          (L.singleLinkHeatBathFluctuationLinearMap e g)) :=
      finite_lattice_singleLinkHeatBathProjectionLinearMap_gibbsPairing_symm
        L e f (L.singleLinkHeatBathFluctuationLinearMap e g)
    _ = L.gibbsPairingReal f 0 := by
      rw [finite_lattice_singleLinkHeatBathProjection_annihilates_fluctuation]
    _ = 0 := by
      classical
      simp [FiniteLatticeWilsonSystem.gibbsPairingReal]

/-- Orthogonality also holds with the fluctuation component in the first slot
and the conditional-expectation component in the second slot. -/
theorem finite_lattice_singleLinkHeatBath_fluctuation_projection_gibbsOrthogonal
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f)
        (L.singleLinkHeatBathProjectionLinearMap e g) = 0 := by
  calc
    L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuationLinearMap e f)
        (L.singleLinkHeatBathProjectionLinearMap e g) =
      L.gibbsPairingReal
        (L.singleLinkHeatBathProjectionLinearMap e g)
        (L.singleLinkHeatBathFluctuationLinearMap e f) :=
      finite_lattice_gibbsPairingReal_symm L
        (L.singleLinkHeatBathFluctuationLinearMap e f)
        (L.singleLinkHeatBathProjectionLinearMap e g)
    _ = 0 :=
      finite_lattice_singleLinkHeatBath_projection_fluctuation_gibbsOrthogonal
        L e g f

/-- In particular, the two components of a single observable are mutually
Gibbs-orthogonal. -/
theorem finite_lattice_singleLinkHeatBath_projection_fluctuation_self_gibbsOrthogonal
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathProjectionLinearMap e f)
        (L.singleLinkHeatBathFluctuationLinearMap e f) = 0 :=
  finite_lattice_singleLinkHeatBath_projection_fluctuation_gibbsOrthogonal
    L e f f

end

end MathlibAnalytic
end MGAP4D
