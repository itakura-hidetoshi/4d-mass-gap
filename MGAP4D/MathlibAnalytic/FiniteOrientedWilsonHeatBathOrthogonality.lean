import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonHeatBathWeightedFluctuationNorm

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The projected component is Gibbs-orthogonal to every native local
fluctuation. -/
theorem finite_oriented_singleLinkHeatBath_gibbsPairing_projection_fluctuation_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
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
      finite_oriented_singleLinkHeatBathProjectionLinearMap_gibbsPairing_symm
        L e f (L.singleLinkHeatBathFluctuationLinearMap e g)
    _ = L.gibbsPairingReal f 0 := by
      rw [finite_oriented_singleLinkHeatBathProjection_annihilates_fluctuation]
    _ = 0 := by
      classical
      unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
      simp

/-- Every native local fluctuation is Gibbs-orthogonal to the projected
component. -/
theorem finite_oriented_singleLinkHeatBath_gibbsPairing_fluctuation_projection_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
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
      finite_oriented_gibbsPairingReal_symm L _ _
    _ = 0 :=
      finite_oriented_singleLinkHeatBath_gibbsPairing_projection_fluctuation_zero
        L e g f

end

end MathlibAnalytic
end MGAP4D
