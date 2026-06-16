import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathPairingSymmetry
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFluctuationProjection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The conditional-expectation projection is Gibbs-orthogonal to every local
fluctuation. -/
theorem finite_lattice_singleLinkHeatBath_gibbsPairing_projection_fluctuation_zero
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
      unfold FiniteLatticeWilsonSystem.gibbsPairingReal
      simp

/-- Every local fluctuation is Gibbs-orthogonal to the conditional-expectation
projection. -/
theorem finite_lattice_singleLinkHeatBath_gibbsPairing_fluctuation_projection_zero
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
      finite_lattice_gibbsPairingReal_symm L _ _
    _ = 0 :=
      finite_lattice_singleLinkHeatBath_gibbsPairing_projection_fluctuation_zero
        L e g f

/-- The range of the conditional-expectation projection is Gibbs-orthogonal to
the range of the complementary fluctuation projection. -/
theorem finite_lattice_singleLinkHeatBath_projection_range_orthogonal_fluctuation_range
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (p q : L.Configuration → ℝ)
    (hp : p ∈ LinearMap.range (L.singleLinkHeatBathProjectionLinearMap e))
    (hq : q ∈ LinearMap.range (L.singleLinkHeatBathFluctuationLinearMap e)) :
    L.gibbsPairingReal p q = 0 := by
  rcases hp with ⟨f, rfl⟩
  rcases hq with ⟨g, rfl⟩
  exact
    finite_lattice_singleLinkHeatBath_gibbsPairing_projection_fluctuation_zero
      L e f g

end

end MathlibAnalytic
end MGAP4D
