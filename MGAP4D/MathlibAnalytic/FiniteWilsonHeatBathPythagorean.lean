import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathPairingOrthogonality

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The finite Wilson Gibbs pairing is additive in its first argument. -/
theorem finite_lattice_gibbsPairingReal_add_left
    (L : FiniteLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.gibbsPairingReal (f + g) h =
      L.gibbsPairingReal f h + L.gibbsPairingReal g h := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.add_apply]
  ring

/-- The finite Wilson Gibbs pairing is additive in its second argument. -/
theorem finite_lattice_gibbsPairingReal_add_right
    (L : FiniteLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.gibbsPairingReal f (g + h) =
      L.gibbsPairingReal f g + L.gibbsPairingReal f h := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.add_apply]
  ring

/-- The Gibbs pairing decomposes into the mutually orthogonal conditional and
fluctuation components. -/
theorem finite_lattice_singleLinkHeatBath_gibbsPairing_projection_fluctuation_decomposition
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f g =
      L.gibbsPairingReal
          (L.singleLinkHeatBathProjectionLinearMap e f)
          (L.singleLinkHeatBathProjectionLinearMap e g) +
        L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuationLinearMap e f)
          (L.singleLinkHeatBathFluctuationLinearMap e g) := by
  calc
    L.gibbsPairingReal f g =
        L.gibbsPairingReal
          (L.singleLinkHeatBathProjectionLinearMap e f +
            L.singleLinkHeatBathFluctuationLinearMap e f)
          (L.singleLinkHeatBathProjectionLinearMap e g +
            L.singleLinkHeatBathFluctuationLinearMap e g) := by
      rw [finite_lattice_singleLinkHeatBath_projection_add_fluctuation L e f,
        finite_lattice_singleLinkHeatBath_projection_add_fluctuation L e g]
    _ =
        (L.gibbsPairingReal
            (L.singleLinkHeatBathProjectionLinearMap e f)
            (L.singleLinkHeatBathProjectionLinearMap e g) +
          L.gibbsPairingReal
            (L.singleLinkHeatBathProjectionLinearMap e f)
            (L.singleLinkHeatBathFluctuationLinearMap e g)) +
        (L.gibbsPairingReal
            (L.singleLinkHeatBathFluctuationLinearMap e f)
            (L.singleLinkHeatBathProjectionLinearMap e g) +
          L.gibbsPairingReal
            (L.singleLinkHeatBathFluctuationLinearMap e f)
            (L.singleLinkHeatBathFluctuationLinearMap e g)) := by
      rw [finite_lattice_gibbsPairingReal_add_left,
        finite_lattice_gibbsPairingReal_add_right,
        finite_lattice_gibbsPairingReal_add_right]
    _ =
        L.gibbsPairingReal
            (L.singleLinkHeatBathProjectionLinearMap e f)
            (L.singleLinkHeatBathProjectionLinearMap e g) +
          L.gibbsPairingReal
            (L.singleLinkHeatBathFluctuationLinearMap e f)
            (L.singleLinkHeatBathFluctuationLinearMap e g) := by
      rw [finite_lattice_singleLinkHeatBath_gibbsPairing_projection_fluctuation_zero,
        finite_lattice_singleLinkHeatBath_gibbsPairing_fluctuation_projection_zero]
      ring

/-- Gibbs-weighted Pythagorean identity for the exact single-link heat-bath
orthogonal decomposition. -/
theorem finite_lattice_singleLinkHeatBath_gibbsPairing_pythagorean
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.gibbsPairingReal f f =
      L.gibbsPairingReal
          (L.singleLinkHeatBathProjectionLinearMap e f)
          (L.singleLinkHeatBathProjectionLinearMap e f) +
        L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuationLinearMap e f)
          (L.singleLinkHeatBathFluctuationLinearMap e f) := by
  exact
    finite_lattice_singleLinkHeatBath_gibbsPairing_projection_fluctuation_decomposition
      L e f f

end

end MathlibAnalytic
end MGAP4D
