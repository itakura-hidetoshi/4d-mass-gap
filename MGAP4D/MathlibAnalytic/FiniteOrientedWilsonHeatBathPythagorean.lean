import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonHeatBathOrthogonality

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The native Gibbs pairing is additive in its first argument. -/
theorem finite_oriented_gibbsPairingReal_add_left
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.gibbsPairingReal (f + g) h =
      L.gibbsPairingReal f h + L.gibbsPairingReal g h := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.add_apply]
  ring

/-- The native Gibbs pairing is additive in its second argument. -/
theorem finite_oriented_gibbsPairingReal_add_right
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.gibbsPairingReal f (g + h) =
      L.gibbsPairingReal f g + L.gibbsPairingReal f h := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.add_apply]
  ring

/-- Native Gibbs pairing decomposes into projected and fluctuation parts. -/
theorem finite_oriented_singleLinkHeatBath_gibbsPairing_projection_fluctuation_decomposition
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
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
      rw [finite_oriented_singleLinkHeatBath_projection_add_fluctuation L e f,
        finite_oriented_singleLinkHeatBath_projection_add_fluctuation L e g]
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
      rw [finite_oriented_gibbsPairingReal_add_left,
        finite_oriented_gibbsPairingReal_add_right,
        finite_oriented_gibbsPairingReal_add_right]
    _ =
        L.gibbsPairingReal
            (L.singleLinkHeatBathProjectionLinearMap e f)
            (L.singleLinkHeatBathProjectionLinearMap e g) +
          L.gibbsPairingReal
            (L.singleLinkHeatBathFluctuationLinearMap e f)
            (L.singleLinkHeatBathFluctuationLinearMap e g) := by
      rw [finite_oriented_singleLinkHeatBath_gibbsPairing_projection_fluctuation_zero,
        finite_oriented_singleLinkHeatBath_gibbsPairing_fluctuation_projection_zero]
      ring

/-- Native Gibbs-weighted Pythagorean identity. -/
theorem finite_oriented_singleLinkHeatBath_gibbsPairing_pythagorean
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.gibbsPairingReal f f =
      L.gibbsPairingReal
          (L.singleLinkHeatBathProjectionLinearMap e f)
          (L.singleLinkHeatBathProjectionLinearMap e f) +
        L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuationLinearMap e f)
          (L.singleLinkHeatBathFluctuationLinearMap e f) :=
  finite_oriented_singleLinkHeatBath_gibbsPairing_projection_fluctuation_decomposition
    L e f f

end

end MathlibAnalytic
end MGAP4D
