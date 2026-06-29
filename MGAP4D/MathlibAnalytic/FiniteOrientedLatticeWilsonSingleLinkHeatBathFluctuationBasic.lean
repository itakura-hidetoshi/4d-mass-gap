import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkHeatBathLinearProjection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Native local fluctuation operator `Q_e = I - P_e`. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathFluctuationLinearMap
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    (L.Configuration → ℝ) →ₗ[ℝ] (L.Configuration → ℝ) :=
  LinearMap.id - L.singleLinkHeatBathProjectionLinearMap e

@[simp] theorem finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathFluctuationLinearMap e f =
      f - L.singleLinkHeatBathProjectionLinearMap e f :=
  rfl

/-- Native conditional expectation annihilates local fluctuations. -/
theorem finite_oriented_singleLinkHeatBathProjection_annihilates_fluctuation
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjectionLinearMap e
        (L.singleLinkHeatBathFluctuationLinearMap e f) = 0 := by
  rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply,
    map_sub]
  change L.singleLinkHeatBathProjection e f -
      L.singleLinkHeatBathProjection e
        (L.singleLinkHeatBathProjection e f) = 0
  rw [finite_oriented_singleLinkHeatBathProjection_idempotent]
  simp

/-- Local fluctuations annihilate the conditionally projected component. -/
theorem finite_oriented_singleLinkHeatBathFluctuation_annihilates_projection
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathFluctuationLinearMap e
        (L.singleLinkHeatBathProjectionLinearMap e f) = 0 := by
  rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply]
  change L.singleLinkHeatBathProjection e f -
      L.singleLinkHeatBathProjection e
        (L.singleLinkHeatBathProjection e f) = 0
  rw [finite_oriented_singleLinkHeatBathProjection_idempotent]
  simp

/-- Every observable decomposes as `P_e f + Q_e f`. -/
theorem finite_oriented_singleLinkHeatBath_projection_add_fluctuation
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjectionLinearMap e f +
        L.singleLinkHeatBathFluctuationLinearMap e f = f := by
  rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply]
  abel

/-- The native local fluctuation operator is idempotent. -/
theorem finite_oriented_singleLinkHeatBathFluctuationLinearMap_idempotent
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    (L.singleLinkHeatBathFluctuationLinearMap e).comp
        (L.singleLinkHeatBathFluctuationLinearMap e) =
      L.singleLinkHeatBathFluctuationLinearMap e := by
  apply LinearMap.ext
  intro f
  rw [LinearMap.comp_apply,
    finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply,
    finite_oriented_singleLinkHeatBathProjection_annihilates_fluctuation]
  simp

end

end MathlibAnalytic
end MGAP4D
