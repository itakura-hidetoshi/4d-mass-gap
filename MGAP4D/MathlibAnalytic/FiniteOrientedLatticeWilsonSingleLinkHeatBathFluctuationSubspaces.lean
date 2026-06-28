import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkHeatBathFluctuationBasic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The kernel of `Q_e` is the range of `P_e`. -/
theorem finite_oriented_singleLinkHeatBathFluctuationLinearMap_ker_eq_projection_range
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    LinearMap.ker (L.singleLinkHeatBathFluctuationLinearMap e) =
      LinearMap.range (L.singleLinkHeatBathProjectionLinearMap e) := by
  ext f
  constructor
  · intro hf
    change L.singleLinkHeatBathFluctuationLinearMap e f = 0 at hf
    rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply] at hf
    have hFix : L.singleLinkHeatBathProjectionLinearMap e f = f :=
      (sub_eq_zero.mp hf).symm
    exact ⟨f, hFix⟩
  · rintro ⟨g, rfl⟩
    exact finite_oriented_singleLinkHeatBathFluctuation_annihilates_projection
      L e g

/-- The kernel of `Q_e` is the off-link-fiber-constant subspace. -/
theorem finite_oriented_singleLinkHeatBathFluctuationLinearMap_ker
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    LinearMap.ker (L.singleLinkHeatBathFluctuationLinearMap e) =
      L.offLinkFiberConstantSubmodule e := by
  rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_ker_eq_projection_range,
    finite_oriented_singleLinkHeatBathProjectionLinearMap_range]

/-- The range of `Q_e` is the kernel of `P_e`. -/
theorem finite_oriented_singleLinkHeatBathFluctuationLinearMap_range_eq_projection_ker
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    LinearMap.range (L.singleLinkHeatBathFluctuationLinearMap e) =
      LinearMap.ker (L.singleLinkHeatBathProjectionLinearMap e) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact finite_oriented_singleLinkHeatBathProjection_annihilates_fluctuation
      L e g
  · intro hf
    change L.singleLinkHeatBathProjectionLinearMap e f = 0 at hf
    refine ⟨f, ?_⟩
    rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply, hf]
    simp

/-- Fixed vectors of `Q_e` are exactly vectors annihilated by `P_e`. -/
theorem finite_oriented_singleLinkHeatBathFluctuationLinearMap_fixed_iff
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathFluctuationLinearMap e f = f ↔
      L.singleLinkHeatBathProjectionLinearMap e f = 0 := by
  rw [finite_oriented_singleLinkHeatBathFluctuationLinearMap_apply]
  exact sub_eq_self

end

end MathlibAnalytic
end MGAP4D
