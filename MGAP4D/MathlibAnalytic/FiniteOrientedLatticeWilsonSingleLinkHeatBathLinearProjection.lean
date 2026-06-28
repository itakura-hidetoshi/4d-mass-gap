import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonHeatBathPairingSymmetry

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Native oriented heat-bath projection preserves addition. -/
theorem finite_oriented_singleLinkHeatBathProjection_add
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection e (f + g) =
      L.singleLinkHeatBathProjection e f +
        L.singleLinkHeatBathProjection e g := by
  funext A
  classical
  simp [FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection,
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation,
    mul_add, Finset.sum_add_distrib]

/-- Native oriented heat-bath projection preserves real scalar multiplication. -/
theorem finite_oriented_singleLinkHeatBathProjection_smul
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (c : ℝ)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection e (c • f) =
      c • L.singleLinkHeatBathProjection e f := by
  funext A
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    ∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A e g).toReal *
          (c * f (L.replaceLink A e g)) =
      ∑ g : L.Gauge,
        c * ((L.singleLinkConditionalPMF A e g).toReal *
          f (L.replaceLink A e g)) := by
      apply Finset.sum_congr rfl
      intro g _hg
      ring
    _ = c * ∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A e g).toReal *
          f (L.replaceLink A e g) := by
      rw [Finset.mul_sum]

/-- Native one-link conditional expectation as a real linear endomorphism. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjectionLinearMap
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    (L.Configuration → ℝ) →ₗ[ℝ] (L.Configuration → ℝ) where
  toFun := L.singleLinkHeatBathProjection e
  map_add' := finite_oriented_singleLinkHeatBathProjection_add L e
  map_smul' := finite_oriented_singleLinkHeatBathProjection_smul L e

@[simp] theorem finite_oriented_singleLinkHeatBathProjectionLinearMap_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjectionLinearMap e f =
      L.singleLinkHeatBathProjection e f :=
  rfl

/-- The native linear heat-bath projection is idempotent. -/
theorem finite_oriented_singleLinkHeatBathProjectionLinearMap_idempotent
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    (L.singleLinkHeatBathProjectionLinearMap e).comp
        (L.singleLinkHeatBathProjectionLinearMap e) =
      L.singleLinkHeatBathProjectionLinearMap e := by
  apply LinearMap.ext
  intro f
  exact finite_oriented_singleLinkHeatBathProjection_idempotent L e f

/-- Off-link-fiber-constant observables form a real linear subspace. -/
def FiniteOrientedLatticeWilsonSystem.offLinkFiberConstantSubmodule
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    Submodule ℝ (L.Configuration → ℝ) where
  carrier := {f | L.OffLinkFiberConstant e f}
  zero_mem' := by
    intro A B _hAgree
    rfl
  add_mem' := by
    intro f g hf hg A B hAgree
    simp only [Pi.add_apply]
    rw [hf A B hAgree, hg A B hAgree]
  smul_mem' := by
    intro c f hf A B hAgree
    simp only [Pi.smul_apply]
    rw [hf A B hAgree]

/-- The range of native conditional expectation is the off-link subspace. -/
theorem finite_oriented_singleLinkHeatBathProjectionLinearMap_range
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    LinearMap.range (L.singleLinkHeatBathProjectionLinearMap e) =
      L.offLinkFiberConstantSubmodule e := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change L.OffLinkFiberConstant e
      (L.singleLinkHeatBathProjection e g)
    exact finite_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
      L e g
  · intro hf
    change L.OffLinkFiberConstant e f at hf
    refine ⟨f, ?_⟩
    change L.singleLinkHeatBathProjection e f = f
    exact finite_oriented_singleLinkHeatBathProjection_fixes L e f hf

/-- Fixed vectors of the native linear projection are the off-link subspace. -/
theorem finite_oriented_singleLinkHeatBathProjectionLinearMap_fixed_iff
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjectionLinearMap e f = f ↔
      f ∈ L.offLinkFiberConstantSubmodule e := by
  change L.singleLinkHeatBathProjection e f = f ↔
    L.OffLinkFiberConstant e f
  exact finite_oriented_singleLinkHeatBathProjection_fixed_iff L e f

/-- The native real-linear projection is symmetric for the Gibbs pairing. -/
theorem finite_oriented_singleLinkHeatBathProjectionLinearMap_gibbsPairing_symm
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathProjectionLinearMap e f) g =
      L.gibbsPairingReal f
        (L.singleLinkHeatBathProjectionLinearMap e g) := by
  simpa only [finite_oriented_singleLinkHeatBathProjectionLinearMap_apply] using
    finite_oriented_singleLinkHeatBath_gibbsPairing_projection_symm
      L e f g

end

end MathlibAnalytic
end MGAP4D
