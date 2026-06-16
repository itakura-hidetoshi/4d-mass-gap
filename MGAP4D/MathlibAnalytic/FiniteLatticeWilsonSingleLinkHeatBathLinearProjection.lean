import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathProjection

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Single-link heat-bath projection preserves addition of real observables. -/
theorem finite_lattice_singleLinkHeatBathProjection_add
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f g : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection e (f + g) =
      L.singleLinkHeatBathProjection e f +
        L.singleLinkHeatBathProjection e g := by
  funext A
  classical
  simp [FiniteLatticeWilsonSystem.singleLinkHeatBathProjection,
    FiniteLatticeWilsonSystem.singleLinkConditionalExpectation,
    mul_add, Finset.sum_add_distrib]

/-- Single-link heat-bath projection preserves real scalar multiplication. -/
theorem finite_lattice_singleLinkHeatBathProjection_smul
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (c : ℝ) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjection e (c • f) =
      c • L.singleLinkHeatBathProjection e f := by
  funext A
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkHeatBathProjection
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalExpectation
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
    _ = c *
        ∑ g : L.Gauge,
          (L.singleLinkConditionalPMF A e g).toReal *
            f (L.replaceLink A e g) := by
      rw [Finset.mul_sum]

/-- The exact single-link heat-bath conditional expectation as a real linear
endomorphism of finite Wilson observables. -/
noncomputable def FiniteLatticeWilsonSystem.singleLinkHeatBathProjectionLinearMap
    (L : FiniteLatticeWilsonSystem) (e : L.Edge) :
    (L.Configuration → ℝ) →ₗ[ℝ] (L.Configuration → ℝ) where
  toFun := L.singleLinkHeatBathProjection e
  map_add' := finite_lattice_singleLinkHeatBathProjection_add L e
  map_smul' := finite_lattice_singleLinkHeatBathProjection_smul L e

@[simp] theorem finite_lattice_singleLinkHeatBathProjectionLinearMap_apply
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjectionLinearMap e f =
      L.singleLinkHeatBathProjection e f :=
  rfl

/-- The linear heat-bath projection is idempotent under composition. -/
theorem finite_lattice_singleLinkHeatBathProjectionLinearMap_idempotent
    (L : FiniteLatticeWilsonSystem) (e : L.Edge) :
    (L.singleLinkHeatBathProjectionLinearMap e).comp
        (L.singleLinkHeatBathProjectionLinearMap e) =
      L.singleLinkHeatBathProjectionLinearMap e := by
  apply LinearMap.ext
  intro f
  exact finite_lattice_singleLinkHeatBathProjection_idempotent L e f

/-- Off-link-fiber-constant observables form a real linear subspace. -/
def FiniteLatticeWilsonSystem.offLinkFiberConstantSubmodule
    (L : FiniteLatticeWilsonSystem) (e : L.Edge) :
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

/-- The range of the linear heat-bath projection is exactly the subspace of
observables depending only on off-link data. -/
theorem finite_lattice_singleLinkHeatBathProjectionLinearMap_range
    (L : FiniteLatticeWilsonSystem) (e : L.Edge) :
    LinearMap.range (L.singleLinkHeatBathProjectionLinearMap e) =
      L.offLinkFiberConstantSubmodule e := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change L.OffLinkFiberConstant e
      (L.singleLinkHeatBathProjection e g)
    exact finite_lattice_singleLinkHeatBathProjection_offLinkFiberConstant
      L e g
  · intro hf
    change L.OffLinkFiberConstant e f at hf
    refine ⟨f, ?_⟩
    change L.singleLinkHeatBathProjection e f = f
    exact finite_lattice_singleLinkHeatBathProjection_fixes L e f hf

/-- Fixed vectors of the linear heat-bath projection are precisely the
corresponding off-link-fiber-constant observables. -/
theorem finite_lattice_singleLinkHeatBathProjectionLinearMap_fixed_iff
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjectionLinearMap e f = f ↔
      f ∈ L.offLinkFiberConstantSubmodule e := by
  change L.singleLinkHeatBathProjection e f = f ↔
    L.OffLinkFiberConstant e f
  exact finite_lattice_singleLinkHeatBathProjection_fixed_iff L e f

end

end MathlibAnalytic
end MGAP4D
