import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainRawActionLinearity

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Additivity of the dense-domain `lp`-valued action as an equality in the
Hilbert carrier, not just coordinatewise. -/
theorem concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_add
    (x y : concreteL2R2DenseDiagonalDomainCarrier) :
    concreteL2R2DenseDiagonalDomainLpValuedRawAction (x + y) =
      concreteL2R2DenseDiagonalDomainLpValuedRawAction x +
        concreteL2R2DenseDiagonalDomainLpValuedRawAction y := by
  ext n
  simpa using
    concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_add_apply x y n

/-- Scalar compatibility of the dense-domain `lp`-valued action as an equality in
the Hilbert carrier, not just coordinatewise. -/
theorem concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_smul
    (c : ℝ) (x : concreteL2R2DenseDiagonalDomainCarrier) :
    concreteL2R2DenseDiagonalDomainLpValuedRawAction (c • x) =
      c • concreteL2R2DenseDiagonalDomainLpValuedRawAction x := by
  ext n
  simpa using
    concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_smul_apply c x n

/-- The dense-domain diagonal action bundled as a Mathlib linear map. -/
def concreteL2R2DenseDiagonalDomainLinearMap :
    concreteL2R2DenseDiagonalDomainCarrier →ₗ[ℝ] ConcreteL2R1HilbertCarrier :=
  { toFun := concreteL2R2DenseDiagonalDomainLpValuedRawAction
    map_add' := by
      intro x y
      exact concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_add x y
    map_smul' := by
      intro c x
      exact concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_smul c x }

/-- The bundled linear map evaluates to the dense-domain `lp`-valued raw action. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_apply
    (x : concreteL2R2DenseDiagonalDomainCarrier) :
    concreteL2R2DenseDiagonalDomainLinearMap x =
      concreteL2R2DenseDiagonalDomainLpValuedRawAction x := by
  rfl

/-- Coordinate law for the bundled dense-domain linear map. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_apply_coord
    (x : concreteL2R2DenseDiagonalDomainCarrier) (n : ℕ) :
    concreteL2R2DenseDiagonalDomainLinearMap x n =
      concreteL2R2WeightedCoordinate (concreteL2R2DenseDiagonalDomainCarrierVal x) n := by
  rw [concrete_l2_r2_dense_diagonal_domain_linear_map_apply]
  exact concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply_weighted x n

/-- Dense-domain bundled linear-map surface. -/
structure ConcreteL2R2DenseDiagonalDomainLinearMapSurface where
  rawActionLinearityReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionLinearitySurfaceReady
  linearMap : concreteL2R2DenseDiagonalDomainCarrier →ₗ[ℝ] ConcreteL2R1HilbertCarrier
  linearMapApply :
    ∀ x : concreteL2R2DenseDiagonalDomainCarrier,
      linearMap x = concreteL2R2DenseDiagonalDomainLpValuedRawAction x
  coordinateLaw :
    ∀ x : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
      linearMap x n =
        concreteL2R2WeightedCoordinate (concreteL2R2DenseDiagonalDomainCarrierVal x) n
  boundaryNotGraphCarrierAgreement : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete dense-domain bundled linear-map surface. -/
def concreteL2R2DenseDiagonalDomainLinearMapSurface :
    ConcreteL2R2DenseDiagonalDomainLinearMapSurface :=
  { rawActionLinearityReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_raw_action_linearity_surface_ready
    linearMap := concreteL2R2DenseDiagonalDomainLinearMap
    linearMapApply := concrete_l2_r2_dense_diagonal_domain_linear_map_apply
    coordinateLaw := concrete_l2_r2_dense_diagonal_domain_linear_map_apply_coord
    boundaryNotGraphCarrierAgreement := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for the dense-domain bundled linear-map surface. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionLinearitySurfaceReady ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier,
    concreteL2R2DenseDiagonalDomainLinearMap x =
      concreteL2R2DenseDiagonalDomainLpValuedRawAction x) ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
    concreteL2R2DenseDiagonalDomainLinearMap x n =
      concreteL2R2WeightedCoordinate (concreteL2R2DenseDiagonalDomainCarrierVal x) n) ∧
  concreteL2R2DenseDiagonalDomainLinearMapSurface.boundaryNotGraphCarrierAgreement ∧
  concreteL2R2DenseDiagonalDomainLinearMapSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DenseDiagonalDomainLinearMapSurface.boundaryNotSelfAdjointness

/-- The dense-domain bundled linear-map surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_raw_action_linearity_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_map_apply,
    concrete_l2_r2_dense_diagonal_domain_linear_map_apply_coord,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker: the dense-domain action is now a Mathlib `LinearMap`, but
its graph has not yet been identified with the existing graph carrier. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapSurfaceReady

/-- Boundary theorem for the bundled dense-domain linear-map surface. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_surface_ready

end

end MathlibAnalytic
end MGAP4D
