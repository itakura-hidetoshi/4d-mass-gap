import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainRawActionMemLp

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Weighted coordinates are compatible with scalar multiplication on the
completed real `ℓ²(ℕ)` carrier. -/
theorem concrete_l2_r2_weighted_coordinate_smul
    (c : ℝ) (x : ConcreteL2R1HilbertCarrier) (n : ℕ) :
    concreteL2R2WeightedCoordinate (c • x) n =
      c * concreteL2R2WeightedCoordinate x n := by
  simp only [concreteL2R2WeightedCoordinate]
  change concreteL2R2DiagonalWeight n * (c * x n) =
    c * (concreteL2R2DiagonalWeight n * x n)
  ring

/-- The dense-domain raw action is additive coordinatewise. -/
theorem concrete_l2_r2_dense_diagonal_domain_raw_action_add_apply
    (x y : concreteL2R2DenseDiagonalDomainCarrier) (n : ℕ) :
    concreteL2R2DenseDiagonalDomainRawAction (x + y) n =
      concreteL2R2DenseDiagonalDomainRawAction x n +
        concreteL2R2DenseDiagonalDomainRawAction y n := by
  simpa [concreteL2R2DenseDiagonalDomainRawAction,
    concreteL2R2DenseDiagonalDomainCarrierVal,
    concreteL2R2DiagonalRawAction] using
    concrete_l2_r2_weighted_coordinate_add
      (concreteL2R2DenseDiagonalDomainCarrierVal x)
      (concreteL2R2DenseDiagonalDomainCarrierVal y) n

/-- The dense-domain raw action is compatible with scalar multiplication
coordinatewise. -/
theorem concrete_l2_r2_dense_diagonal_domain_raw_action_smul_apply
    (c : ℝ) (x : concreteL2R2DenseDiagonalDomainCarrier) (n : ℕ) :
    concreteL2R2DenseDiagonalDomainRawAction (c • x) n =
      c * concreteL2R2DenseDiagonalDomainRawAction x n := by
  simpa [concreteL2R2DenseDiagonalDomainRawAction,
    concreteL2R2DenseDiagonalDomainCarrierVal,
    concreteL2R2DiagonalRawAction] using
    concrete_l2_r2_weighted_coordinate_smul c
      (concreteL2R2DenseDiagonalDomainCarrierVal x) n

/-- Coordinatewise additivity of the `lp`-valued dense-domain raw action. -/
theorem concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_add_apply
    (x y : concreteL2R2DenseDiagonalDomainCarrier) (n : ℕ) :
    concreteL2R2DenseDiagonalDomainLpValuedRawAction (x + y) n =
      concreteL2R2DenseDiagonalDomainLpValuedRawAction x n +
        concreteL2R2DenseDiagonalDomainLpValuedRawAction y n := by
  rw [concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply]
  rw [concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply]
  rw [concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply]
  exact concrete_l2_r2_dense_diagonal_domain_raw_action_add_apply x y n

/-- Coordinatewise scalar compatibility of the `lp`-valued dense-domain raw action. -/
theorem concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_smul_apply
    (c : ℝ) (x : concreteL2R2DenseDiagonalDomainCarrier) (n : ℕ) :
    concreteL2R2DenseDiagonalDomainLpValuedRawAction (c • x) n =
      c * concreteL2R2DenseDiagonalDomainLpValuedRawAction x n := by
  rw [concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply]
  rw [concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply]
  exact concrete_l2_r2_dense_diagonal_domain_raw_action_smul_apply c x n

/-- Dense-domain raw-action coordinate linearity surface. -/
structure ConcreteL2R2DenseDiagonalDomainRawActionLinearitySurface where
  lpValuedRawActionReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLpValuedRawActionSurfaceReady
  rawActionAddApply :
    ∀ x y : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
      concreteL2R2DenseDiagonalDomainRawAction (x + y) n =
        concreteL2R2DenseDiagonalDomainRawAction x n +
          concreteL2R2DenseDiagonalDomainRawAction y n
  rawActionSmulApply :
    ∀ c : ℝ, ∀ x : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
      concreteL2R2DenseDiagonalDomainRawAction (c • x) n =
        c * concreteL2R2DenseDiagonalDomainRawAction x n
  lpValuedActionAddApply :
    ∀ x y : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
      concreteL2R2DenseDiagonalDomainLpValuedRawAction (x + y) n =
        concreteL2R2DenseDiagonalDomainLpValuedRawAction x n +
          concreteL2R2DenseDiagonalDomainLpValuedRawAction y n
  lpValuedActionSmulApply :
    ∀ c : ℝ, ∀ x : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
      concreteL2R2DenseDiagonalDomainLpValuedRawAction (c • x) n =
        c * concreteL2R2DenseDiagonalDomainLpValuedRawAction x n
  boundaryNotBundledLinearMap : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete dense-domain raw-action coordinate linearity surface. -/
def concreteL2R2DenseDiagonalDomainRawActionLinearitySurface :
    ConcreteL2R2DenseDiagonalDomainRawActionLinearitySurface :=
  { lpValuedRawActionReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_lp_valued_raw_action_surface_ready
    rawActionAddApply := concrete_l2_r2_dense_diagonal_domain_raw_action_add_apply
    rawActionSmulApply := concrete_l2_r2_dense_diagonal_domain_raw_action_smul_apply
    lpValuedActionAddApply :=
      concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_add_apply
    lpValuedActionSmulApply :=
      concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_smul_apply
    boundaryNotBundledLinearMap := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for dense-domain raw-action coordinate linearity. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionLinearitySurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLpValuedRawActionSurfaceReady ∧
  (∀ x y : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
    concreteL2R2DenseDiagonalDomainRawAction (x + y) n =
      concreteL2R2DenseDiagonalDomainRawAction x n +
        concreteL2R2DenseDiagonalDomainRawAction y n) ∧
  (∀ c : ℝ, ∀ x : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
    concreteL2R2DenseDiagonalDomainRawAction (c • x) n =
      c * concreteL2R2DenseDiagonalDomainRawAction x n) ∧
  (∀ x y : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
    concreteL2R2DenseDiagonalDomainLpValuedRawAction (x + y) n =
      concreteL2R2DenseDiagonalDomainLpValuedRawAction x n +
        concreteL2R2DenseDiagonalDomainLpValuedRawAction y n) ∧
  (∀ c : ℝ, ∀ x : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
    concreteL2R2DenseDiagonalDomainLpValuedRawAction (c • x) n =
      c * concreteL2R2DenseDiagonalDomainLpValuedRawAction x n) ∧
  concreteL2R2DenseDiagonalDomainRawActionLinearitySurface.boundaryNotBundledLinearMap ∧
  concreteL2R2DenseDiagonalDomainRawActionLinearitySurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DenseDiagonalDomainRawActionLinearitySurface.boundaryNotSelfAdjointness

/-- The dense-domain raw-action coordinate linearity surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_raw_action_linearity_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionLinearitySurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_lp_valued_raw_action_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_raw_action_add_apply,
    concrete_l2_r2_dense_diagonal_domain_raw_action_smul_apply,
    concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_add_apply,
    concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_smul_apply,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker: coordinatewise linearity of the `lp`-valued dense-domain
action is established, but it is not yet bundled as a Mathlib `LinearMap`. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionLinearityBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionLinearitySurfaceReady

/-- Boundary theorem for dense-domain raw-action coordinate linearity. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_raw_action_linearity_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionLinearityBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_raw_action_linearity_surface_ready

end

end MathlibAnalytic
end MGAP4D
