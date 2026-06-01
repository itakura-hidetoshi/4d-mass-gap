import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainRawActionSummability

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Norm-rpow form of square summability for the dense-domain raw action.

Mathlib's `Memℓp` predicate expects `Summable fun i => ‖f i‖ ^ p.toReal`,
so this normalizes the previously proved real-square summability into exactly
that shape for `p = 2`. -/
theorem concrete_l2_r2_dense_diagonal_domain_raw_action_norm_rpow_summable
    (x : concreteL2R2DenseDiagonalDomainCarrier) :
    Summable fun n : ℕ =>
      ‖concreteL2R2DenseDiagonalDomainRawAction x n‖ ^ (2 : ℝ≥0∞).toReal := by
  simpa [Real.norm_eq_abs, sq_abs] using
    concrete_l2_r2_dense_diagonal_domain_raw_action_square_summable x

/-- Norm-rpow form of square summability for the dense-domain weighted-coordinate action. -/
theorem concrete_l2_r2_dense_diagonal_domain_weighted_coordinate_norm_rpow_summable
    (x : concreteL2R2DenseDiagonalDomainCarrier) :
    Summable fun n : ℕ =>
      ‖concreteL2R2WeightedCoordinate
          (concreteL2R2DenseDiagonalDomainCarrierVal x) n‖ ^ (2 : ℝ≥0∞).toReal := by
  simpa [Real.norm_eq_abs, sq_abs] using
    concrete_l2_r2_dense_diagonal_domain_weighted_coordinate_square_summable x

/-- The dense-domain raw action satisfies Mathlib's `Memℓp` predicate for `p = 2`.

This is the precise Mathlib subtype-membership datum needed to build an element
of `lp (fun _ : ℕ => ℝ) 2`. -/
theorem concrete_l2_r2_dense_diagonal_domain_raw_action_memℓp
    (x : concreteL2R2DenseDiagonalDomainCarrier) :
    Memℓp (concreteL2R2DenseDiagonalDomainRawAction x) (2 : ℝ≥0∞) := by
  exact memℓp_gen
    (concrete_l2_r2_dense_diagonal_domain_raw_action_norm_rpow_summable x)

/-- The weighted-coordinate raw action satisfies Mathlib's `Memℓp` predicate for
`p = 2`. -/
theorem concrete_l2_r2_dense_diagonal_domain_weighted_coordinate_memℓp
    (x : concreteL2R2DenseDiagonalDomainCarrier) :
    Memℓp
      (fun n : ℕ =>
        concreteL2R2WeightedCoordinate
          (concreteL2R2DenseDiagonalDomainCarrierVal x) n)
      (2 : ℝ≥0∞) := by
  exact memℓp_gen
    (concrete_l2_r2_dense_diagonal_domain_weighted_coordinate_norm_rpow_summable x)

/-- The dense-domain raw action as a Mathlib `lp` value. -/
def concreteL2R2DenseDiagonalDomainLpValuedRawAction
    (x : concreteL2R2DenseDiagonalDomainCarrier) : ConcreteL2R1HilbertCarrier :=
  ⟨concreteL2R2DenseDiagonalDomainRawAction x,
    concrete_l2_r2_dense_diagonal_domain_raw_action_memℓp x⟩

/-- Coordinate evaluation of the `lp`-valued raw action is the raw action. -/
theorem concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply
    (x : concreteL2R2DenseDiagonalDomainCarrier) (n : ℕ) :
    concreteL2R2DenseDiagonalDomainLpValuedRawAction x n =
      concreteL2R2DenseDiagonalDomainRawAction x n := by
  rfl

/-- Coordinate evaluation of the `lp`-valued raw action is the weighted-coordinate formula. -/
theorem concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply_weighted
    (x : concreteL2R2DenseDiagonalDomainCarrier) (n : ℕ) :
    concreteL2R2DenseDiagonalDomainLpValuedRawAction x n =
      concreteL2R2WeightedCoordinate (concreteL2R2DenseDiagonalDomainCarrierVal x) n := by
  rw [concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply]
  exact concrete_l2_r2_dense_diagonal_domain_raw_action_eq_weighted x n

/-- Dense-domain `lp`-valued action surface. -/
structure ConcreteL2R2DenseDiagonalDomainLpValuedRawActionSurface where
  rawActionSummabilityReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionSummabilitySurfaceReady
  lpValuedAction : concreteL2R2DenseDiagonalDomainCarrier → ConcreteL2R1HilbertCarrier
  rawActionNormRpowSummable :
    ∀ x : concreteL2R2DenseDiagonalDomainCarrier,
      Summable fun n : ℕ =>
        ‖concreteL2R2DenseDiagonalDomainRawAction x n‖ ^ (2 : ℝ≥0∞).toReal
  rawActionMemLp :
    ∀ x : concreteL2R2DenseDiagonalDomainCarrier,
      Memℓp (concreteL2R2DenseDiagonalDomainRawAction x) (2 : ℝ≥0∞)
  coordinateLaw :
    ∀ x : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
      lpValuedAction x n = concreteL2R2DenseDiagonalDomainRawAction x n
  weightedCoordinateLaw :
    ∀ x : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
      lpValuedAction x n =
        concreteL2R2WeightedCoordinate (concreteL2R2DenseDiagonalDomainCarrierVal x) n
  boundaryNotLinearMap : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete dense-domain `lp`-valued action surface. -/
def concreteL2R2DenseDiagonalDomainLpValuedRawActionSurface :
    ConcreteL2R2DenseDiagonalDomainLpValuedRawActionSurface :=
  { rawActionSummabilityReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_raw_action_summability_surface_ready
    lpValuedAction := concreteL2R2DenseDiagonalDomainLpValuedRawAction
    rawActionNormRpowSummable :=
      concrete_l2_r2_dense_diagonal_domain_raw_action_norm_rpow_summable
    rawActionMemLp := concrete_l2_r2_dense_diagonal_domain_raw_action_memℓp
    coordinateLaw := concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply
    weightedCoordinateLaw :=
      concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply_weighted
    boundaryNotLinearMap := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for the dense-domain `lp`-valued action surface. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLpValuedRawActionSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionSummabilitySurfaceReady ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier,
    Summable fun n : ℕ =>
      ‖concreteL2R2DenseDiagonalDomainRawAction x n‖ ^ (2 : ℝ≥0∞).toReal) ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier,
    Memℓp (concreteL2R2DenseDiagonalDomainRawAction x) (2 : ℝ≥0∞)) ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
    concreteL2R2DenseDiagonalDomainLpValuedRawAction x n =
      concreteL2R2DenseDiagonalDomainRawAction x n) ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier, ∀ n : ℕ,
    concreteL2R2DenseDiagonalDomainLpValuedRawAction x n =
      concreteL2R2WeightedCoordinate (concreteL2R2DenseDiagonalDomainCarrierVal x) n) ∧
  concreteL2R2DenseDiagonalDomainLpValuedRawActionSurface.boundaryNotLinearMap ∧
  concreteL2R2DenseDiagonalDomainLpValuedRawActionSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DenseDiagonalDomainLpValuedRawActionSurface.boundaryNotSelfAdjointness

/-- The dense-domain `lp`-valued action surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_lp_valued_raw_action_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLpValuedRawActionSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_raw_action_summability_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_raw_action_norm_rpow_summable,
    concrete_l2_r2_dense_diagonal_domain_raw_action_memℓp,
    concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply,
    concrete_l2_r2_dense_diagonal_domain_lp_valued_raw_action_apply_weighted,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker: the dense-domain action is now `lp`-valued, but has not yet
been promoted to a linear map on the dense domain submodule. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLpValuedRawActionBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLpValuedRawActionSurfaceReady

/-- Boundary theorem for the dense-domain `lp`-valued action surface. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_lp_valued_raw_action_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLpValuedRawActionBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_lp_valued_raw_action_surface_ready

end

end MathlibAnalytic
end MGAP4D
