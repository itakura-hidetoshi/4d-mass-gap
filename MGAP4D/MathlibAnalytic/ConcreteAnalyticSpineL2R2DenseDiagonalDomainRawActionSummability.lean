import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainCarrierBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The raw diagonal action on the promoted dense-domain carrier is square
summable.

This is the exact analytic datum needed before packaging the raw action as a
Mathlib `lp`-valued vector.  It is not merely a boundary packet: it transports
the original domain-candidate summability proof to the dense-submodule carrier. -/
theorem concrete_l2_r2_dense_diagonal_domain_raw_action_square_summable
    (x : concreteL2R2DenseDiagonalDomainCarrier) :
    Summable fun n : ℕ => (concreteL2R2DenseDiagonalDomainRawAction x n) ^ 2 := by
  have hx :
      ConcreteL2R2DiagonalDomainCandidate
        (concreteL2R2DenseDiagonalDomainCarrierVal x) :=
    concrete_l2_r2_dense_diagonal_domain_carrier_mem_candidate x
  unfold ConcreteL2R2DiagonalDomainCandidate at hx
  simpa [concreteL2R2DenseDiagonalDomainRawAction, concreteL2R2DiagonalRawAction] using hx

/-- The raw diagonal action has the same square-summability statement when
rewritten by the weighted-coordinate formula. -/
theorem concrete_l2_r2_dense_diagonal_domain_weighted_coordinate_square_summable
    (x : concreteL2R2DenseDiagonalDomainCarrier) :
    Summable fun n : ℕ =>
      (concreteL2R2WeightedCoordinate
        (concreteL2R2DenseDiagonalDomainCarrierVal x) n) ^ 2 := by
  exact concrete_l2_r2_dense_diagonal_domain_carrier_mem_candidate x

/-- Dense-domain raw-action summability surface. -/
structure ConcreteL2R2DenseDiagonalDomainRawActionSummabilitySurface where
  carrierBridgeReady : concreteAnalyticSpineL2R2DenseDiagonalDomainCarrierBridgeSurfaceReady
  rawActionSquareSummable :
    ∀ x : concreteL2R2DenseDiagonalDomainCarrier,
      Summable fun n : ℕ => (concreteL2R2DenseDiagonalDomainRawAction x n) ^ 2
  weightedCoordinateSquareSummable :
    ∀ x : concreteL2R2DenseDiagonalDomainCarrier,
      Summable fun n : ℕ =>
        (concreteL2R2WeightedCoordinate
          (concreteL2R2DenseDiagonalDomainCarrierVal x) n) ^ 2
  boundaryNotLpValuedAction : Prop
  boundaryNotLinearMap : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete dense-domain raw-action summability surface. -/
def concreteL2R2DenseDiagonalDomainRawActionSummabilitySurface :
    ConcreteL2R2DenseDiagonalDomainRawActionSummabilitySurface :=
  { carrierBridgeReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_carrier_bridge_surface_ready
    rawActionSquareSummable :=
      concrete_l2_r2_dense_diagonal_domain_raw_action_square_summable
    weightedCoordinateSquareSummable :=
      concrete_l2_r2_dense_diagonal_domain_weighted_coordinate_square_summable
    boundaryNotLpValuedAction := True
    boundaryNotLinearMap := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for dense-domain raw-action summability. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionSummabilitySurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainCarrierBridgeSurfaceReady ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier,
    Summable fun n : ℕ => (concreteL2R2DenseDiagonalDomainRawAction x n) ^ 2) ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier,
    Summable fun n : ℕ =>
      (concreteL2R2WeightedCoordinate
        (concreteL2R2DenseDiagonalDomainCarrierVal x) n) ^ 2) ∧
  concreteL2R2DenseDiagonalDomainRawActionSummabilitySurface.boundaryNotLpValuedAction ∧
  concreteL2R2DenseDiagonalDomainRawActionSummabilitySurface.boundaryNotLinearMap ∧
  concreteL2R2DenseDiagonalDomainRawActionSummabilitySurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DenseDiagonalDomainRawActionSummabilitySurface.boundaryNotSelfAdjointness

/-- The dense-domain raw-action summability surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_raw_action_summability_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionSummabilitySurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_carrier_bridge_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_raw_action_square_summable,
    concrete_l2_r2_dense_diagonal_domain_weighted_coordinate_square_summable,
    trivial,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker: raw action square-summability has been transported to the
dense-domain carrier, but the action is not yet packaged as an `lp`-valued map. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionSummabilityBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionSummabilitySurfaceReady

/-- Boundary theorem for the dense-domain raw-action summability surface. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_raw_action_summability_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainRawActionSummabilityBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_raw_action_summability_surface_ready

end

end MathlibAnalytic
end MGAP4D
