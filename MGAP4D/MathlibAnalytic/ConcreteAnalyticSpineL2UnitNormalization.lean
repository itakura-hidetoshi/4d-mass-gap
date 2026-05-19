import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2NonPromotionIndex

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Coordinate-normalization law for the concrete unit vector.  This is the
coordinate-level precursor to the later norm-one theorem. -/
theorem concrete_l2_unit_coordinate_self (k : ℕ) :
    (concreteL2Unit k).1 k = 1 := by
  simp [concreteL2Unit, concreteL2UnitRaw]

/-- Off-coordinate vanishing law for the concrete unit vector. -/
theorem concrete_l2_unit_coordinate_off (k n : ℕ) (h : n ≠ k) :
    (concreteL2Unit k).1 n = 0 := by
  simp [concreteL2Unit, concreteL2UnitRaw, h]

/-- Square of the selected coordinate of the concrete unit vector. -/
theorem concrete_l2_unit_coordinate_square_self (k : ℕ) :
    ((concreteL2Unit k).1 k) ^ 2 = 1 := by
  simp [concrete_l2_unit_coordinate_self]

/-- Off-coordinate square vanishing law for the concrete unit vector. -/
theorem concrete_l2_unit_coordinate_square_off (k n : ℕ) (h : n ≠ k) :
    ((concreteL2Unit k).1 n) ^ 2 = 0 := by
  simp [concrete_l2_unit_coordinate_off k n h]

/-- Surface recording the coordinate-normalized unit probes.  This is not yet a
Hilbert norm-one theorem, not an operator-norm unboundedness theorem, not graph
closure, not a closed-operator theorem, and not self-adjointness. -/
structure ConcreteL2UnitNormalizationSurface where
  unitProbeReady : concreteAnalyticSpineL2UnitProbeSurfaceReady
  r2NonPromotionReady : concreteAnalyticSpineL2R2NonPromotionIndexSurfaceReady
  coordinateSelfLaw : ∀ k : ℕ, (concreteL2Unit k).1 k = 1
  coordinateOffLaw : ∀ k n : ℕ, n ≠ k → (concreteL2Unit k).1 n = 0
  coordinateSquareSelfLaw : ∀ k : ℕ, ((concreteL2Unit k).1 k) ^ 2 = 1
  coordinateSquareOffLaw : ∀ k n : ℕ, n ≠ k → ((concreteL2Unit k).1 n) ^ 2 = 0
  boundaryNotHilbertNormOneTheorem : Prop
  boundaryNotOperatorNormUnboundednessTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- The concrete coordinate-normalized unit probe surface. -/
def concreteL2UnitNormalizationSurface : ConcreteL2UnitNormalizationSurface :=
  { unitProbeReady := concrete_analytic_spine_l2_unit_probe_surface_ready
    r2NonPromotionReady :=
      concrete_analytic_spine_l2_r2_non_promotion_index_surface_ready
    coordinateSelfLaw := concrete_l2_unit_coordinate_self
    coordinateOffLaw := concrete_l2_unit_coordinate_off
    coordinateSquareSelfLaw := concrete_l2_unit_coordinate_square_self
    coordinateSquareOffLaw := concrete_l2_unit_coordinate_square_off
    boundaryNotHilbertNormOneTheorem := True
    boundaryNotOperatorNormUnboundednessTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness for the concrete coordinate-normalized unit probe surface. -/
def concreteAnalyticSpineL2UnitNormalizationSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2NonPromotionIndexSurfaceReady ∧
  (∀ k : ℕ, (concreteL2Unit k).1 k = 1) ∧
  (∀ k n : ℕ, n ≠ k → (concreteL2Unit k).1 n = 0) ∧
  concreteL2UnitNormalizationSurface.boundaryNotHilbertNormOneTheorem ∧
  concreteL2UnitNormalizationSurface.boundaryNotOperatorNormUnboundednessTheorem ∧
  concreteL2UnitNormalizationSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2UnitNormalizationSurface.boundaryNotSelfAdjointness

/-- Readiness theorem for the coordinate-normalized unit probe surface. -/
theorem concrete_analytic_spine_l2_unit_normalization_surface_ready :
    concreteAnalyticSpineL2UnitNormalizationSurfaceReady := by
  unfold concreteAnalyticSpineL2UnitNormalizationSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_non_promotion_index_surface_ready <|
      And.intro concrete_l2_unit_coordinate_self <|
        And.intro concrete_l2_unit_coordinate_off <|
          And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the coordinate-normalized unit probe surface. -/
def concreteAnalyticSpineL2UnitNormalizationHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2UnitNormalizationSurfaceReady

/-- Boundary theorem for the coordinate-normalized unit probe surface. -/
theorem concrete_analytic_spine_l2_unit_normalization_hard_residual_boundary_held :
    concreteAnalyticSpineL2UnitNormalizationHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_unit_normalization_surface_ready

end

end MathlibAnalytic
end MGAP4D
