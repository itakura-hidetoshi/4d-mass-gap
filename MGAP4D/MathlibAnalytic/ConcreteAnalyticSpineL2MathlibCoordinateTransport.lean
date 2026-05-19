import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2UnitNormalization
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibNormAdapter

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Coordinate-level transport from the local finite-support unit vector to the
Mathlib completed `ℓ²(ℕ, ℝ)` unit vector.  This is intentionally only a
coordinate equality theorem; it is not yet a global linear isometry or subtype
quotient/equivalence theorem. -/
theorem concrete_l2_unit_to_mathlib_coordinate_transport (k n : ℕ) :
    (concreteL2Unit k).1 n = concreteL2MathlibUnit k n := by
  classical
  by_cases h : n = k
  · subst h
    simp [concrete_l2_unit_coordinate_self, concrete_l2_mathlib_unit_apply_self]
  · simp [concrete_l2_unit_coordinate_off k n h, concrete_l2_mathlib_unit_apply_ne h]

/-- Selected-coordinate transport. -/
theorem concrete_l2_unit_to_mathlib_coordinate_transport_self (k : ℕ) :
    (concreteL2Unit k).1 k = concreteL2MathlibUnit k k := by
  exact concrete_l2_unit_to_mathlib_coordinate_transport k k

/-- Off-coordinate transport. -/
theorem concrete_l2_unit_to_mathlib_coordinate_transport_off (k n : ℕ) (h : n ≠ k) :
    (concreteL2Unit k).1 n = concreteL2MathlibUnit k n := by
  simp [concrete_l2_unit_coordinate_off k n h, concrete_l2_mathlib_unit_apply_ne h]

/-- Transported local unit norm theorem: the local unit has a Mathlib-side norm-one
witness after coordinate transport to `lp.single`.  The norm itself is still the
Mathlib completed-`ℓ²` norm of the transported representative, not a newly claimed
local subtype norm theorem. -/
theorem concrete_l2_unit_transported_mathlib_norm_eq_one (k : ℕ) :
    ‖concreteL2MathlibUnit k‖ = 1 := by
  exact concrete_l2_mathlib_unit_norm_eq_one k

/-- Adapter predicate for coordinate transport into Mathlib completed `ℓ²`. -/
def concreteL2MathlibCoordinateTransportAdapter : Prop :=
  (∀ k n : ℕ, (concreteL2Unit k).1 n = concreteL2MathlibUnit k n) ∧
  (∀ k : ℕ, ‖concreteL2MathlibUnit k‖ = 1)

/-- Coordinate transport adapter theorem. -/
theorem concrete_l2_mathlib_coordinate_transport_adapter_ready :
    concreteL2MathlibCoordinateTransportAdapter := by
  exact And.intro concrete_l2_unit_to_mathlib_coordinate_transport
    concrete_l2_unit_transported_mathlib_norm_eq_one

/-- Surface for the local-to-Mathlib coordinate transport.  This closes the
coordinate agreement of the unit probes with Mathlib's `lp.single` representatives,
while preserving all hard boundaries that would require stronger equivalence,
domain, operator, and spectral proofs. -/
structure ConcreteL2MathlibCoordinateTransportSurface where
  unitNormalizationReady : concreteAnalyticSpineL2UnitNormalizationSurfaceReady
  mathlibNormAdapterReady : concreteAnalyticSpineL2MathlibNormAdapterSurfaceReady
  coordinateTransportLaw : ∀ k n : ℕ,
    (concreteL2Unit k).1 n = concreteL2MathlibUnit k n
  transportedNormOneLaw : ∀ k : ℕ, ‖concreteL2MathlibUnit k‖ = 1
  boundaryNotLocalSubtypeEquivalence : Prop
  boundaryNotLinearIsometryEquivalence : Prop
  boundaryNotCompletedTransportTheorem : Prop
  boundaryNotDiagonalDomainMembershipTheorem : Prop
  boundaryNotOperatorEigenvectorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop

/-- Concrete local-to-Mathlib coordinate transport surface. -/
def concreteL2MathlibCoordinateTransportSurface :
    ConcreteL2MathlibCoordinateTransportSurface :=
  { unitNormalizationReady := concrete_analytic_spine_l2_unit_normalization_surface_ready
    mathlibNormAdapterReady := concrete_analytic_spine_l2_mathlib_norm_adapter_surface_ready
    coordinateTransportLaw := concrete_l2_unit_to_mathlib_coordinate_transport
    transportedNormOneLaw := concrete_l2_unit_transported_mathlib_norm_eq_one
    boundaryNotLocalSubtypeEquivalence := True
    boundaryNotLinearIsometryEquivalence := True
    boundaryNotCompletedTransportTheorem := True
    boundaryNotDiagonalDomainMembershipTheorem := True
    boundaryNotOperatorEigenvectorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True }

/-- Readiness for the local-to-Mathlib coordinate transport surface. -/
def concreteAnalyticSpineL2MathlibCoordinateTransportSurfaceReady : Prop :=
  concreteAnalyticSpineL2UnitNormalizationSurfaceReady ∧
  concreteAnalyticSpineL2MathlibNormAdapterSurfaceReady ∧
  concreteL2MathlibCoordinateTransportAdapter ∧
  concreteL2MathlibCoordinateTransportSurface.boundaryNotLocalSubtypeEquivalence ∧
  concreteL2MathlibCoordinateTransportSurface.boundaryNotLinearIsometryEquivalence ∧
  concreteL2MathlibCoordinateTransportSurface.boundaryNotCompletedTransportTheorem ∧
  concreteL2MathlibCoordinateTransportSurface.boundaryNotDiagonalDomainMembershipTheorem ∧
  concreteL2MathlibCoordinateTransportSurface.boundaryNotOperatorEigenvectorTheorem ∧
  concreteL2MathlibCoordinateTransportSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibCoordinateTransportSurface.boundaryNotSpectralTheoremApplication

/-- Readiness theorem for the local-to-Mathlib coordinate transport surface. -/
theorem concrete_analytic_spine_l2_mathlib_coordinate_transport_surface_ready :
    concreteAnalyticSpineL2MathlibCoordinateTransportSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibCoordinateTransportSurfaceReady
  exact And.intro concrete_analytic_spine_l2_unit_normalization_surface_ready <|
    And.intro concrete_analytic_spine_l2_mathlib_norm_adapter_surface_ready <|
      And.intro concrete_l2_mathlib_coordinate_transport_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the local-to-Mathlib coordinate transport surface. -/
def concreteAnalyticSpineL2MathlibCoordinateTransportHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibCoordinateTransportSurfaceReady

/-- Boundary theorem for the local-to-Mathlib coordinate transport surface. -/
theorem concrete_analytic_spine_l2_mathlib_coordinate_transport_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibCoordinateTransportHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_coordinate_transport_surface_ready

end

end MathlibAnalytic
end MGAP4D