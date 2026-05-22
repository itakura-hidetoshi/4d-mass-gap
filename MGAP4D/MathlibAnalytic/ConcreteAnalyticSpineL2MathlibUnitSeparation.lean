import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibCoordinateTransport

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Distinct coordinate indices give distinct Mathlib `ℓ²(ℕ, ℝ)` unit vectors.

This is a genuine Mathlib-side separation lemma: the proof reads equality of
`lp.single` representatives at the selected coordinate and reduces it to
`1 = 0`.  It is still intentionally only a unit-vector separation surface, not
a basis theorem, dense-span theorem, operator-domain theorem, or spectral
statement. -/
theorem concrete_l2_mathlib_unit_ne_of_ne {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibUnit k ≠ concreteL2MathlibUnit n := by
  intro hEq
  have hcoord : concreteL2MathlibUnit k k = concreteL2MathlibUnit n k := by
    exact congrArg (fun f => f k) hEq
  have hleft : concreteL2MathlibUnit k k = 1 :=
    concrete_l2_mathlib_unit_apply_self k
  have hright : concreteL2MathlibUnit n k = 0 := by
    exact concrete_l2_mathlib_unit_apply_ne (k := n) (n := k) hkn
  rw [hleft, hright] at hcoord
  norm_num at hcoord

/-- The canonical coordinate-unit map `ℕ → ℓ²(ℕ, ℝ)` is injective. -/
theorem concrete_l2_mathlib_unit_injective :
    Function.Injective concreteL2MathlibUnit := by
  intro k n hEq
  by_contra hkn
  exact (concrete_l2_mathlib_unit_ne_of_ne hkn) hEq

/-- Equality of Mathlib `ℓ²` coordinate units is exactly equality of indices. -/
theorem concrete_l2_mathlib_unit_eq_iff {k n : ℕ} :
    concreteL2MathlibUnit k = concreteL2MathlibUnit n ↔ k = n := by
  constructor
  · intro hEq
    exact concrete_l2_mathlib_unit_injective hEq
  · intro hEq
    subst hEq
    rfl

/-- Adapter predicate for the coordinate-unit separation layer. -/
def concreteL2MathlibUnitSeparationAdapter : Prop :=
  Function.Injective concreteL2MathlibUnit ∧
  (∀ {k n : ℕ}, k ≠ n → concreteL2MathlibUnit k ≠ concreteL2MathlibUnit n) ∧
  (∀ {k n : ℕ}, concreteL2MathlibUnit k = concreteL2MathlibUnit n ↔ k = n)

/-- Coordinate-unit separation adapter theorem. -/
theorem concrete_l2_mathlib_unit_separation_adapter_ready :
    concreteL2MathlibUnitSeparationAdapter := by
  exact ⟨
    concrete_l2_mathlib_unit_injective,
    by intro k n hkn; exact concrete_l2_mathlib_unit_ne_of_ne hkn,
    by intro k n; exact concrete_l2_mathlib_unit_eq_iff⟩

/-- Surface for the Mathlib completed-`ℓ²` coordinate-unit separation layer.

This is the next hard-residual leaf after coordinate transport: it proves that
Mathlib's completed `ℓ²` carrier contains a countably indexed family of
coordinate-distinguishable unit vectors.  It deliberately preserves the later
obligations needed for the physical proof: no basis/dense-span claim, no finite
support domain identification, no unbounded-operator domain theorem, no
self-adjointness, no PVM, and no spectral atom claim. -/
structure ConcreteL2MathlibUnitSeparationSurface where
  coordinateTransportReady : concreteAnalyticSpineL2MathlibCoordinateTransportSurfaceReady
  separationAdapter : concreteL2MathlibUnitSeparationAdapter
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete Mathlib completed-`ℓ²` coordinate-unit separation surface. -/
def concreteL2MathlibUnitSeparationSurface :
    ConcreteL2MathlibUnitSeparationSurface :=
  { coordinateTransportReady :=
      concrete_analytic_spine_l2_mathlib_coordinate_transport_surface_ready
    separationAdapter := concrete_l2_mathlib_unit_separation_adapter_ready
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the Mathlib completed-`ℓ²` coordinate-unit separation surface. -/
def concreteAnalyticSpineL2MathlibUnitSeparationSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibCoordinateTransportSurfaceReady ∧
  concreteL2MathlibUnitSeparationAdapter ∧
  concreteL2MathlibUnitSeparationSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibUnitSeparationSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibUnitSeparationSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibUnitSeparationSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibUnitSeparationSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibUnitSeparationSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibUnitSeparationSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the Mathlib completed-`ℓ²` coordinate-unit separation surface. -/
theorem concrete_analytic_spine_l2_mathlib_unit_separation_surface_ready :
    concreteAnalyticSpineL2MathlibUnitSeparationSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibUnitSeparationSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_coordinate_transport_surface_ready <|
      And.intro concrete_l2_mathlib_unit_separation_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the Mathlib completed-`ℓ²` coordinate-unit separation surface. -/
def concreteAnalyticSpineL2MathlibUnitSeparationHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibUnitSeparationSurfaceReady

/-- Boundary theorem for the Mathlib completed-`ℓ²` coordinate-unit separation surface. -/
theorem concrete_analytic_spine_l2_mathlib_unit_separation_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibUnitSeparationHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_unit_separation_surface_ready

end

end MathlibAnalytic
end MGAP4D
