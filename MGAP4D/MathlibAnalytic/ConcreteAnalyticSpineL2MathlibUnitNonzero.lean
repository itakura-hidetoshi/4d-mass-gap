import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibUnitSeparation

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Each Mathlib completed-`ℓ²(ℕ, ℝ)` coordinate unit is nonzero.

The proof is purely coordinate-level: evaluating a hypothetical equality
`e_k = 0` at coordinate `k` turns the already proved self-coordinate law into
`1 = 0`. -/
theorem concrete_l2_mathlib_unit_ne_zero (k : ℕ) :
    concreteL2MathlibUnit k ≠ 0 := by
  intro hzero
  have hcoord : concreteL2MathlibUnit k k = (0 : lp (fun _ : ℕ => ℝ) 2) k := by
    exact congrArg (fun f => f k) hzero
  have hleft : concreteL2MathlibUnit k k = 1 :=
    concrete_l2_mathlib_unit_apply_self k
  have hright : (0 : lp (fun _ : ℕ => ℝ) 2) k = 0 := rfl
  rw [hleft, hright] at hcoord
  norm_num at hcoord

/-- The selected coordinate of each unit vector is nonzero. -/
theorem concrete_l2_mathlib_unit_self_ne_zero (k : ℕ) :
    concreteL2MathlibUnit k k ≠ 0 := by
  rw [concrete_l2_mathlib_unit_apply_self]
  norm_num

/-- Each coordinate unit is separated from the zero vector by its selected
coordinate. -/
theorem concrete_l2_mathlib_unit_zero_separation (k : ℕ) :
    concreteL2MathlibUnit k ≠ (0 : lp (fun _ : ℕ => ℝ) 2) := by
  exact concrete_l2_mathlib_unit_ne_zero k

/-- Adapter predicate for the coordinate-unit nonzero layer. -/
def concreteL2MathlibUnitNonzeroAdapter : Prop :=
  (∀ k : ℕ, concreteL2MathlibUnit k ≠ 0) ∧
  (∀ k : ℕ, concreteL2MathlibUnit k k ≠ 0) ∧
  (∀ k : ℕ, concreteL2MathlibUnit k ≠ (0 : lp (fun _ : ℕ => ℝ) 2))

/-- Coordinate-unit nonzero adapter theorem. -/
theorem concrete_l2_mathlib_unit_nonzero_adapter_ready :
    concreteL2MathlibUnitNonzeroAdapter := by
  exact ⟨
    concrete_l2_mathlib_unit_ne_zero,
    concrete_l2_mathlib_unit_self_ne_zero,
    concrete_l2_mathlib_unit_zero_separation⟩

/-- Surface for the Mathlib completed-`ℓ²` coordinate-unit nonzero layer.

This strengthens the carrier lane after coordinate-unit separation: every
canonical coordinate unit is provably nonzero in Mathlib's completed `lp`
carrier.  It deliberately remains below basis, dense-span, finite-support-domain,
unbounded-operator, self-adjoint, PVM, and spectral-atom claims. -/
structure ConcreteL2MathlibUnitNonzeroSurface where
  unitSeparationReady : concreteAnalyticSpineL2MathlibUnitSeparationSurfaceReady
  nonzeroAdapter : concreteL2MathlibUnitNonzeroAdapter
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete Mathlib completed-`ℓ²` coordinate-unit nonzero surface. -/
def concreteL2MathlibUnitNonzeroSurface :
    ConcreteL2MathlibUnitNonzeroSurface :=
  { unitSeparationReady :=
      concrete_analytic_spine_l2_mathlib_unit_separation_surface_ready
    nonzeroAdapter := concrete_l2_mathlib_unit_nonzero_adapter_ready
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the Mathlib completed-`ℓ²` coordinate-unit nonzero surface. -/
def concreteAnalyticSpineL2MathlibUnitNonzeroSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibUnitSeparationSurfaceReady ∧
  concreteL2MathlibUnitNonzeroAdapter ∧
  concreteL2MathlibUnitNonzeroSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibUnitNonzeroSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibUnitNonzeroSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibUnitNonzeroSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibUnitNonzeroSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibUnitNonzeroSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibUnitNonzeroSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the Mathlib completed-`ℓ²` coordinate-unit nonzero surface. -/
theorem concrete_analytic_spine_l2_mathlib_unit_nonzero_surface_ready :
    concreteAnalyticSpineL2MathlibUnitNonzeroSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibUnitNonzeroSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_unit_separation_surface_ready <|
      And.intro concrete_l2_mathlib_unit_nonzero_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the Mathlib completed-`ℓ²` coordinate-unit nonzero surface. -/
def concreteAnalyticSpineL2MathlibUnitNonzeroHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibUnitNonzeroSurfaceReady

/-- Boundary theorem for the Mathlib completed-`ℓ²` coordinate-unit nonzero surface. -/
theorem concrete_analytic_spine_l2_mathlib_unit_nonzero_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibUnitNonzeroHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_unit_nonzero_surface_ready

end

end MathlibAnalytic
end MGAP4D
