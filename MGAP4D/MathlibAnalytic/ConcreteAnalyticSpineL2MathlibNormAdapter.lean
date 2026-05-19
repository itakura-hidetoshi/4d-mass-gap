import Mathlib.Analysis.InnerProductSpace.l2Space
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2CompletedHilbertBridgeTarget

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Mathlib-side concrete unit vector in the completed Hilbert-sum space
`ℓ²(ℕ, ℝ)`.  This is the first adapter target that uses Mathlib's completed
`lp`/`l2Space` infrastructure rather than only the local subtype carrier. -/
def concreteL2MathlibUnit (k : ℕ) : lp (fun _ : ℕ => ℝ) 2 :=
  lp.single 2 k (1 : ℝ)

/-- Coordinate agreement at the selected index for the Mathlib `ℓ²` unit. -/
theorem concrete_l2_mathlib_unit_apply_self (k : ℕ) :
    concreteL2MathlibUnit k k = 1 := by
  simp [concreteL2MathlibUnit]

/-- Coordinate agreement away from the selected index for the Mathlib `ℓ²` unit. -/
theorem concrete_l2_mathlib_unit_apply_ne {k n : ℕ} (h : n ≠ k) :
    concreteL2MathlibUnit k n = 0 := by
  simp [concreteL2MathlibUnit, h]

/-- Mathlib norm theorem for the concrete `ℓ²` unit vector.  This is the point
where the local finite-support normalization is connected to Mathlib's completed
`lp` norm infrastructure. -/
theorem concrete_l2_mathlib_unit_norm_eq_one (k : ℕ) :
    ‖concreteL2MathlibUnit k‖ = 1 := by
  simp [concreteL2MathlibUnit]

/-- Adapter predicate: every concrete Mathlib-side coordinate unit has norm one
in the completed `ℓ²(ℕ, ℝ)` Hilbert-sum space. -/
def concreteL2MathlibNormTheoremAdapter : Prop :=
  ∀ k : ℕ, ‖concreteL2MathlibUnit k‖ = 1

/-- The Mathlib norm theorem adapter is discharged by the Mathlib `lp.single`
norm theorem. -/
theorem concrete_l2_mathlib_norm_theorem_adapter_ready :
    concreteL2MathlibNormTheoremAdapter := by
  exact concrete_l2_mathlib_unit_norm_eq_one

/-- Surface connecting the local finite-support normalization lane to the
Mathlib completed-`ℓ²` norm theorem.  It still does not claim that the local
subtype carrier has been definitionally identified with `lp`; that is a later
transport/equivalence proof obligation. -/
structure ConcreteL2MathlibNormAdapterSurface where
  completedHilbertBridgeTargetReady :
    concreteAnalyticSpineL2CompletedHilbertBridgeTargetSurfaceReady
  mathlibUnit : ℕ → lp (fun _ : ℕ => ℝ) 2
  coordinateSelfLaw : ∀ k : ℕ, mathlibUnit k k = 1
  coordinateOffLaw : ∀ {k n : ℕ}, n ≠ k → mathlibUnit k n = 0
  mathlibNormOneLaw : ∀ k : ℕ, ‖mathlibUnit k‖ = 1
  boundaryNotLocalSubtypeEquivalence : Prop
  boundaryNotCompletedTransportTheorem : Prop
  boundaryNotDiagonalDomainMembershipTheorem : Prop
  boundaryNotOperatorEigenvectorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete Mathlib norm adapter surface. -/
def concreteL2MathlibNormAdapterSurface : ConcreteL2MathlibNormAdapterSurface :=
  { completedHilbertBridgeTargetReady :=
      concrete_analytic_spine_l2_completed_hilbert_bridge_target_surface_ready
    mathlibUnit := concreteL2MathlibUnit
    coordinateSelfLaw := concrete_l2_mathlib_unit_apply_self
    coordinateOffLaw := by
      intro k n h
      exact concrete_l2_mathlib_unit_apply_ne h
    mathlibNormOneLaw := concrete_l2_mathlib_unit_norm_eq_one
    boundaryNotLocalSubtypeEquivalence := True
    boundaryNotCompletedTransportTheorem := True
    boundaryNotDiagonalDomainMembershipTheorem := True
    boundaryNotOperatorEigenvectorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for the Mathlib norm adapter. -/
def concreteAnalyticSpineL2MathlibNormAdapterSurfaceReady : Prop :=
  concreteAnalyticSpineL2CompletedHilbertBridgeTargetSurfaceReady ∧
  concreteL2MathlibNormTheoremAdapter ∧
  concreteL2MathlibNormAdapterSurface.boundaryNotLocalSubtypeEquivalence ∧
  concreteL2MathlibNormAdapterSurface.boundaryNotCompletedTransportTheorem ∧
  concreteL2MathlibNormAdapterSurface.boundaryNotDiagonalDomainMembershipTheorem ∧
  concreteL2MathlibNormAdapterSurface.boundaryNotOperatorEigenvectorTheorem ∧
  concreteL2MathlibNormAdapterSurface.boundaryNotSelfAdjointness

/-- Readiness theorem for the Mathlib norm adapter. -/
theorem concrete_analytic_spine_l2_mathlib_norm_adapter_surface_ready :
    concreteAnalyticSpineL2MathlibNormAdapterSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibNormAdapterSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_completed_hilbert_bridge_target_surface_ready <|
      And.intro concrete_l2_mathlib_norm_theorem_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial trivial

/-- Boundary marker for the Mathlib norm adapter. -/
def concreteAnalyticSpineL2MathlibNormAdapterHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibNormAdapterSurfaceReady

/-- Boundary theorem for the Mathlib norm adapter. -/
theorem concrete_analytic_spine_l2_mathlib_norm_adapter_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibNormAdapterHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_norm_adapter_surface_ready

end

end MathlibAnalytic
end MGAP4D
