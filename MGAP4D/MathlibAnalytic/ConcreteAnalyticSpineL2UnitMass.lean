import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2UnitNormalization

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Finite-support squared mass of the concrete unit probe over its singleton
support.  This is the finite-support precursor to the later Hilbert norm-one
statement. -/
def concreteL2UnitSingletonSquaredMass (k : ℕ) : ℝ :=
  ∑ n in ({k} : Finset ℕ), ((concreteL2Unit k).1 n) ^ 2

/-- The singleton-support squared mass of the concrete unit probe is exactly one. -/
theorem concrete_l2_unit_singleton_squared_mass_eq_one (k : ℕ) :
    concreteL2UnitSingletonSquaredMass k = 1 := by
  simp [concreteL2UnitSingletonSquaredMass, concrete_l2_unit_coordinate_square_self]

/-- Any finite set not containing the selected coordinate contributes zero to
the squared mass of the concrete unit probe. -/
theorem concrete_l2_unit_squared_mass_zero_off_singleton
    (k : ℕ) (s : Finset ℕ) (hks : k ∉ s) :
    (∑ n in s, ((concreteL2Unit k).1 n) ^ 2) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro n hn
  have hne : n ≠ k := by
    intro hnk
    exact hks (by simpa [hnk] using hn)
  exact concrete_l2_unit_coordinate_square_off k n hne

/-- Surface recording the finite-support mass normalization of the concrete unit
probe.  This is not yet a Hilbert norm theorem, not an operator-norm
unboundedness theorem, not graph closure, not a closed-operator theorem, and not
self-adjointness. -/
structure ConcreteL2UnitMassSurface where
  unitNormalizationReady : concreteAnalyticSpineL2UnitNormalizationSurfaceReady
  singletonSquaredMass : ℕ → ℝ
  singletonSquaredMassEqOne : ∀ k : ℕ, singletonSquaredMass k = 1
  offSingletonMassZero : ∀ k : ℕ, ∀ s : Finset ℕ, k ∉ s →
    (∑ n in s, ((concreteL2Unit k).1 n) ^ 2) = 0
  boundaryNotHilbertNormOneTheorem : Prop
  boundaryNotOperatorNormUnboundednessTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- The concrete finite-support mass normalization surface. -/
def concreteL2UnitMassSurface : ConcreteL2UnitMassSurface :=
  { unitNormalizationReady :=
      concrete_analytic_spine_l2_unit_normalization_surface_ready
    singletonSquaredMass := concreteL2UnitSingletonSquaredMass
    singletonSquaredMassEqOne := concrete_l2_unit_singleton_squared_mass_eq_one
    offSingletonMassZero := concrete_l2_unit_squared_mass_zero_off_singleton
    boundaryNotHilbertNormOneTheorem := True
    boundaryNotOperatorNormUnboundednessTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness for the concrete finite-support unit mass surface. -/
def concreteAnalyticSpineL2UnitMassSurfaceReady : Prop :=
  concreteAnalyticSpineL2UnitNormalizationSurfaceReady ∧
  (∀ k : ℕ, concreteL2UnitSingletonSquaredMass k = 1) ∧
  concreteL2UnitMassSurface.boundaryNotHilbertNormOneTheorem ∧
  concreteL2UnitMassSurface.boundaryNotOperatorNormUnboundednessTheorem ∧
  concreteL2UnitMassSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2UnitMassSurface.boundaryNotSelfAdjointness

/-- Readiness theorem for the concrete finite-support unit mass surface. -/
theorem concrete_analytic_spine_l2_unit_mass_surface_ready :
    concreteAnalyticSpineL2UnitMassSurfaceReady := by
  unfold concreteAnalyticSpineL2UnitMassSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_unit_normalization_surface_ready <|
      And.intro concrete_l2_unit_singleton_squared_mass_eq_one <|
        And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the concrete finite-support unit mass surface. -/
def concreteAnalyticSpineL2UnitMassHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2UnitMassSurfaceReady

/-- Boundary theorem for the concrete finite-support unit mass surface. -/
theorem concrete_analytic_spine_l2_unit_mass_hard_residual_boundary_held :
    concreteAnalyticSpineL2UnitMassHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_unit_mass_surface_ready

end

end MathlibAnalytic
end MGAP4D
