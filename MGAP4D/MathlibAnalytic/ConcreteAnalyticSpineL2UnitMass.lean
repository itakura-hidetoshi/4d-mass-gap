import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2UnitNormalization

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

def concreteL2UnitSingletonSquaredMass (k : ℕ) : ℝ :=
  Finset.sum ({k} : Finset ℕ) (fun n => ((concreteL2Unit k).1 n) ^ 2)

theorem concrete_l2_unit_singleton_squared_mass_eq_one (k : ℕ) :
    concreteL2UnitSingletonSquaredMass k = 1 := by
  simp [concreteL2UnitSingletonSquaredMass]

theorem concrete_l2_unit_squared_mass_zero_off_singleton
    (k : ℕ) (s : Finset ℕ) (hks : k ∉ s) :
    Finset.sum s (fun n => ((concreteL2Unit k).1 n) ^ 2) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro n hn
  have hne : n ≠ k := by
    intro hnk
    exact hks (by simpa [hnk] using hn)
  exact concrete_l2_unit_coordinate_square_off k n hne

structure ConcreteL2UnitMassSurface where
  unitNormalizationReady : concreteAnalyticSpineL2UnitNormalizationSurfaceReady
  singletonSquaredMass : ℕ → ℝ
  singletonSquaredMassEqOne : ∀ k : ℕ, singletonSquaredMass k = 1
  offSingletonMassZero : ∀ k : ℕ, ∀ s : Finset ℕ, k ∉ s →
    Finset.sum s (fun n => ((concreteL2Unit k).1 n) ^ 2) = 0
  boundaryNotHilbertNormOneTheorem : Prop
  boundaryNotOperatorNormUnboundednessTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

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

def concreteAnalyticSpineL2UnitMassSurfaceReady : Prop :=
  concreteAnalyticSpineL2UnitNormalizationSurfaceReady ∧
  (∀ k : ℕ, concreteL2UnitSingletonSquaredMass k = 1) ∧
  concreteL2UnitMassSurface.boundaryNotHilbertNormOneTheorem ∧
  concreteL2UnitMassSurface.boundaryNotOperatorNormUnboundednessTheorem ∧
  concreteL2UnitMassSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2UnitMassSurface.boundaryNotSelfAdjointness

theorem concrete_analytic_spine_l2_unit_mass_surface_ready :
    concreteAnalyticSpineL2UnitMassSurfaceReady := by
  unfold concreteAnalyticSpineL2UnitMassSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_unit_normalization_surface_ready <|
      And.intro concrete_l2_unit_singleton_squared_mass_eq_one <|
        And.intro trivial <| And.intro trivial <| And.intro trivial trivial

def concreteAnalyticSpineL2UnitMassHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2UnitMassSurfaceReady

theorem concrete_analytic_spine_l2_unit_mass_hard_residual_boundary_held :
    concreteAnalyticSpineL2UnitMassHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_unit_mass_surface_ready

end

end MathlibAnalytic
end MGAP4D
