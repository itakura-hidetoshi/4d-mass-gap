import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeUnitCoordinates

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- A concrete support-containment predicate for Mathlib completed `ℓ²(ℕ, ℝ)`.

This is intentionally weaker than a `Finsupp` equivalence: it only records that a
vector vanishes outside the two selected coordinate indices. -/
def concreteL2MathlibSupportedOnTwo (k n : ℕ)
    (v : lp (fun _ : ℕ => ℝ) 2) : Prop :=
  ∀ j : ℕ, j ≠ k → j ≠ n → v j = 0

/-- The first selected coordinate unit is supported on `{k,n}`. -/
theorem concrete_l2_mathlib_first_unit_supported_on_two
    (k n : ℕ) :
    concreteL2MathlibSupportedOnTwo k n (concreteL2MathlibUnit k) := by
  intro j hjk _hjn
  exact concrete_l2_mathlib_unit_apply_ne (k := k) (n := j) hjk

/-- The second selected coordinate unit is supported on `{k,n}`. -/
theorem concrete_l2_mathlib_second_unit_supported_on_two
    (k n : ℕ) :
    concreteL2MathlibSupportedOnTwo k n (concreteL2MathlibUnit n) := by
  intro j _hjk hjn
  exact concrete_l2_mathlib_unit_apply_ne (k := n) (n := j) hjn

/-- The explicit two-term combination associated to a `Fin 2` coefficient vector
is supported on the two selected indices. -/
theorem concrete_l2_mathlib_fin_two_unit_explicit_supported_on_two
    (k n : ℕ) (c : Fin 2 → ℝ) :
    concreteL2MathlibSupportedOnTwo k n
      (c 0 • concreteL2MathlibUnit k + c 1 • concreteL2MathlibUnit n) := by
  intro j hjk hjn
  have hk0 : concreteL2MathlibUnit k j = 0 :=
    concrete_l2_mathlib_unit_apply_ne (k := k) (n := j) hjk
  have hn0 : concreteL2MathlibUnit n j = 0 :=
    concrete_l2_mathlib_unit_apply_ne (k := n) (n := j) hjn
  have hleft : (c 0 • concreteL2MathlibUnit k : lp (fun _ : ℕ => ℝ) 2) j = 0 := by
    simpa [hk0]
  have hright : (c 1 • concreteL2MathlibUnit n : lp (fun _ : ℕ => ℝ) 2) j = 0 := by
    simpa [hn0]
  change (c 0 • concreteL2MathlibUnit k : lp (fun _ : ℕ => ℝ) 2) j +
      (c 1 • concreteL2MathlibUnit n : lp (fun _ : ℕ => ℝ) 2) j = 0
  simp [hleft, hright]

/-- The named two-unit synthesis vector is supported on the two selected indices. -/
theorem concrete_l2_mathlib_fin_two_unit_synthesis_supported_on_two
    (k n : ℕ) (c : Fin 2 → ℝ) :
    concreteL2MathlibSupportedOnTwo k n
      (concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c) := by
  intro j hjk hjn
  have hsum :
      concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c =
        c 0 • concreteL2MathlibUnit k + c 1 • concreteL2MathlibUnit n := by
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_apply_eq_sum]
    rw [Fin.sum_univ_two]
    rfl
  have hsupp := concrete_l2_mathlib_fin_two_unit_explicit_supported_on_two k n c
  rw [hsum]
  exact hsupp j hjk hjn

/-- Every range vector of the two-unit synthesis map is supported on the two
selected indices. -/
theorem concrete_l2_mathlib_fin_two_unit_range_supported_on_two
    (k n : ℕ) (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    concreteL2MathlibSupportedOnTwo k n (v : lp (fun _ : ℕ => ℝ) 2) := by
  rcases v.property with ⟨c, hc⟩
  rw [← hc]
  exact concrete_l2_mathlib_fin_two_unit_synthesis_supported_on_two k n c

/-- Adapter predicate for the two-unit finite-support-style containment bridge. -/
def concreteL2MathlibFinTwoUnitSupportContainmentAdapter : Prop :=
  (∀ k n : ℕ, concreteL2MathlibSupportedOnTwo k n (concreteL2MathlibUnit k)) ∧
  (∀ k n : ℕ, concreteL2MathlibSupportedOnTwo k n (concreteL2MathlibUnit n)) ∧
  (∀ k n : ℕ, ∀ c : Fin 2 → ℝ,
    concreteL2MathlibSupportedOnTwo k n
      (concreteL2MathlibFinTwoUnitSynthesisLinearMap k n c)) ∧
  (∀ k n : ℕ, ∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
    concreteL2MathlibSupportedOnTwo k n (v : lp (fun _ : ℕ => ℝ) 2))

/-- Adapter theorem for the two-unit finite-support-style containment bridge. -/
theorem concrete_l2_mathlib_fin_two_unit_support_containment_adapter_ready :
    concreteL2MathlibFinTwoUnitSupportContainmentAdapter := by
  exact ⟨
    concrete_l2_mathlib_first_unit_supported_on_two,
    concrete_l2_mathlib_second_unit_supported_on_two,
    concrete_l2_mathlib_fin_two_unit_synthesis_supported_on_two,
    concrete_l2_mathlib_fin_two_unit_range_supported_on_two⟩

/-- Surface for the two-unit finite-support-style containment bridge.

This is the first bridge from the completed `ℓ²` two-unit range chain toward a
finite-support domain reading: every synthesized vector vanishes outside the two
selected coordinates.  It deliberately does not identify the range with
`Finsupp`, does not prove dense span, and does not open any unbounded-operator,
self-adjointness, PVM, spectral atom, or spectral weight claim. -/
structure ConcreteL2MathlibFinTwoUnitSupportContainmentSurface where
  rangeUnitCoordinatesReady :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeUnitCoordinatesSurfaceReady
  supportContainmentAdapter : concreteL2MathlibFinTwoUnitSupportContainmentAdapter
  boundaryNotFinsuppEquivalence : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotSpectralWeightTheorem : Prop

/-- Concrete two-unit finite-support-style containment bridge. -/
def concreteL2MathlibFinTwoUnitSupportContainmentSurface :
    ConcreteL2MathlibFinTwoUnitSupportContainmentSurface :=
  { rangeUnitCoordinatesReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_unit_coordinates_surface_ready
    supportContainmentAdapter :=
      concrete_l2_mathlib_fin_two_unit_support_containment_adapter_ready
    boundaryNotFinsuppEquivalence := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotSpectralWeightTheorem := True }

/-- Readiness for the two-unit finite-support-style containment bridge. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitSupportContainmentSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeUnitCoordinatesSurfaceReady ∧
  concreteL2MathlibFinTwoUnitSupportContainmentAdapter ∧
  concreteL2MathlibFinTwoUnitSupportContainmentSurface.boundaryNotFinsuppEquivalence ∧
  concreteL2MathlibFinTwoUnitSupportContainmentSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitSupportContainmentSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitSupportContainmentSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitSupportContainmentSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitSupportContainmentSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinTwoUnitSupportContainmentSurface.boundaryNotSpectralWeightTheorem

/-- Readiness theorem for the two-unit finite-support-style containment bridge. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_support_containment_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitSupportContainmentSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitSupportContainmentSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_unit_coordinates_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_support_containment_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the two-unit finite-support-style containment bridge. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitSupportContainmentHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitSupportContainmentSurfaceReady

/-- Boundary theorem for the two-unit finite-support-style containment bridge. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_support_containment_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitSupportContainmentHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_support_containment_surface_ready

end

end MathlibAnalytic
end MGAP4D
