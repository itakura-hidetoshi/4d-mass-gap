import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibUnitNonzero

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Distinct Mathlib completed-`ℓ²(ℕ, ℝ)` coordinate units have nonzero
difference.

This is the additive separation form of the previous injectivity theorem:
`e_k - e_n = 0` would imply `e_k = e_n`, hence `k = n`, contradicting the
index separation hypothesis. -/
theorem concrete_l2_mathlib_unit_sub_ne_zero {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibUnit k - concreteL2MathlibUnit n ≠ 0 := by
  intro hsub
  have hEq : concreteL2MathlibUnit k = concreteL2MathlibUnit n := by
    exact sub_eq_zero.mp hsub
  exact hkn (concrete_l2_mathlib_unit_injective hEq)

/-- The norm of the difference of two distinct coordinate units is nonzero. -/
theorem concrete_l2_mathlib_unit_norm_sub_ne_zero {k n : ℕ} (hkn : k ≠ n) :
    ‖concreteL2MathlibUnit k - concreteL2MathlibUnit n‖ ≠ 0 := by
  intro hnorm
  have hsub : concreteL2MathlibUnit k - concreteL2MathlibUnit n = 0 := by
    exact norm_eq_zero.mp hnorm
  exact concrete_l2_mathlib_unit_sub_ne_zero hkn hsub

/-- The norm-distance between distinct coordinate units is strictly positive. -/
theorem concrete_l2_mathlib_unit_norm_sub_pos {k n : ℕ} (hkn : k ≠ n) :
    0 < ‖concreteL2MathlibUnit k - concreteL2MathlibUnit n‖ := by
  exact norm_pos_iff.mpr (concrete_l2_mathlib_unit_sub_ne_zero hkn)

/-- Distinct coordinate units are separated by positive metric distance. -/
theorem concrete_l2_mathlib_unit_dist_pos {k n : ℕ} (hkn : k ≠ n) :
    0 < dist (concreteL2MathlibUnit k) (concreteL2MathlibUnit n) := by
  exact dist_pos.mpr (concrete_l2_mathlib_unit_ne_of_ne hkn)

/-- Adapter predicate for pairwise coordinate-unit separation. -/
def concreteL2MathlibUnitPairSeparationAdapter : Prop :=
  (∀ {k n : ℕ}, k ≠ n → concreteL2MathlibUnit k - concreteL2MathlibUnit n ≠ 0) ∧
  (∀ {k n : ℕ}, k ≠ n → ‖concreteL2MathlibUnit k - concreteL2MathlibUnit n‖ ≠ 0) ∧
  (∀ {k n : ℕ}, k ≠ n → 0 < ‖concreteL2MathlibUnit k - concreteL2MathlibUnit n‖) ∧
  (∀ {k n : ℕ}, k ≠ n → 0 < dist (concreteL2MathlibUnit k) (concreteL2MathlibUnit n))

/-- Pairwise coordinate-unit separation adapter theorem. -/
theorem concrete_l2_mathlib_unit_pair_separation_adapter_ready :
    concreteL2MathlibUnitPairSeparationAdapter := by
  exact ⟨
    by intro k n hkn; exact concrete_l2_mathlib_unit_sub_ne_zero hkn,
    by intro k n hkn; exact concrete_l2_mathlib_unit_norm_sub_ne_zero hkn,
    by intro k n hkn; exact concrete_l2_mathlib_unit_norm_sub_pos hkn,
    by intro k n hkn; exact concrete_l2_mathlib_unit_dist_pos hkn⟩

/-- Surface for pairwise separation of the Mathlib completed-`ℓ²` coordinate
units.

This layer upgrades index separation and nonzeroness to additive and metric
separation: distinct coordinate units have nonzero difference, positive norm of
that difference, and positive metric distance.  It remains a carrier-level leaf:
no basis theorem, no dense-span theorem, no finite-support-domain equivalence,
no unbounded-operator domain theorem, no self-adjointness, no PVM, and no
spectral atom claim. -/
structure ConcreteL2MathlibUnitPairSeparationSurface where
  unitNonzeroReady : concreteAnalyticSpineL2MathlibUnitNonzeroSurfaceReady
  pairSeparationAdapter : concreteL2MathlibUnitPairSeparationAdapter
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete Mathlib completed-`ℓ²` coordinate-unit pairwise separation surface. -/
def concreteL2MathlibUnitPairSeparationSurface :
    ConcreteL2MathlibUnitPairSeparationSurface :=
  { unitNonzeroReady :=
      concrete_analytic_spine_l2_mathlib_unit_nonzero_surface_ready
    pairSeparationAdapter := concrete_l2_mathlib_unit_pair_separation_adapter_ready
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the Mathlib completed-`ℓ²` coordinate-unit pairwise separation surface. -/
def concreteAnalyticSpineL2MathlibUnitPairSeparationSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibUnitNonzeroSurfaceReady ∧
  concreteL2MathlibUnitPairSeparationAdapter ∧
  concreteL2MathlibUnitPairSeparationSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibUnitPairSeparationSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibUnitPairSeparationSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibUnitPairSeparationSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibUnitPairSeparationSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibUnitPairSeparationSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibUnitPairSeparationSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the Mathlib completed-`ℓ²` coordinate-unit pairwise separation surface. -/
theorem concrete_analytic_spine_l2_mathlib_unit_pair_separation_surface_ready :
    concreteAnalyticSpineL2MathlibUnitPairSeparationSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibUnitPairSeparationSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_unit_nonzero_surface_ready <|
      And.intro concrete_l2_mathlib_unit_pair_separation_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the Mathlib completed-`ℓ²` coordinate-unit pairwise separation surface. -/
def concreteAnalyticSpineL2MathlibUnitPairSeparationHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibUnitPairSeparationSurfaceReady

/-- Boundary theorem for the Mathlib completed-`ℓ²` coordinate-unit pairwise separation surface. -/
theorem concrete_analytic_spine_l2_mathlib_unit_pair_separation_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibUnitPairSeparationHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_unit_pair_separation_surface_ready

end

end MathlibAnalytic
end MGAP4D
