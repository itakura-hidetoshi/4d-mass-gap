import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearMapIdentity

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The range-restricted finite synthesis map preserves addition. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_add
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (c d : Fin m → ℝ) :
    concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) (c + d) =
      concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c +
      concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) d := by
  change (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).toLinearMap (c + d) =
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).toLinearMap c +
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).toLinearMap d
  exact map_add (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).toLinearMap c d

/-- The range-restricted finite synthesis map preserves scalar multiplication. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_smul
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (a : ℝ) (c : Fin m → ℝ) :
    concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) (a • c) =
      a • concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c := by
  change (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).toLinearMap (a • c) =
    a • (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).toLinearMap c
  exact map_smul (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).toLinearMap a c

/-- The range-map equivalence preserves addition through its linear-equivalence bridge. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_add
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (c d : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisRangeMapEquiv hφ (c + d) =
      concreteL2MathlibFinNSynthesisRangeMapEquiv hφ c +
      concreteL2MathlibFinNSynthesisRangeMapEquiv hφ d := by
  change concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) (c + d) =
      concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c +
      concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) d
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_add hφ c d

/-- The range-map equivalence preserves scalar multiplication through its
linear-equivalence bridge. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_smul
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (a : ℝ) (c : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisRangeMapEquiv hφ (a • c) =
      a • concreteL2MathlibFinNSynthesisRangeMapEquiv hφ c := by
  change concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) (a • c) =
      a • concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_smul hφ a c

/-- Adapter predicate for the range-map linearity layer. -/
def concreteL2MathlibFinNSynthesisRangeMapLinearityAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    (∀ c d : Fin m → ℝ,
      concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ) (c + d) =
        concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ) c +
        concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ) d) ∧
    (∀ (a : ℝ) (c : Fin m → ℝ),
      concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ) (a • c) =
        a • concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ) c)

/-- Adapter theorem for the range-map linearity layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_linearity_adapter_ready :
    concreteL2MathlibFinNSynthesisRangeMapLinearityAdapter := by
  intro m φ hφ
  exact ⟨concrete_l2_mathlib_fin_n_synthesis_range_map_add hφ,
    concrete_l2_mathlib_fin_n_synthesis_range_map_smul hφ⟩

/-- Surface for the range-map linearity layer. -/
structure ConcreteL2MathlibFinNSynthesisRangeMapLinearitySurface where
  rangeMapLinearMapIdentityReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurfaceReady
  rangeMapLinearityAdapter : concreteL2MathlibFinNSynthesisRangeMapLinearityAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete range-map linearity surface. -/
def concreteL2MathlibFinNSynthesisRangeMapLinearitySurface :
    ConcreteL2MathlibFinNSynthesisRangeMapLinearitySurface :=
  { rangeMapLinearMapIdentityReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_linear_map_identity_surface_ready
    rangeMapLinearityAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_range_map_linearity_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the range-map linearity layer. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearitySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurfaceReady ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearityAdapter ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearitySurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearitySurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearitySurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearitySurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearitySurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearitySurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearitySurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearitySurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearitySurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the range-map linearity layer. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_linearity_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearitySurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearitySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_linear_map_identity_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_range_map_linearity_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the range-map linearity layer. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearityHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearitySurfaceReady

/-- Hard-residual boundary theorem for the range-map linearity layer. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_linearity_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearityHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_linearity_surface_ready

end

end MathlibAnalytic
end MGAP4D
