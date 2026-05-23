import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFiniteSynthesisKernelTemplate

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Coordinate-recovery law for a generic finite-coefficient synthesis map.

For a synthesis map `T : (ι → ℝ) →ₗ ℓ²(ℕ, ℝ)`, a coordinate selector
`φ : ι → ℕ` recovers coefficients if evaluating the synthesized vector at
`φ i` returns exactly the coefficient `c i`.

Later coordinate-unit synthesis leaves should prove this law from the facts
`e_(φ i) (φ i) = 1` and `e_(φ j) (φ i) = 0` for `j ≠ i`. -/
def concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw (ι : Type*)
    (φ : ι → ℕ) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2) : Prop :=
  ∀ c : ι → ℝ, ∀ i : ι, T c (φ i) = c i

/-- A coordinate-recovery law implies coefficient-triviality of the zero fiber. -/
theorem concrete_l2_mathlib_finite_synthesis_zero_fiber_coeff_trivial_of_coordinate_recovery
    (ι : Type*) (φ : ι → ℕ)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hrecover : concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw ι φ T) :
    concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T := by
  intro c hTc i
  have hcoord_zero : T c (φ i) = (0 : ℝ) := by
    rw [hTc]
    rfl
  have hcoord_coeff : T c (φ i) = c i := hrecover c i
  exact Eq.trans hcoord_coeff.symm hcoord_zero

/-- A coordinate-recovery law implies bottom kernel. -/
theorem concrete_l2_mathlib_finite_synthesis_ker_eq_bot_of_coordinate_recovery
    (ι : Type*) (φ : ι → ℕ)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hrecover : concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw ι φ T) :
    LinearMap.ker T = ⊥ := by
  exact concrete_l2_mathlib_finite_synthesis_ker_eq_bot_of_zero_fiber_coeff_trivial ι T
    (concrete_l2_mathlib_finite_synthesis_zero_fiber_coeff_trivial_of_coordinate_recovery ι φ T hrecover)

/-- A coordinate-recovery law implies injectivity of the synthesis map. -/
theorem concrete_l2_mathlib_finite_synthesis_injective_of_coordinate_recovery
    (ι : Type*) (φ : ι → ℕ)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hrecover : concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw ι φ T) :
    Function.Injective T := by
  exact concrete_l2_mathlib_finite_synthesis_injective_of_zero_fiber_coeff_trivial ι T
    (concrete_l2_mathlib_finite_synthesis_zero_fiber_coeff_trivial_of_coordinate_recovery ι φ T hrecover)

/-- A coordinate-recovery law implies bijectivity of the range-restricted
synthesis map. -/
theorem concrete_l2_mathlib_finite_synthesis_range_map_bijective_of_coordinate_recovery
    (ι : Type*) (φ : ι → ℕ)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hrecover : concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw ι φ T) :
    Function.Bijective (concreteL2MathlibFiniteSynthesisRangeMap ι T) := by
  exact concrete_l2_mathlib_finite_synthesis_range_map_bijective_of_zero_fiber_coeff_trivial ι T
    (concrete_l2_mathlib_finite_synthesis_zero_fiber_coeff_trivial_of_coordinate_recovery ι φ T hrecover)

/-- Coordinate recovery gives the generic range linear equivalence. -/
def concreteL2MathlibFiniteSynthesisRangeLinearEquivOfCoordinateRecovery
    (ι : Type*) (φ : ι → ℕ)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hrecover : concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw ι φ T) :
    (ι → ℝ) ≃ₗ[ℝ] concreteL2MathlibFiniteSynthesisRange ι T :=
  concreteL2MathlibFiniteSynthesisRangeLinearEquivOfZeroFiberCoeffTrivial ι T
    (concrete_l2_mathlib_finite_synthesis_zero_fiber_coeff_trivial_of_coordinate_recovery ι φ T hrecover)

/-- Coordinate recovery gives generic coordinate reconstruction on the range. -/
def concreteL2MathlibFiniteSynthesisRangeCoordinatesOfCoordinateRecovery
    (ι : Type*) (φ : ι → ℕ)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hrecover : concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw ι φ T)
    (v : concreteL2MathlibFiniteSynthesisRange ι T) : ι → ℝ :=
  concreteL2MathlibFiniteSynthesisRangeCoordinatesOfZeroFiberCoeffTrivial ι T
    (concrete_l2_mathlib_finite_synthesis_zero_fiber_coeff_trivial_of_coordinate_recovery ι φ T hrecover) v

/-- Re-synthesizing the coordinates reconstructed under coordinate recovery gives
back the range vector. -/
theorem concrete_l2_mathlib_finite_synthesis_range_coordinates_synthesize_of_coordinate_recovery
    (ι : Type*) (φ : ι → ℕ)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hrecover : concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw ι φ T)
    (v : concreteL2MathlibFiniteSynthesisRange ι T) :
    concreteL2MathlibFiniteSynthesisRangeLinearEquivOfCoordinateRecovery ι φ T hrecover
        (concreteL2MathlibFiniteSynthesisRangeCoordinatesOfCoordinateRecovery ι φ T hrecover v) = v := by
  unfold concreteL2MathlibFiniteSynthesisRangeLinearEquivOfCoordinateRecovery
  unfold concreteL2MathlibFiniteSynthesisRangeCoordinatesOfCoordinateRecovery
  exact concrete_l2_mathlib_finite_synthesis_range_coordinates_synthesize_of_zero_fiber_coeff_trivial ι T
    (concrete_l2_mathlib_finite_synthesis_zero_fiber_coeff_trivial_of_coordinate_recovery ι φ T hrecover) v

/-- Adapter predicate for the coordinate-recovery template. -/
def concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateAdapter : Prop :=
  ∀ (ι : Type*) (φ : ι → ℕ)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2),
    concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw ι φ T →
      concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T ∧
      LinearMap.ker T = ⊥ ∧
      Function.Injective T ∧
      Function.Bijective (concreteL2MathlibFiniteSynthesisRangeMap ι T) ∧
      ∀ v : concreteL2MathlibFiniteSynthesisRange ι T,
        concreteL2MathlibFiniteSynthesisRangeLinearEquivOfCoordinateRecovery ι φ T ‹concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw ι φ T›
          (concreteL2MathlibFiniteSynthesisRangeCoordinatesOfCoordinateRecovery ι φ T ‹concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw ι φ T› v) = v

/-- Adapter theorem for the coordinate-recovery template. -/
theorem concrete_l2_mathlib_finite_synthesis_coordinate_recovery_template_adapter_ready :
    concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateAdapter := by
  intro ι φ T hrecover
  exact ⟨
    concrete_l2_mathlib_finite_synthesis_zero_fiber_coeff_trivial_of_coordinate_recovery ι φ T hrecover,
    concrete_l2_mathlib_finite_synthesis_ker_eq_bot_of_coordinate_recovery ι φ T hrecover,
    concrete_l2_mathlib_finite_synthesis_injective_of_coordinate_recovery ι φ T hrecover,
    concrete_l2_mathlib_finite_synthesis_range_map_bijective_of_coordinate_recovery ι φ T hrecover,
    by
      intro v
      exact concrete_l2_mathlib_finite_synthesis_range_coordinates_synthesize_of_coordinate_recovery ι φ T hrecover v⟩

/-- Surface for the finite synthesis coordinate-recovery template.

This layer isolates the next proof obligation for all-`Fin n` coordinate-unit
synthesis: prove the coordinate-recovery law.  Once coordinate recovery is proved,
zero fiber triviality, kernel-bottom, injectivity, range equivalence, and range
coordinate reconstruction follow automatically from the preceding templates. -/
structure ConcreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface where
  kernelTemplateReady : concreteAnalyticSpineL2MathlibFiniteSynthesisKernelTemplateSurfaceReady
  coordinateRecoveryTemplateAdapter : concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateAdapter
  boundaryCoordinateRecoveryForGeneralCoordinateSynthesisNotClaimed : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete finite synthesis coordinate-recovery template surface. -/
def concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface :
    ConcreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface :=
  { kernelTemplateReady :=
      concrete_analytic_spine_l2_mathlib_finite_synthesis_kernel_template_surface_ready
    coordinateRecoveryTemplateAdapter :=
      concrete_l2_mathlib_finite_synthesis_coordinate_recovery_template_adapter_ready
    boundaryCoordinateRecoveryForGeneralCoordinateSynthesisNotClaimed := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the finite synthesis coordinate-recovery template
surface. -/
def concreteAnalyticSpineL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFiniteSynthesisKernelTemplateSurfaceReady ∧
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateAdapter ∧
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface.boundaryCoordinateRecoveryForGeneralCoordinateSynthesisNotClaimed ∧
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the finite synthesis coordinate-recovery template
surface. -/
theorem concrete_analytic_spine_l2_mathlib_finite_synthesis_coordinate_recovery_template_surface_ready :
    concreteAnalyticSpineL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_finite_synthesis_kernel_template_surface_ready <|
      And.intro concrete_l2_mathlib_finite_synthesis_coordinate_recovery_template_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the finite synthesis coordinate-recovery
template. -/
def concreteAnalyticSpineL2MathlibFiniteSynthesisCoordinateRecoveryTemplateHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurfaceReady

/-- Hard-residual boundary theorem for the finite synthesis coordinate-recovery
template. -/
theorem concrete_analytic_spine_l2_mathlib_finite_synthesis_coordinate_recovery_template_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFiniteSynthesisCoordinateRecoveryTemplateHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_finite_synthesis_coordinate_recovery_template_surface_ready

end

end MathlibAnalytic
end MGAP4D
