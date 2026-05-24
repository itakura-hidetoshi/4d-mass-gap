import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFiniteSynthesisCoordinateRecoveryTemplate

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- A general `Fin m` coordinate-unit family selected by an index map
`φ : Fin m → ℕ`. -/
def concreteL2MathlibFinNUnitFamily (m : ℕ) (φ : Fin m → ℕ) :
    Fin m → lp (fun _ : ℕ => ℝ) 2 :=
  fun i => concreteL2MathlibUnit (φ i)

/-- The named finite synthesis function for a general `Fin m` coordinate-unit
family. -/
def concreteL2MathlibFinNSynthesis (m : ℕ) (φ : Fin m → ℕ)
    (c : Fin m → ℝ) : lp (fun _ : ℕ => ℝ) 2 :=
  ∑ i : Fin m, c i • concreteL2MathlibFinNUnitFamily m φ i

/-- The named `Fin m` synthesis function is exactly its finite-sum expression. -/
theorem concrete_l2_mathlib_fin_n_synthesis_eq_sum
    (m : ℕ) (φ : Fin m → ℕ) (c : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesis m φ c =
      ∑ i : Fin m, c i • concreteL2MathlibFinNUnitFamily m φ i := by
  rfl

/-- The zero coefficient function synthesizes to zero. -/
theorem concrete_l2_mathlib_fin_n_synthesis_zero_coefficients
    (m : ℕ) (φ : Fin m → ℕ) :
    concreteL2MathlibFinNSynthesis m φ (fun _ : Fin m => (0 : ℝ)) = 0 := by
  unfold concreteL2MathlibFinNSynthesis concreteL2MathlibFinNUnitFamily
  simp

/-- Coordinate-recovery statement for the general `Fin m` coordinate-unit
synthesis.

This is intentionally introduced as a named proposition before being proved in a
later leaf.  It is the exact finite-sum evaluation goal needed to unlock the
kernel/range templates. -/
def concreteL2MathlibFinNSynthesisCoordinateRecovery (m : ℕ) (φ : Fin m → ℕ) : Prop :=
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw (Fin m) φ
    { toFun := concreteL2MathlibFinNSynthesis m φ
      map_add' := by
        intro c d
        unfold concreteL2MathlibFinNSynthesis concreteL2MathlibFinNUnitFamily
        simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        unfold concreteL2MathlibFinNSynthesis concreteL2MathlibFinNUnitFamily
        simp [Pi.smul_apply, Finset.smul_sum, smul_smul] }

/-- Linear-map form of the general `Fin m` coordinate-unit synthesis.

The linearity part is already purely formal.  The hard part for later is not
linearity but coordinate recovery under injectivity of `φ`. -/
def concreteL2MathlibFinNSynthesisLinearMap (m : ℕ) (φ : Fin m → ℕ) :
    (Fin m → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2 where
  toFun := concreteL2MathlibFinNSynthesis m φ
  map_add' := by
    intro c d
    unfold concreteL2MathlibFinNSynthesis concreteL2MathlibFinNUnitFamily
    simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a c
    unfold concreteL2MathlibFinNSynthesis concreteL2MathlibFinNUnitFamily
    simp [Pi.smul_apply, Finset.smul_sum, smul_smul]

/-- The linear-map synthesis agrees definitionally with the named synthesis
function. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_map_apply
    (m : ℕ) (φ : Fin m → ℕ) (c : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisLinearMap m φ c =
      concreteL2MathlibFinNSynthesis m φ c := by
  rfl

/-- Coordinate-recovery statement for the linear-map form of `Fin m` synthesis. -/
def concreteL2MathlibFinNSynthesisLinearMapCoordinateRecovery
    (m : ℕ) (φ : Fin m → ℕ) : Prop :=
  concreteL2MathlibFiniteSynthesisCoordinateRecoveryLaw (Fin m) φ
    (concreteL2MathlibFinNSynthesisLinearMap m φ)

/-- If coordinate recovery holds for the general `Fin m` synthesis linear map,
then its kernel is bottom. -/
theorem concrete_l2_mathlib_fin_n_synthesis_ker_eq_bot_of_coordinate_recovery
    (m : ℕ) (φ : Fin m → ℕ)
    (hrecover : concreteL2MathlibFinNSynthesisLinearMapCoordinateRecovery m φ) :
    LinearMap.ker (concreteL2MathlibFinNSynthesisLinearMap m φ) = ⊥ := by
  exact concrete_l2_mathlib_finite_synthesis_ker_eq_bot_of_coordinate_recovery
    (Fin m) φ (concreteL2MathlibFinNSynthesisLinearMap m φ) hrecover

/-- If coordinate recovery holds for the general `Fin m` synthesis linear map,
then the range-restricted synthesis map is bijective. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_of_coordinate_recovery
    (m : ℕ) (φ : Fin m → ℕ)
    (hrecover : concreteL2MathlibFinNSynthesisLinearMapCoordinateRecovery m φ) :
    Function.Bijective
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)) := by
  exact concrete_l2_mathlib_finite_synthesis_range_map_bijective_of_coordinate_recovery
    (Fin m) φ (concreteL2MathlibFinNSynthesisLinearMap m φ) hrecover

/-- If coordinate recovery holds, every range vector has reconstructed
coefficients through the generic template. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinates_synthesize_of_coordinate_recovery
    (m : ℕ) (φ : Fin m → ℕ)
    (hrecover : concreteL2MathlibFinNSynthesisLinearMapCoordinateRecovery m φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    concreteL2MathlibFiniteSynthesisRangeLinearEquivOfCoordinateRecovery
        (Fin m) φ (concreteL2MathlibFinNSynthesisLinearMap m φ) hrecover
      (concreteL2MathlibFiniteSynthesisRangeCoordinatesOfCoordinateRecovery
        (Fin m) φ (concreteL2MathlibFinNSynthesisLinearMap m φ) hrecover v) = v := by
  exact concrete_l2_mathlib_finite_synthesis_range_coordinates_synthesize_of_coordinate_recovery
    (Fin m) φ (concreteL2MathlibFinNSynthesisLinearMap m φ) hrecover v

/-- Adapter predicate for the `Fin m` synthesis skeleton.

The skeleton packages the formal linear-map/range-template consequences, while
leaving the actual coordinate recovery theorem under `Function.Injective φ` for a
later leaf. -/
def concreteL2MathlibFinNSynthesisSkeletonAdapter : Prop :=
  ∀ (m : ℕ) (φ : Fin m → ℕ),
    (∀ hrecover : concreteL2MathlibFinNSynthesisLinearMapCoordinateRecovery m φ,
      LinearMap.ker (concreteL2MathlibFinNSynthesisLinearMap m φ) = ⊥ ∧
      Function.Bijective
        (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ)))

/-- Adapter theorem for the `Fin m` synthesis skeleton. -/
theorem concrete_l2_mathlib_fin_n_synthesis_skeleton_adapter_ready :
    concreteL2MathlibFinNSynthesisSkeletonAdapter := by
  intro m φ hrecover
  exact ⟨
    concrete_l2_mathlib_fin_n_synthesis_ker_eq_bot_of_coordinate_recovery m φ hrecover,
    concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_of_coordinate_recovery m φ hrecover⟩

/-- Surface for the general `Fin m` coordinate-unit synthesis skeleton.

This is the first concrete all-`Fin m` layer.  It defines the general finite
coordinate-unit family and synthesis linear map, and connects a future coordinate
recovery theorem to the already-proved kernel/range templates. -/
structure ConcreteL2MathlibFinNSynthesisSkeletonSurface where
  coordinateRecoveryTemplateReady : concreteAnalyticSpineL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurfaceReady
  finNSynthesisSkeletonAdapter : concreteL2MathlibFinNSynthesisSkeletonAdapter
  boundaryCoordinateRecoveryUnderInjectiveIndexMapNotYetClaimed : Prop
  boundaryZeroFiberForGeneralCoordinateSynthesisNotYetClaimed : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete `Fin m` synthesis skeleton surface. -/
def concreteL2MathlibFinNSynthesisSkeletonSurface :
    ConcreteL2MathlibFinNSynthesisSkeletonSurface :=
  { coordinateRecoveryTemplateReady :=
      concrete_analytic_spine_l2_mathlib_finite_synthesis_coordinate_recovery_template_surface_ready
    finNSynthesisSkeletonAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_skeleton_adapter_ready
    boundaryCoordinateRecoveryUnderInjectiveIndexMapNotYetClaimed := True
    boundaryZeroFiberForGeneralCoordinateSynthesisNotYetClaimed := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the `Fin m` synthesis skeleton surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisSkeletonSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFiniteSynthesisCoordinateRecoveryTemplateSurfaceReady ∧
  concreteL2MathlibFinNSynthesisSkeletonAdapter ∧
  concreteL2MathlibFinNSynthesisSkeletonSurface.boundaryCoordinateRecoveryUnderInjectiveIndexMapNotYetClaimed ∧
  concreteL2MathlibFinNSynthesisSkeletonSurface.boundaryZeroFiberForGeneralCoordinateSynthesisNotYetClaimed ∧
  concreteL2MathlibFinNSynthesisSkeletonSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinNSynthesisSkeletonSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinNSynthesisSkeletonSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisSkeletonSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisSkeletonSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisSkeletonSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisSkeletonSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisSkeletonSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisSkeletonSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the `Fin m` synthesis skeleton surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_skeleton_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisSkeletonSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisSkeletonSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_finite_synthesis_coordinate_recovery_template_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_skeleton_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial trivial

/-- Hard-residual boundary marker for the `Fin m` synthesis skeleton. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisSkeletonHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisSkeletonSurfaceReady

/-- Hard-residual boundary theorem for the `Fin m` synthesis skeleton. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_skeleton_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisSkeletonHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_skeleton_surface_ready

end

end MathlibAnalytic
end MGAP4D
