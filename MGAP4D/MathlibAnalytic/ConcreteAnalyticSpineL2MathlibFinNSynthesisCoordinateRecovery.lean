import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisSkeleton

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

theorem concrete_l2_mathlib_fin_n_unit_family_apply_off_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {i j : Fin m} (hji : j ≠ i) :
    concreteL2MathlibFinNUnitFamily m φ j (φ i) = 0 := by
  unfold concreteL2MathlibFinNUnitFamily
  apply concrete_l2_mathlib_unit_apply_ne
  intro hcoord
  exact hji (hφ hcoord.symm)

theorem concrete_l2_mathlib_fin_n_unit_family_apply_self
    {m : ℕ} {φ : Fin m → ℕ} (i : Fin m) :
    concreteL2MathlibFinNUnitFamily m φ i (φ i) = 1 := by
  unfold concreteL2MathlibFinNUnitFamily
  exact concrete_l2_mathlib_unit_apply_self (φ i)

theorem concrete_l2_mathlib_fin_n_synthesis_apply_selected_coordinate
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (c : Fin m → ℝ) (i : Fin m) :
    concreteL2MathlibFinNSynthesis m φ c (φ i) = c i := by
  classical
  unfold concreteL2MathlibFinNSynthesis concreteL2MathlibFinNUnitFamily
  calc
    (∑ j : Fin m, c j • concreteL2MathlibUnit (φ j)) (φ i)
        = ∑ j : Fin m, (c j • concreteL2MathlibUnit (φ j)) (φ i) := by
          exact Finset.sum_apply
    _ = ∑ j : Fin m, c j * concreteL2MathlibUnit (φ j) (φ i) := by
          simp [Pi.smul_apply]
    _ = c i := by
          rw [Finset.sum_eq_single i]
          · simp [concrete_l2_mathlib_unit_apply_self]
          · intro j _hj hji
            have hoff : concreteL2MathlibUnit (φ j) (φ i) = 0 := by
              apply concrete_l2_mathlib_unit_apply_ne
              intro hcoord
              exact hji (hφ hcoord.symm)
            simp [hoff]
          · intro hi
            exact False.elim (hi (Finset.mem_univ i))

theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_recovery_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    concreteL2MathlibFinNSynthesisCoordinateRecovery m φ := by
  intro c i
  exact concrete_l2_mathlib_fin_n_synthesis_apply_selected_coordinate hφ c i

theorem concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    concreteL2MathlibFinNSynthesisLinearMapCoordinateRecovery m φ := by
  intro c i
  change concreteL2MathlibFinNSynthesis m φ c (φ i) = c i
  exact concrete_l2_mathlib_fin_n_synthesis_apply_selected_coordinate hφ c i

theorem concrete_l2_mathlib_fin_n_synthesis_ker_eq_bot_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    LinearMap.ker (concreteL2MathlibFinNSynthesisLinearMap m φ) = ⊥ := by
  exact concrete_l2_mathlib_fin_n_synthesis_ker_eq_bot_of_coordinate_recovery m φ
    (concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective hφ)

theorem concrete_l2_mathlib_fin_n_synthesis_linear_map_injective_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Injective (concreteL2MathlibFinNSynthesisLinearMap m φ) := by
  rw [← LinearMap.ker_eq_bot]
  exact concrete_l2_mathlib_fin_n_synthesis_ker_eq_bot_of_injective hφ

theorem concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Bijective
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)) := by
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_of_coordinate_recovery m φ
    (concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective hφ)

def concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    (Fin m → ℝ) ≃ₗ[ℝ]
      concreteL2MathlibFiniteSynthesisRange (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) :=
  concreteL2MathlibFiniteSynthesisRangeLinearEquivOfCoordinateRecovery
    (Fin m) φ (concreteL2MathlibFinNSynthesisLinearMap m φ)
    (concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective hφ)

def concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) : Fin m → ℝ :=
  concreteL2MathlibFiniteSynthesisRangeCoordinatesOfCoordinateRecovery
    (Fin m) φ (concreteL2MathlibFinNSynthesisLinearMap m φ)
    (concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective hφ) v

theorem concrete_l2_mathlib_fin_n_synthesis_coordinates_synthesize_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
        (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v) = v := by
  unfold concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective
  unfold concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective
  exact concrete_l2_mathlib_finite_synthesis_range_coordinates_synthesize_of_coordinate_recovery
    (Fin m) φ (concreteL2MathlibFinNSynthesisLinearMap m φ)
    (concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective hφ) v

def concreteL2MathlibFinNSynthesisCoordinateRecoveryAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ}, Function.Injective φ →
    concreteL2MathlibFinNSynthesisLinearMapCoordinateRecovery m φ ∧
    LinearMap.ker (concreteL2MathlibFinNSynthesisLinearMap m φ) = ⊥ ∧
    Function.Injective (concreteL2MathlibFinNSynthesisLinearMap m φ) ∧
    Function.Bijective
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ))

theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_recovery_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateRecoveryAdapter := by
  intro m φ hφ
  exact ⟨
    concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective hφ,
    concrete_l2_mathlib_fin_n_synthesis_ker_eq_bot_of_injective hφ,
    concrete_l2_mathlib_fin_n_synthesis_linear_map_injective_of_injective hφ,
    concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_of_injective hφ⟩

structure ConcreteL2MathlibFinNSynthesisCoordinateRecoverySurface where
  finNSynthesisSkeletonReady : concreteAnalyticSpineL2MathlibFinNSynthesisSkeletonSurfaceReady
  coordinateRecoveryAdapter : concreteL2MathlibFinNSynthesisCoordinateRecoveryAdapter
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

def concreteL2MathlibFinNSynthesisCoordinateRecoverySurface :
    ConcreteL2MathlibFinNSynthesisCoordinateRecoverySurface :=
  { finNSynthesisSkeletonReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_skeleton_surface_ready
    coordinateRecoveryAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_recovery_adapter_ready
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoverySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisSkeletonSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateRecoveryAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateRecoverySurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRecoverySurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRecoverySurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateRecoverySurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRecoverySurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateRecoverySurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateRecoverySurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRecoverySurface.boundaryNotPositiveSpectralWeightTheorem

theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_recovery_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoverySurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoverySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_skeleton_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_recovery_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial trivial

def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoveryHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoverySurfaceReady

theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_recovery_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoveryHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_recovery_surface_ready

end

end MathlibAnalytic
end MGAP4D
