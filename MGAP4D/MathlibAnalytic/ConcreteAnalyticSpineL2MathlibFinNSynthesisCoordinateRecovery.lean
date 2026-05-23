import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisSkeleton

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Off-diagonal coordinate evaluation vanishes for an injective selected-index map. -/
theorem concrete_l2_mathlib_fin_n_unit_family_apply_off_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {i j : Fin m} (hji : j ≠ i) :
    concreteL2MathlibFinNUnitFamily m φ j (φ i) = 0 := by
  unfold concreteL2MathlibFinNUnitFamily
  apply concrete_l2_mathlib_unit_apply_ne
  intro hcoord
  exact hji (hφ hcoord.symm)

/-- Diagonal coordinate evaluation is one for the selected coordinate-unit family. -/
theorem concrete_l2_mathlib_fin_n_unit_family_apply_self
    {m : ℕ} {φ : Fin m → ℕ} (i : Fin m) :
    concreteL2MathlibFinNUnitFamily m φ i (φ i) = 1 := by
  unfold concreteL2MathlibFinNUnitFamily
  exact concrete_l2_mathlib_unit_apply_self (φ i)

/-- Evaluating the `Pi.single` finite sum at the selected coordinate recovers the
selected coefficient. -/
theorem concrete_l2_mathlib_fin_n_pi_single_sum_apply_selected_coordinate
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (c : Fin m → ℝ) (i : Fin m) :
    (∑ x : Fin m, c x * Pi.single (φ x) (1 : ℝ) (φ i)) = c i := by
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    have hne : φ j ≠ φ i := by
      intro h
      exact hji (hφ h)
    simp [Pi.single_eq_of_ne hne]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Evaluating the general `Fin m` coordinate-unit synthesis at the selected
coordinate `φ i` recovers the coefficient `c i`, provided `φ` is injective. -/
theorem concrete_l2_mathlib_fin_n_synthesis_apply_selected_coordinate
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (c : Fin m → ℝ) (i : Fin m) :
    concreteL2MathlibFinNSynthesis m φ c (φ i) = c i := by
  classical
  calc
    concreteL2MathlibFinNSynthesis m φ c (φ i)
        = (∑ j : Fin m, (c j • concreteL2MathlibUnit (φ j) : lp (fun _ : ℕ => ℝ) 2)) (φ i) := by
          rfl
    _ = (∑ j : Fin m, ((c j • concreteL2MathlibUnit (φ j) : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ)) (φ i) := by
          have hsum := lp.coeFn_sum
            (E := fun _ : ℕ => ℝ) (p := (2 : ℝ≥0∞))
            (f := fun j : Fin m => (c j • concreteL2MathlibUnit (φ j) : lp (fun _ : ℕ => ℝ) 2))
            (s := Finset.univ)
          exact congrFun hsum (φ i)
    _ = ∑ j : Fin m, c j * Pi.single (φ j) (1 : ℝ) (φ i) := by
          simp [concreteL2MathlibUnit, Pi.smul_apply]
    _ = c i := by
          exact concrete_l2_mathlib_fin_n_pi_single_sum_apply_selected_coordinate hφ c i

/-- Coordinate recovery for the general `Fin m` synthesis function under an
injective selected-index map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_recovery_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    concreteL2MathlibFinNSynthesisCoordinateRecovery m φ := by
  intro c i
  exact concrete_l2_mathlib_fin_n_synthesis_apply_selected_coordinate hφ c i

/-- Coordinate recovery for the general `Fin m` synthesis linear map under an
injective selected-index map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    concreteL2MathlibFinNSynthesisLinearMapCoordinateRecovery m φ := by
  intro c i
  change concreteL2MathlibFinNSynthesis m φ c (φ i) = c i
  exact concrete_l2_mathlib_fin_n_synthesis_apply_selected_coordinate hφ c i

/-- Injective selected indices give a bottom kernel for the general `Fin m`
coordinate-unit synthesis linear map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_ker_eq_bot_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    LinearMap.ker (concreteL2MathlibFinNSynthesisLinearMap m φ) = ⊥ := by
  exact concrete_l2_mathlib_fin_n_synthesis_ker_eq_bot_of_coordinate_recovery m φ
    (concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective hφ)

/-- Injective selected indices make the general `Fin m` coordinate-unit synthesis
linear map injective. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_map_injective_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Injective (concreteL2MathlibFinNSynthesisLinearMap m φ) := by
  rw [← LinearMap.ker_eq_bot]
  exact concrete_l2_mathlib_fin_n_synthesis_ker_eq_bot_of_injective hφ

/-- Injective selected indices make the range-restricted general `Fin m`
synthesis map bijective. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Bijective
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)) := by
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_of_coordinate_recovery m φ
    (concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective hφ)

/-- Injective selected indices give a linear equivalence from the coefficient
space to the synthesis range. -/
def concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    (Fin m → ℝ) ≃ₗ[ℝ]
      concreteL2MathlibFiniteSynthesisRange (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) :=
  concreteL2MathlibFiniteSynthesisRangeLinearEquivOfCoordinateRecovery
    (Fin m) φ (concreteL2MathlibFinNSynthesisLinearMap m φ)
    (concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective hφ)

/-- Injective selected indices give coordinate reconstruction on the general
`Fin m` synthesis range. -/
def concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) : Fin m → ℝ :=
  concreteL2MathlibFiniteSynthesisRangeCoordinatesOfCoordinateRecovery
    (Fin m) φ (concreteL2MathlibFinNSynthesisLinearMap m φ)
    (concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective hφ) v

/-- Re-synthesizing the coordinates reconstructed under injective selected indices
gives back the range vector. -/
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

/-- Adapter predicate for the general `Fin m` synthesis coordinate-recovery layer. -/
def concreteL2MathlibFinNSynthesisCoordinateRecoveryAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ}, Function.Injective φ →
    concreteL2MathlibFinNSynthesisLinearMapCoordinateRecovery m φ ∧
    LinearMap.ker (concreteL2MathlibFinNSynthesisLinearMap m φ) = ⊥ ∧
    Function.Injective (concreteL2MathlibFinNSynthesisLinearMap m φ) ∧
    Function.Bijective
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ))

/-- Adapter theorem for the general `Fin m` synthesis coordinate-recovery layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_recovery_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateRecoveryAdapter := by
  intro m φ hφ
  exact ⟨
    concrete_l2_mathlib_fin_n_synthesis_linear_map_coordinate_recovery_of_injective hφ,
    concrete_l2_mathlib_fin_n_synthesis_ker_eq_bot_of_injective hφ,
    concrete_l2_mathlib_fin_n_synthesis_linear_map_injective_of_injective hφ,
    concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_of_injective hφ⟩

/-- Surface for coordinate recovery of general `Fin m` coordinate-unit synthesis. -/
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

/-- Concrete coordinate-recovery surface for general `Fin m` coordinate-unit
synthesis. -/
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

/-- Readiness predicate for the coordinate-recovery surface of general `Fin m`
coordinate-unit synthesis. -/
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

/-- Readiness theorem for the coordinate-recovery surface of general `Fin m`
coordinate-unit synthesis. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_recovery_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoverySurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoverySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_skeleton_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_recovery_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial trivial

/-- Hard-residual boundary marker for the coordinate-recovery surface of general
`Fin m` coordinate-unit synthesis. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoveryHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoverySurfaceReady

/-- Hard-residual boundary theorem for the coordinate-recovery surface of general
`Fin m` coordinate-unit synthesis. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_recovery_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoveryHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_recovery_surface_ready

end

end MathlibAnalytic
end MGAP4D
