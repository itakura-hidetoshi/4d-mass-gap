import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecovery

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The selected coordinate unit as an element of the general `Fin m` synthesis range. -/
def concreteL2MathlibFinNSelectedRangeVector
    {m : ℕ} (φ : Fin m → ℕ) (i : Fin m) :
    concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ) :=
  ⟨concreteL2MathlibUnit (φ i), by
    refine ⟨fun j : Fin m => if j = i then (1 : ℝ) else 0, ?_⟩
    rw [concrete_l2_mathlib_fin_n_synthesis_linear_map_apply]
    unfold concreteL2MathlibFinNSynthesis concreteL2MathlibFinNUnitFamily
    classical
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      simp [hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))⟩

/-- The selected range vector has the selected coordinate unit as its underlying
value. -/
theorem concrete_l2_mathlib_fin_n_selected_range_vector_val
    {m : ℕ} (φ : Fin m → ℕ) (i : Fin m) :
    (concreteL2MathlibFinNSelectedRangeVector φ i : lp (fun _ : ℕ => ℝ) 2) =
      concreteL2MathlibUnit (φ i) := by
  rfl

/-- The coefficient-space standard vector synthesizes to the selected range vector. -/
theorem concrete_l2_mathlib_fin_n_selected_range_vector_synthesized_by_standard_coeff
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (i : Fin m) :
    concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
        (fun j : Fin m => if j = i then (1 : ℝ) else 0) =
      concreteL2MathlibFinNSelectedRangeVector φ i := by
  apply Subtype.ext
  simp [concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective,
    concreteL2MathlibFiniteSynthesisRangeLinearEquivOfCoordinateRecovery,
    concreteL2MathlibFiniteSynthesisRangeLinearEquivOfZeroFiberCoeffTrivial,
    concreteL2MathlibFiniteSynthesisRangeLinearEquiv,
    concreteL2MathlibFiniteSynthesisRangeMap,
    concreteL2MathlibFinNSynthesisLinearMap,
    concreteL2MathlibFinNSynthesis, concreteL2MathlibFinNUnitFamily]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- The reconstructed coordinates of a selected range vector are the corresponding
standard coefficient vector. -/
theorem concrete_l2_mathlib_fin_n_selected_range_coordinates_eq_standard
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (i : Fin m) :
    concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ
        (concreteL2MathlibFinNSelectedRangeVector φ i) =
      (fun j : Fin m => if j = i then (1 : ℝ) else 0) := by
  let E := concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
  have hE : E (fun j : Fin m => if j = i then (1 : ℝ) else 0) =
      concreteL2MathlibFinNSelectedRangeVector φ i :=
    concrete_l2_mathlib_fin_n_selected_range_vector_synthesized_by_standard_coeff hφ i
  change E.symm (concreteL2MathlibFinNSelectedRangeVector φ i) =
    (fun j : Fin m => if j = i then (1 : ℝ) else 0)
  exact Eq.symm ((LinearEquiv.symm_apply_eq E).mpr hE.symm)

/-- Every vector in the general `Fin m` synthesis range decomposes as the finite
linear combination of selected coordinate units with its recovered coordinates. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_decompose_val
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (v : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m,
        concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v i •
          concreteL2MathlibUnit (φ i) := by
  have hsynth := concrete_l2_mathlib_fin_n_synthesis_coordinates_synthesize_of_injective hφ v
  have hval := congrArg (fun w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ) =>
      (w : lp (fun _ : ℕ => ℝ) 2)) hsynth
  simp [concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective,
    concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective,
    concreteL2MathlibFiniteSynthesisRangeLinearEquivOfCoordinateRecovery,
    concreteL2MathlibFiniteSynthesisRangeLinearEquivOfZeroFiberCoeffTrivial,
    concreteL2MathlibFiniteSynthesisRangeLinearEquiv,
    concreteL2MathlibFiniteSynthesisRangeMap,
    concreteL2MathlibFinNSynthesisLinearMap,
    concreteL2MathlibFinNSynthesis, concreteL2MathlibFinNUnitFamily] at hval
  exact hval.symm

/-- Range-subtype form of the general `Fin m` coordinate decomposition. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_decompose_subtype
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    v =
      ∑ i : Fin m,
        concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v i •
          concreteL2MathlibFinNSelectedRangeVector φ i := by
  apply Subtype.ext
  simp [concreteL2MathlibFinNSelectedRangeVector,
    concrete_l2_mathlib_fin_n_synthesis_range_decompose_val hφ v]

/-- Coefficient uniqueness for the general `Fin m` range decomposition. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_decompose_coefficients_unique
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)} {c : Fin m → ℝ}
    (hc : (v : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, c i • concreteL2MathlibUnit (φ i)) :
    c = concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v := by
  let E := concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
  have hsynth : E c = v := by
    apply Subtype.ext
    simp [E, concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective,
      concreteL2MathlibFiniteSynthesisRangeLinearEquivOfCoordinateRecovery,
      concreteL2MathlibFiniteSynthesisRangeLinearEquivOfZeroFiberCoeffTrivial,
      concreteL2MathlibFiniteSynthesisRangeLinearEquiv,
      concreteL2MathlibFiniteSynthesisRangeMap,
      concreteL2MathlibFinNSynthesisLinearMap,
      concreteL2MathlibFinNSynthesis, concreteL2MathlibFinNUnitFamily]
    exact hc.symm
  change c = E.symm v
  exact Eq.symm ((LinearEquiv.symm_apply_eq E).mpr hsynth.symm)

/-- Adapter predicate for the general `Fin m` range decomposition layer. -/
def concreteL2MathlibFinNSynthesisRangeDecompositionAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    (∀ v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      (v : lp (fun _ : ℕ => ℝ) 2) =
        ∑ i : Fin m,
          concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v i •
            concreteL2MathlibUnit (φ i)) ∧
    (∀ i : Fin m,
      concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ
          (concreteL2MathlibFinNSelectedRangeVector φ i) =
        (fun j : Fin m => if j = i then (1 : ℝ) else 0))

/-- Adapter theorem for the general `Fin m` range decomposition layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_decomposition_adapter_ready :
    concreteL2MathlibFinNSynthesisRangeDecompositionAdapter := by
  intro m φ hφ
  exact ⟨
    by intro v; exact concrete_l2_mathlib_fin_n_synthesis_range_decompose_val hφ v,
    by intro i; exact concrete_l2_mathlib_fin_n_selected_range_coordinates_eq_standard hφ i⟩

/-- Surface for general `Fin m` range decomposition.

This layer upgrades the previous coordinate-recovery result to an explicit
finite decomposition of every range vector in the selected coordinate units. -/
structure ConcreteL2MathlibFinNSynthesisRangeDecompositionSurface where
  coordinateRecoveryReady : concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoverySurfaceReady
  rangeDecompositionAdapter : concreteL2MathlibFinNSynthesisRangeDecompositionAdapter
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete general `Fin m` range decomposition surface. -/
def concreteL2MathlibFinNSynthesisRangeDecompositionSurface :
    ConcreteL2MathlibFinNSynthesisRangeDecompositionSurface :=
  { coordinateRecoveryReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_recovery_surface_ready
    rangeDecompositionAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_range_decomposition_adapter_ready
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the general `Fin m` range decomposition surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisRangeDecompositionSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRecoverySurfaceReady ∧
  concreteL2MathlibFinNSynthesisRangeDecompositionAdapter ∧
  concreteL2MathlibFinNSynthesisRangeDecompositionSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinNSynthesisRangeDecompositionSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisRangeDecompositionSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisRangeDecompositionSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisRangeDecompositionSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisRangeDecompositionSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisRangeDecompositionSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisRangeDecompositionSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the general `Fin m` range decomposition surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_decomposition_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisRangeDecompositionSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisRangeDecompositionSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_recovery_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_range_decomposition_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial trivial

/-- Hard-residual boundary marker for the general `Fin m` range decomposition
surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisRangeDecompositionHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisRangeDecompositionSurfaceReady

/-- Hard-residual boundary theorem for the general `Fin m` range decomposition
surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_decomposition_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisRangeDecompositionHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_decomposition_surface_ready

end

end MathlibAnalytic
end MGAP4D
