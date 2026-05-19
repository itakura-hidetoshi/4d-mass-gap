import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FiniteSupportDensityTarget

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The canonical Mathlib Hilbert basis of the completed real `ℓ²(ℕ)` carrier,
constructed explicitly from the reflexive linear isometry equivalence.  We avoid
using `default` here because type-class search does not synthesize the
`Inhabited (HilbertBasis ...)` instance through the local carrier abbreviation in
CI. -/
def concreteL2R2CanonicalHilbertBasis :
    HilbertBasis ℕ ℝ ConcreteL2R1HilbertCarrier :=
  HilbertBasis.ofRepr
    (LinearIsometryEquiv.refl ℝ ConcreteL2R1HilbertCarrier)

/-- The inverse of the reflexive linear isometry equivalence is pointwise the
identity.  This local lemma keeps the R2b basis computation stable under the
Lean 4.30 / Mathlib CI simplifier. -/
theorem concrete_l2_r2_linear_isometry_equiv_refl_symm_apply
    (x : ConcreteL2R1HilbertCarrier) :
    (LinearIsometryEquiv.refl ℝ ConcreteL2R1HilbertCarrier).symm x = x := by
  simpa using
    ((LinearIsometryEquiv.refl ℝ ConcreteL2R1HilbertCarrier).apply_symm_apply x)

/-- The explicit canonical Mathlib Hilbert basis of the completed real `ℓ²(ℕ)`
carrier is exactly the concrete coordinate-unit family already used by the R2
finite seed lane.  This keeps the R2b density proof Mathlib-native: no
hand-rolled finite support completion argument is introduced here. -/
theorem concrete_l2_r2_canonical_hilbert_basis_eq_mathlib_unit
    (n : ℕ) :
    (concreteL2R2CanonicalHilbertBasis n) =
      (concreteL2MathlibUnit n : ConcreteL2R1HilbertCarrier) := by
  rw [← HilbertBasis.repr_symm_single concreteL2R2CanonicalHilbertBasis n]
  simpa [concreteL2R2CanonicalHilbertBasis, concreteL2MathlibUnit]
    using concrete_l2_r2_linear_isometry_equiv_refl_symm_apply
      (lp.single 2 n (1 : ℝ) : ConcreteL2R1HilbertCarrier)

/-- The range of the explicit canonical Mathlib Hilbert basis is the
coordinate-unit set used to define the R2 finite-coordinate submodule. -/
theorem concrete_l2_r2_canonical_hilbert_basis_range_eq_coordinate_unit_set :
    Set.range concreteL2R2CanonicalHilbertBasis =
      concreteL2R2CoordinateUnitSet := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, (concrete_l2_r2_canonical_hilbert_basis_eq_mathlib_unit n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, concrete_l2_r2_canonical_hilbert_basis_eq_mathlib_unit n⟩

/-- R2b core theorem: the Mathlib-native span of the coordinate units is dense in
the completed real `ℓ²(ℕ)` carrier.  This proves finite-support density in the
carrier only.  It is not yet a graph-norm core theorem, closed-operator theorem,
self-adjointness theorem, spectral theorem application, PVM construction, or
positive spectral weight statement. -/
theorem concrete_l2_r2_finite_coordinate_submodule_topologicalClosure_eq_top :
    concreteL2R2FiniteCoordinateSubmodule.topologicalClosure =
      (⊤ : Submodule ℝ ConcreteL2R1HilbertCarrier) := by
  classical
  let b : HilbertBasis ℕ ℝ ConcreteL2R1HilbertCarrier :=
    concreteL2R2CanonicalHilbertBasis
  have hb_dense :
      (Submodule.span ℝ (Set.range b)).topologicalClosure =
        (⊤ : Submodule ℝ ConcreteL2R1HilbertCarrier) := by
    exact HilbertBasis.dense_span b
  have hRange : Set.range b = concreteL2R2CoordinateUnitSet := by
    simpa [b] using concrete_l2_r2_canonical_hilbert_basis_range_eq_coordinate_unit_set
  simpa [concreteL2R2FiniteCoordinateSubmodule, hRange] using hb_dense

/-- Set-level closure form of the R2b carrier-density theorem. -/
theorem concrete_l2_r2_finite_coordinate_submodule_closure_target_eq_univ :
    concreteL2R2FiniteCoordinateSubmoduleClosureTarget =
      (Set.univ : Set ConcreteL2R1HilbertCarrier) := by
  have h := congrArg
    (fun S : Submodule ℝ ConcreteL2R1HilbertCarrier =>
      (S : Set ConcreteL2R1HilbertCarrier))
    concrete_l2_r2_finite_coordinate_submodule_topologicalClosure_eq_top
  simpa [concreteL2R2FiniteCoordinateSubmoduleClosureTarget,
    Submodule.topologicalClosure_coe] using h

/-- R2b target theorem: every vector of the completed Mathlib carrier lies in the
closure of the finite-coordinate submodule. -/
theorem concrete_l2_r2_finite_coordinate_submodule_dense_target_ready :
    concreteL2R2FiniteCoordinateSubmoduleDenseTarget := by
  intro x
  rw [concrete_l2_r2_finite_coordinate_submodule_closure_target_eq_univ]
  exact Set.mem_univ x

/-- Adapter predicate recording that R2b has closed the carrier-density target,
while still refusing every stronger operator/spectral promotion. -/
def concreteL2R2FiniteSupportDensityTheoremAdapter : Prop :=
  concreteL2R2FiniteCoordinateSubmoduleDenseTarget

/-- Adapter theorem for the R2b finite-support density theorem. -/
theorem concrete_l2_r2_finite_support_density_theorem_adapter_ready :
    concreteL2R2FiniteSupportDensityTheoremAdapter := by
  exact concrete_l2_r2_finite_coordinate_submodule_dense_target_ready

/-- R2b finite-support density theorem surface.  This is the first actual density
result in the Mathlib completed carrier, but it is deliberately restricted to
carrier density of the finite-coordinate span.  The dense diagonal-domain theorem
is left for the next handoff layer. -/
structure ConcreteL2R2FiniteSupportDensityTheoremSurface where
  densityTargetReady : concreteAnalyticSpineL2R2FiniteSupportDensityTargetSurfaceReady
  coordinateSubmoduleTopologicalClosureEqTop :
    concreteL2R2FiniteCoordinateSubmodule.topologicalClosure =
      (⊤ : Submodule ℝ ConcreteL2R1HilbertCarrier)
  closureTargetEqUniv :
    concreteL2R2FiniteCoordinateSubmoduleClosureTarget =
      (Set.univ : Set ConcreteL2R1HilbertCarrier)
  finiteSupportDenseInCarrier : concreteL2R2FiniteCoordinateSubmoduleDenseTarget
  boundaryNotDenseDiagonalDomainTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2b finite-support density theorem surface. -/
def concreteL2R2FiniteSupportDensityTheoremSurface :
    ConcreteL2R2FiniteSupportDensityTheoremSurface :=
  { densityTargetReady :=
      concrete_analytic_spine_l2_r2_finite_support_density_target_surface_ready
    coordinateSubmoduleTopologicalClosureEqTop :=
      concrete_l2_r2_finite_coordinate_submodule_topologicalClosure_eq_top
    closureTargetEqUniv :=
      concrete_l2_r2_finite_coordinate_submodule_closure_target_eq_univ
    finiteSupportDenseInCarrier :=
      concrete_l2_r2_finite_coordinate_submodule_dense_target_ready
    boundaryNotDenseDiagonalDomainTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2b finite-support density theorem readiness. -/
def concreteAnalyticSpineL2R2FiniteSupportDensityTheoremSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2FiniteSupportDensityTargetSurfaceReady ∧
  concreteL2R2FiniteSupportDensityTheoremAdapter ∧
  concreteL2R2FiniteSupportDensityTheoremSurface.boundaryNotDenseDiagonalDomainTheorem ∧
  concreteL2R2FiniteSupportDensityTheoremSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2FiniteSupportDensityTheoremSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2FiniteSupportDensityTheoremSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2FiniteSupportDensityTheoremSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2FiniteSupportDensityTheoremSurface.boundaryNotPVMConstruction ∧
  concreteL2R2FiniteSupportDensityTheoremSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for the R2b finite-support density theorem surface. -/
theorem concrete_analytic_spine_l2_r2_finite_support_density_theorem_surface_ready :
    concreteAnalyticSpineL2R2FiniteSupportDensityTheoremSurfaceReady := by
  unfold concreteAnalyticSpineL2R2FiniteSupportDensityTheoremSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_finite_support_density_target_surface_ready <|
      And.intro concrete_l2_r2_finite_support_density_theorem_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the R2b finite-support density theorem surface. -/
def concreteAnalyticSpineL2R2FiniteSupportDensityTheoremHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2FiniteSupportDensityTheoremSurfaceReady

/-- Boundary theorem for the R2b finite-support density theorem surface. -/
theorem concrete_analytic_spine_l2_r2_finite_support_density_theorem_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2FiniteSupportDensityTheoremHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_finite_support_density_theorem_surface_ready

end

end MathlibAnalytic
end MGAP4D
