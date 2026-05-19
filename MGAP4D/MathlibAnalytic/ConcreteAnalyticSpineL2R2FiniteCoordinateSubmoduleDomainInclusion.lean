import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoff

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- R2 domain-candidate scalar closure.  This closes the easy linear half of the
finite-coordinate-submodule inclusion proof: weighted square summability is
preserved by scalar multiplication. -/
theorem concrete_l2_r2_diagonal_domain_candidate_smul
    (c : ℝ) {x : ConcreteL2R1HilbertCarrier}
    (hx : ConcreteL2R2DiagonalDomainCandidate x) :
    ConcreteL2R2DiagonalDomainCandidate (c • x) := by
  unfold ConcreteL2R2DiagonalDomainCandidate at hx ⊢
  have hseq :
      (fun n : ℕ =>
        (concreteL2R2WeightedCoordinate (c • x) n) ^ 2) =
      (fun n : ℕ =>
        (c ^ 2) • ((concreteL2R2WeightedCoordinate x n) ^ 2)) := by
    funext n
    simp [concreteL2R2WeightedCoordinate, lp.coeFn_smul, pow_two]
    ring
  rw [hseq]
  exact hx.const_smul (c ^ 2)

/-- The remaining analytic closure target for the R2 diagonal-domain candidate:
additive closure of weighted-square summability.  This is intentionally separated
from scalar closure so the next PR can focus only on the comparison estimate for
`(a + b)^2`. -/
def concreteL2R2DiagonalDomainCandidateAddClosureTarget : Prop :=
  ∀ x y : ConcreteL2R1HilbertCarrier,
    ConcreteL2R2DiagonalDomainCandidate x →
    ConcreteL2R2DiagonalDomainCandidate y →
    ConcreteL2R2DiagonalDomainCandidate (x + y)

/-- Conditional R2d inclusion theorem: once additive closure of the diagonal-domain
candidate is supplied, `span_induction` upgrades coordinate-unit domain membership
to inclusion of the whole finite-coordinate submodule. -/
theorem concrete_l2_r2_finite_coordinate_submodule_subset_diagonal_domain_candidate_of_add_closure
    (hadd : concreteL2R2DiagonalDomainCandidateAddClosureTarget) :
    concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate := by
  intro x hx
  change ConcreteL2R2DiagonalDomainCandidate x
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨k, rfl⟩
      exact concrete_l2_r2_diagonal_domain_candidate_mathlib_unit k
  | zero =>
      exact concrete_l2_r2_diagonal_domain_candidate_zero
  | add u v _hu _hv huDomain hvDomain =>
      exact hadd u v huDomain hvDomain
  | smul c u _hu huDomain =>
      exact concrete_l2_r2_diagonal_domain_candidate_smul c huDomain

/-- Conditional R2d dense-domain theorem: additive closure closes the finite
coordinate submodule inclusion, and R2c then transports R2b density to the
diagonal-domain candidate set.  This still does not construct an operator. -/
theorem concrete_l2_r2_diagonal_domain_candidate_dense_target_ready_of_add_closure
    (hadd : concreteL2R2DiagonalDomainCandidateAddClosureTarget) :
    concreteL2R2DiagonalDomainCandidateDenseTarget := by
  exact
    concrete_l2_r2_diagonal_domain_candidate_dense_target_ready_of_finite_coordinate_submodule_subset
      (concrete_l2_r2_finite_coordinate_submodule_subset_diagonal_domain_candidate_of_add_closure hadd)

/-- R2d adapter: scalar closure is proved, additive closure remains the single
explicit analytic target, and the finite-coordinate-submodule inclusion follows
conditionally from it. -/
def concreteL2R2FiniteCoordinateSubmoduleDomainInclusionAdapter : Prop :=
  (∀ (c : ℝ) {x : ConcreteL2R1HilbertCarrier},
      ConcreteL2R2DiagonalDomainCandidate x →
      ConcreteL2R2DiagonalDomainCandidate (c • x)) ∧
  (concreteL2R2DiagonalDomainCandidateAddClosureTarget →
    concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate) ∧
  (concreteL2R2DiagonalDomainCandidateAddClosureTarget →
    concreteL2R2DiagonalDomainCandidateDenseTarget)

/-- Adapter theorem for the R2d finite-coordinate-submodule domain-inclusion
handoff. -/
theorem concrete_l2_r2_finite_coordinate_submodule_domain_inclusion_adapter_ready :
    concreteL2R2FiniteCoordinateSubmoduleDomainInclusionAdapter := by
  exact And.intro
    (fun c x hx => concrete_l2_r2_diagonal_domain_candidate_smul c hx) <|
      And.intro
        concrete_l2_r2_finite_coordinate_submodule_subset_diagonal_domain_candidate_of_add_closure
        concrete_l2_r2_diagonal_domain_candidate_dense_target_ready_of_add_closure

/-- R2d finite-coordinate-submodule domain-inclusion surface.  It reduces the
remaining inclusion obligation to a single additive-closure estimate while
preserving all operator and spectral boundaries. -/
structure ConcreteL2R2FiniteCoordinateSubmoduleDomainInclusionSurface where
  denseHandoffReady : concreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoffSurfaceReady
  scalarClosureReady :
    ∀ (c : ℝ) {x : ConcreteL2R1HilbertCarrier},
      ConcreteL2R2DiagonalDomainCandidate x →
      ConcreteL2R2DiagonalDomainCandidate (c • x)
  additiveClosureTarget : Prop
  conditionalSubmoduleInclusion :
    additiveClosureTarget → concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate
  conditionalDenseDomainCandidate :
    additiveClosureTarget → concreteL2R2DiagonalDomainCandidateDenseTarget
  boundaryNotAdditiveClosureProved : Prop
  boundaryNotUnconditionalDenseDomainTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2d finite-coordinate-submodule domain-inclusion surface. -/
def concreteL2R2FiniteCoordinateSubmoduleDomainInclusionSurface :
    ConcreteL2R2FiniteCoordinateSubmoduleDomainInclusionSurface :=
  { denseHandoffReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_candidate_handoff_surface_ready
    scalarClosureReady :=
      fun c x hx => concrete_l2_r2_diagonal_domain_candidate_smul c hx
    additiveClosureTarget := concreteL2R2DiagonalDomainCandidateAddClosureTarget
    conditionalSubmoduleInclusion :=
      concrete_l2_r2_finite_coordinate_submodule_subset_diagonal_domain_candidate_of_add_closure
    conditionalDenseDomainCandidate :=
      concrete_l2_r2_diagonal_domain_candidate_dense_target_ready_of_add_closure
    boundaryNotAdditiveClosureProved := True
    boundaryNotUnconditionalDenseDomainTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2d finite-coordinate-submodule domain-inclusion readiness. -/
def concreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusionSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoffSurfaceReady ∧
  concreteL2R2FiniteCoordinateSubmoduleDomainInclusionAdapter ∧
  concreteL2R2FiniteCoordinateSubmoduleDomainInclusionSurface.boundaryNotAdditiveClosureProved ∧
  concreteL2R2FiniteCoordinateSubmoduleDomainInclusionSurface.boundaryNotUnconditionalDenseDomainTheorem ∧
  concreteL2R2FiniteCoordinateSubmoduleDomainInclusionSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2FiniteCoordinateSubmoduleDomainInclusionSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2FiniteCoordinateSubmoduleDomainInclusionSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2FiniteCoordinateSubmoduleDomainInclusionSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2FiniteCoordinateSubmoduleDomainInclusionSurface.boundaryNotPVMConstruction ∧
  concreteL2R2FiniteCoordinateSubmoduleDomainInclusionSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for the R2d finite-coordinate-submodule domain-inclusion
handoff surface. -/
theorem concrete_analytic_spine_l2_r2_finite_coordinate_submodule_domain_inclusion_surface_ready :
    concreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusionSurfaceReady := by
  unfold concreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusionSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_candidate_handoff_surface_ready <|
      And.intro concrete_l2_r2_finite_coordinate_submodule_domain_inclusion_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial trivial

/-- Boundary marker for the R2d finite-coordinate-submodule domain-inclusion
surface. -/
def concreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusionHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusionSurfaceReady

/-- Boundary theorem for the R2d finite-coordinate-submodule domain-inclusion
surface. -/
theorem concrete_analytic_spine_l2_r2_finite_coordinate_submodule_domain_inclusion_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusionHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_finite_coordinate_submodule_domain_inclusion_surface_ready

end

end MathlibAnalytic
end MGAP4D
