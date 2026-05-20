import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusion

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Elementary real comparison used by the R2e additive-closure proof. -/
theorem concrete_l2_r2_sq_add_le_two_sq_add_two_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ (2 : ℝ) * a ^ 2 + (2 : ℝ) * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Weighted coordinates are additive on the completed real `ℓ²(ℕ)` carrier. -/
theorem concrete_l2_r2_weighted_coordinate_add
    (x y : ConcreteL2R1HilbertCarrier) (n : ℕ) :
    concreteL2R2WeightedCoordinate (x + y) n =
      concreteL2R2WeightedCoordinate x n +
        concreteL2R2WeightedCoordinate y n := by
  simp [concreteL2R2WeightedCoordinate, lp.coeFn_add, mul_add]

/-- R2e core theorem: the R2 diagonal-domain candidate is additively closed.
This closes the remaining target introduced in R2d using the standard comparison
`(a + b)^2 ≤ 2a^2 + 2b^2` and summability comparison for nonnegative real
series. -/
theorem concrete_l2_r2_diagonal_domain_candidate_add :
    concreteL2R2DiagonalDomainCandidateAddClosureTarget := by
  intro x y hx hy
  unfold ConcreteL2R2DiagonalDomainCandidate at hx hy ⊢
  have hsumBound :
      Summable fun n : ℕ =>
        (2 : ℝ) • ((concreteL2R2WeightedCoordinate x n) ^ 2) +
          (2 : ℝ) • ((concreteL2R2WeightedCoordinate y n) ^ 2) := by
    exact (hx.const_smul (2 : ℝ)).add (hy.const_smul (2 : ℝ))
  refine Summable.of_nonneg_of_le ?hNonneg ?hLe hsumBound
  · intro n
    exact sq_nonneg (concreteL2R2WeightedCoordinate (x + y) n)
  · intro n
    rw [concrete_l2_r2_weighted_coordinate_add]
    simpa [two_smul] using
      concrete_l2_r2_sq_add_le_two_sq_add_two_sq
        (concreteL2R2WeightedCoordinate x n)
        (concreteL2R2WeightedCoordinate y n)

/-- R2e closes the finite-coordinate-submodule inclusion obligation introduced in
R2c/R2d. -/
theorem concrete_l2_r2_finite_coordinate_submodule_subset_diagonal_domain_candidate :
    concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate := by
  exact
    concrete_l2_r2_finite_coordinate_submodule_subset_diagonal_domain_candidate_of_add_closure
      concrete_l2_r2_diagonal_domain_candidate_add

/-- R2e dense diagonal-domain-candidate theorem.  This is density of the
candidate set in the Mathlib completed carrier.  It is still not a graph-norm
core theorem, closed-operator theorem, self-adjointness theorem, spectral theorem
application, PVM construction, or positive spectral-weight theorem. -/
theorem concrete_l2_r2_diagonal_domain_candidate_dense_target_ready :
    concreteL2R2DiagonalDomainCandidateDenseTarget := by
  exact
    concrete_l2_r2_diagonal_domain_candidate_dense_target_ready_of_add_closure
      concrete_l2_r2_diagonal_domain_candidate_add

/-- Set-level closure form of the R2e dense diagonal-domain-candidate theorem. -/
theorem concrete_l2_r2_diagonal_domain_candidate_closure_eq_univ :
    concreteL2R2DiagonalDomainCandidateClosureTarget =
      (Set.univ : Set ConcreteL2R1HilbertCarrier) := by
  exact
    concrete_l2_r2_diagonal_domain_candidate_closure_eq_univ_of_finite_coordinate_submodule_subset
      concrete_l2_r2_finite_coordinate_submodule_subset_diagonal_domain_candidate

/-- R2e adapter: additive closure is now proved, and the dense candidate target is
unconditional at the candidate-set level. -/
def concreteL2R2DiagonalDomainAdditiveClosureAdapter : Prop :=
  concreteL2R2DiagonalDomainCandidateAddClosureTarget ∧
  concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate ∧
  concreteL2R2DiagonalDomainCandidateDenseTarget

/-- Adapter theorem for R2e. -/
theorem concrete_l2_r2_diagonal_domain_additive_closure_adapter_ready :
    concreteL2R2DiagonalDomainAdditiveClosureAdapter := by
  exact And.intro
    concrete_l2_r2_diagonal_domain_candidate_add <|
      And.intro
        concrete_l2_r2_finite_coordinate_submodule_subset_diagonal_domain_candidate
        concrete_l2_r2_diagonal_domain_candidate_dense_target_ready

/-- R2e surface.  This closes additive closure and carrier-density of the
candidate domain, while still explicitly blocking all operator/spectral
promotions. -/
structure ConcreteL2R2DiagonalDomainAdditiveClosureSurface where
  r2dReady : concreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusionSurfaceReady
  additiveClosureReady : concreteL2R2DiagonalDomainCandidateAddClosureTarget
  finiteCoordinateSubmoduleInclusionReady :
    concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate
  denseCandidateReady : concreteL2R2DiagonalDomainCandidateDenseTarget
  candidateClosureEqUniv :
    concreteL2R2DiagonalDomainCandidateClosureTarget =
      (Set.univ : Set ConcreteL2R1HilbertCarrier)
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2e surface. -/
def concreteL2R2DiagonalDomainAdditiveClosureSurface :
    ConcreteL2R2DiagonalDomainAdditiveClosureSurface :=
  { r2dReady :=
      concrete_analytic_spine_l2_r2_finite_coordinate_submodule_domain_inclusion_surface_ready
    additiveClosureReady := concrete_l2_r2_diagonal_domain_candidate_add
    finiteCoordinateSubmoduleInclusionReady :=
      concrete_l2_r2_finite_coordinate_submodule_subset_diagonal_domain_candidate
    denseCandidateReady :=
      concrete_l2_r2_diagonal_domain_candidate_dense_target_ready
    candidateClosureEqUniv :=
      concrete_l2_r2_diagonal_domain_candidate_closure_eq_univ
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2e additive-closure readiness. -/
def concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusionSurfaceReady ∧
  concreteL2R2DiagonalDomainAdditiveClosureAdapter ∧
  concreteL2R2DiagonalDomainAdditiveClosureSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2DiagonalDomainAdditiveClosureSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DiagonalDomainAdditiveClosureSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2DiagonalDomainAdditiveClosureSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2DiagonalDomainAdditiveClosureSurface.boundaryNotPVMConstruction ∧
  concreteL2R2DiagonalDomainAdditiveClosureSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2e. -/
theorem concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_surface_ready :
    concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureSurfaceReady := by
  unfold concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_finite_coordinate_submodule_domain_inclusion_surface_ready <|
      And.intro concrete_l2_r2_diagonal_domain_additive_closure_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the R2e additive-closure surface. -/
def concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureSurfaceReady

/-- Boundary theorem for the R2e additive-closure surface. -/
theorem concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_surface_ready

end

end MathlibAnalytic
end MGAP4D
