import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FiniteSupportDensityTheorem

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The R2 diagonal-domain candidate as a set in the completed Mathlib carrier. -/
def concreteL2R2DiagonalDomainCandidateSet : Set ConcreteL2R1HilbertCarrier :=
  {x | ConcreteL2R2DiagonalDomainCandidate x}

/-- The topological closure target for the R2 diagonal-domain candidate set. -/
def concreteL2R2DiagonalDomainCandidateClosureTarget :
    Set ConcreteL2R1HilbertCarrier :=
  closure concreteL2R2DiagonalDomainCandidateSet

/-- R2c dense diagonal-domain candidate target, stated as membership of every
completed carrier vector in the closure of the diagonal-domain candidate set. -/
def concreteL2R2DiagonalDomainCandidateDenseTarget : Prop :=
  ∀ x : ConcreteL2R1HilbertCarrier,
    x ∈ concreteL2R2DiagonalDomainCandidateClosureTarget

/-- The remaining R2c inclusion obligation: the already-dense finite-coordinate
submodule must be shown to sit inside the diagonal-domain candidate set.  This
obligation is separated from the topological density transport so that no
operator/core/self-adjointness claim is bundled into this handoff. -/
def concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate : Prop :=
  (concreteL2R2FiniteCoordinateSubmodule : Set ConcreteL2R1HilbertCarrier) ⊆
    concreteL2R2DiagonalDomainCandidateSet

/-- If the finite-coordinate submodule is contained in the diagonal-domain
candidate set, then the R2b finite-support density theorem transports to density
of the diagonal-domain candidate set. -/
theorem concrete_l2_r2_diagonal_domain_candidate_closure_eq_univ_of_finite_coordinate_submodule_subset
    (hsubset : concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate) :
    concreteL2R2DiagonalDomainCandidateClosureTarget =
      (Set.univ : Set ConcreteL2R1HilbertCarrier) := by
  have hmono :
      closure ((concreteL2R2FiniteCoordinateSubmodule : Set ConcreteL2R1HilbertCarrier)) ⊆
        concreteL2R2DiagonalDomainCandidateClosureTarget := by
    exact closure_mono hsubset
  have hfinite :
      closure ((concreteL2R2FiniteCoordinateSubmodule : Set ConcreteL2R1HilbertCarrier)) =
        (Set.univ : Set ConcreteL2R1HilbertCarrier) := by
    simpa [concreteL2R2FiniteCoordinateSubmoduleClosureTarget] using
      concrete_l2_r2_finite_coordinate_submodule_closure_target_eq_univ
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  · intro x hx
    have hxfinite :
        x ∈ closure ((concreteL2R2FiniteCoordinateSubmodule : Set ConcreteL2R1HilbertCarrier)) := by
      rw [hfinite]
      exact Set.mem_univ x
    exact hmono hxfinite

/-- Conditional R2c dense target: once the finite-coordinate-submodule inclusion
obligation is supplied, every carrier vector belongs to the closure of the R2
diagonal-domain candidate set. -/
theorem concrete_l2_r2_diagonal_domain_candidate_dense_target_ready_of_finite_coordinate_submodule_subset
    (hsubset : concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate) :
    concreteL2R2DiagonalDomainCandidateDenseTarget := by
  intro x
  rw [concrete_l2_r2_diagonal_domain_candidate_closure_eq_univ_of_finite_coordinate_submodule_subset hsubset]
  exact Set.mem_univ x

/-- R2c handoff adapter.  This records the exact topological transport law from
R2b finite-support density to dense diagonal-domain-candidate readiness, while
leaving the finite-coordinate-submodule inclusion as the next explicit proof
obligation. -/
def concreteL2R2DenseDiagonalDomainCandidateHandoffAdapter : Prop :=
  concreteL2R2FiniteCoordinateSubmoduleDenseTarget ∧
  (concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate →
    concreteL2R2DiagonalDomainCandidateDenseTarget)

/-- Adapter theorem for the R2c conditional dense-domain-candidate handoff. -/
theorem concrete_l2_r2_dense_diagonal_domain_candidate_handoff_adapter_ready :
    concreteL2R2DenseDiagonalDomainCandidateHandoffAdapter := by
  exact And.intro
    concrete_l2_r2_finite_coordinate_submodule_dense_target_ready
    concrete_l2_r2_diagonal_domain_candidate_dense_target_ready_of_finite_coordinate_submodule_subset

/-- R2c dense diagonal-domain-candidate handoff surface.  This is a conditional
handoff surface, not an operator surface.  It proves that the topology is ready:
finite-support density already suffices to make the diagonal-domain candidate
dense once the finite-coordinate-submodule inclusion is closed. -/
structure ConcreteL2R2DenseDiagonalDomainCandidateHandoffSurface where
  finiteSupportDensityReady : concreteAnalyticSpineL2R2FiniteSupportDensityTheoremSurfaceReady
  domainCandidateSet : Set ConcreteL2R1HilbertCarrier
  domainCandidateClosureTarget : Set ConcreteL2R1HilbertCarrier
  finiteCoordinateSubmoduleDense : concreteL2R2FiniteCoordinateSubmoduleDenseTarget
  inclusionObligation : Prop
  conditionalDenseDomainCandidateLaw :
    inclusionObligation → concreteL2R2DiagonalDomainCandidateDenseTarget
  boundaryNotUnconditionalDenseDomainTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2c dense diagonal-domain-candidate handoff surface. -/
def concreteL2R2DenseDiagonalDomainCandidateHandoffSurface :
    ConcreteL2R2DenseDiagonalDomainCandidateHandoffSurface :=
  { finiteSupportDensityReady :=
      concrete_analytic_spine_l2_r2_finite_support_density_theorem_surface_ready
    domainCandidateSet := concreteL2R2DiagonalDomainCandidateSet
    domainCandidateClosureTarget := concreteL2R2DiagonalDomainCandidateClosureTarget
    finiteCoordinateSubmoduleDense :=
      concrete_l2_r2_finite_coordinate_submodule_dense_target_ready
    inclusionObligation :=
      concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate
    conditionalDenseDomainCandidateLaw :=
      concrete_l2_r2_diagonal_domain_candidate_dense_target_ready_of_finite_coordinate_submodule_subset
    boundaryNotUnconditionalDenseDomainTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2c handoff readiness.  This closes only the conditional density transport;
the unconditional dense-domain theorem remains blocked until the inclusion
obligation is separately proved. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoffSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2FiniteSupportDensityTheoremSurfaceReady ∧
  concreteL2R2DenseDiagonalDomainCandidateHandoffAdapter ∧
  concreteL2R2DenseDiagonalDomainCandidateHandoffSurface.boundaryNotUnconditionalDenseDomainTheorem ∧
  concreteL2R2DenseDiagonalDomainCandidateHandoffSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2DenseDiagonalDomainCandidateHandoffSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DenseDiagonalDomainCandidateHandoffSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2DenseDiagonalDomainCandidateHandoffSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2DenseDiagonalDomainCandidateHandoffSurface.boundaryNotPVMConstruction ∧
  concreteL2R2DenseDiagonalDomainCandidateHandoffSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for the R2c conditional dense diagonal-domain-candidate
handoff surface. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_candidate_handoff_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoffSurfaceReady := by
  unfold concreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoffSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_finite_support_density_theorem_surface_ready <|
      And.intro concrete_l2_r2_dense_diagonal_domain_candidate_handoff_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the R2c dense diagonal-domain-candidate handoff surface. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoffHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoffSurfaceReady

/-- Boundary theorem for the R2c dense diagonal-domain-candidate handoff surface. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_candidate_handoff_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoffHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_candidate_handoff_surface_ready

end

end MathlibAnalytic
end MGAP4D
