import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphReverse

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Every element of the concrete real `ℓ²(ℕ)` Hilbert carrier has square-summable
coordinates. -/
theorem concrete_l2_r2_hilbert_carrier_square_summable
    (y : ConcreteL2R1HilbertCarrier) :
    Summable fun n : ℕ => (y n) ^ 2 := by
  have hnorm :
      Summable fun n : ℕ => ‖y n‖ ^ (2 : ℝ≥0∞).toReal := by
    exact Memℓp.summable (by norm_num) y.2
  simpa [Real.norm_eq_abs, sq_abs] using hnorm

/-- If a pair belongs to the completed diagonal graph carrier, then its input is
in the diagonal-domain candidate: the output is already an `ℓ²` vector and is
coordinatewise the weighted input. -/
theorem concrete_l2_r2_completed_graph_input_mem_diagonal_domain_candidate
    (p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)
    (hp : p ∈ concreteL2R2CompletedDiagonalGraphCarrier) :
    ConcreteL2R2DiagonalDomainCandidate p.1 := by
  unfold ConcreteL2R2DiagonalDomainCandidate
  have hy : Summable fun n : ℕ => (p.2 n) ^ 2 :=
    concrete_l2_r2_hilbert_carrier_square_summable p.2
  exact hy.congr fun n => by
    rw [hp n]
    rfl

/-- The input of every completed diagonal graph point belongs to the promoted
submodule domain. -/
theorem concrete_l2_r2_completed_graph_input_mem_diagonal_domain_candidate_submodule
    (p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)
    (hp : p ∈ concreteL2R2CompletedDiagonalGraphCarrier) :
    p.1 ∈ (concreteL2R2DiagonalDomainCandidateSubmodule : Set ConcreteL2R1HilbertCarrier) := by
  rw [concrete_l2_r2_diagonal_domain_candidate_submodule_carrier_eq]
  exact concrete_l2_r2_completed_graph_input_mem_diagonal_domain_candidate p hp

/-- The unrestricted completed diagonal graph carrier is contained in its own
restriction to the promoted dense-domain submodule. -/
theorem concrete_l2_r2_completed_graph_subset_restricted_to_dense_domain :
    concreteL2R2CompletedDiagonalGraphCarrier ⊆
      concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain := by
  intro p hp
  exact ⟨hp, concrete_l2_r2_completed_graph_input_mem_diagonal_domain_candidate_submodule p hp⟩

/-- The dense-domain restriction is definitionally contained in the unrestricted
completed diagonal graph carrier. -/
theorem concrete_l2_r2_restricted_to_dense_domain_subset_completed_graph :
    concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain ⊆
      concreteL2R2CompletedDiagonalGraphCarrier := by
  intro p hp
  exact hp.1

/-- The promoted dense-domain restriction is actually the full completed diagonal
graph carrier.  The key reason is that any graph output is an `ℓ²` vector, hence
the weighted input is automatically square-summable. -/
theorem concrete_l2_r2_completed_graph_eq_restricted_to_dense_domain :
    concreteL2R2CompletedDiagonalGraphCarrier =
      concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain := by
  apply Set.Subset.antisymm
  · exact concrete_l2_r2_completed_graph_subset_restricted_to_dense_domain
  · exact concrete_l2_r2_restricted_to_dense_domain_subset_completed_graph

/-- The bundled dense-domain linear-map graph is the full completed diagonal graph
carrier. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier :
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
      concreteL2R2CompletedDiagonalGraphCarrier := by
  calc
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier
        = concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain :=
          concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_restricted_completed_graph
    _ = concreteL2R2CompletedDiagonalGraphCarrier := by
          exact concrete_l2_r2_completed_graph_eq_restricted_to_dense_domain.symm

/-- Unrestricted dense-domain linear-map graph equality surface. -/
structure ConcreteL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedSurface where
  restrictedReverseReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphReverseSurfaceReady
  completedGraphInputMemDomainCandidate :
    ∀ p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier,
      p ∈ concreteL2R2CompletedDiagonalGraphCarrier →
        ConcreteL2R2DiagonalDomainCandidate p.1
  completedGraphEqRestricted :
    concreteL2R2CompletedDiagonalGraphCarrier =
      concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain
  linearMapGraphEqCompletedGraph :
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
      concreteL2R2CompletedDiagonalGraphCarrier
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotAdjointGraphTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete unrestricted dense-domain linear-map graph equality surface. -/
def concreteL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedSurface :
    ConcreteL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedSurface :=
  { restrictedReverseReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_reverse_surface_ready
    completedGraphInputMemDomainCandidate :=
      concrete_l2_r2_completed_graph_input_mem_diagonal_domain_candidate
    completedGraphEqRestricted :=
      concrete_l2_r2_completed_graph_eq_restricted_to_dense_domain
    linearMapGraphEqCompletedGraph :=
      concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier
    boundaryNotClosedOperatorTheorem := True
    boundaryNotAdjointGraphTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for unrestricted dense-domain linear-map graph equality. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphReverseSurfaceReady ∧
  (∀ p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier,
    p ∈ concreteL2R2CompletedDiagonalGraphCarrier →
      ConcreteL2R2DiagonalDomainCandidate p.1) ∧
  concreteL2R2CompletedDiagonalGraphCarrier =
    concreteL2R2CompletedDiagonalGraphCarrierRestrictedToDenseDomain ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
    concreteL2R2CompletedDiagonalGraphCarrier ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedSurface.boundaryNotAdjointGraphTheorem ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedSurface.boundaryNotSelfAdjointness

/-- The unrestricted dense-domain linear-map graph equality surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_unrestricted_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_reverse_surface_ready,
    concrete_l2_r2_completed_graph_input_mem_diagonal_domain_candidate,
    concrete_l2_r2_completed_graph_eq_restricted_to_dense_domain,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker: the bundled dense-domain linear-map graph is now identical
to the existing completed graph carrier.  Closedness, adjoint graph comparison,
and self-adjointness remain separate theorem layers. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedSurfaceReady

/-- Boundary theorem for unrestricted dense-domain linear-map graph equality. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_unrestricted_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_unrestricted_surface_ready

end

end MathlibAnalytic
end MGAP4D
