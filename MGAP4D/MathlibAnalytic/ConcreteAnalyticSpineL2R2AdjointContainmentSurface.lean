import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2SymmetricOperatorSurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Formal adjoint graph candidate for the completed diagonal graph-defined
operator.

A pair `(y, w)` belongs to this candidate when it satisfies the adjoint testing
identity against every graph point `(z, Tz)` of the original graph:
`⟪w, z⟫ = ⟪y, Tz⟫`.  This is not yet the full Mathlib adjoint operator; it is the
correct graph-form obligation that must be compared with the original graph in
the adjoint-domain-agreement lane. -/
def concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate :
    Set ((lp (fun _ : ℕ => ℝ) 2) × (lp (fun _ : ℕ => ℝ) 2)) :=
  {p | ∀ {z Tz : lp (fun _ : ℕ => ℝ) 2},
    (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    inner ℝ p.2 z = inner ℝ p.1 Tz}

/-- Graph containment into the formal adjoint graph candidate.

This is the graph-theoretic form of `T ⊆ T*`: every graph point of the completed
diagonal operator satisfies the adjoint testing identity against every graph point
of the original operator.  The proof is exactly the already-established graph
symmetry theorem. -/
theorem concrete_l2_r2_completed_diagonal_graph_subset_formal_adjoint_candidate :
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ⊆
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  intro p hp
  rcases p with ⟨x, Tx⟩
  intro z Tz hzgraph
  exact concrete_l2_r2_completed_diagonal_graph_symmetric hp hzgraph

/-- Formal adjoint containment predicate for the completed diagonal graph-defined
operator. -/
def concreteL2R2CompletedDiagonalFormalAdjointContainment : Prop :=
  concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ⊆
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate

/-- The completed diagonal graph is contained in its formal adjoint graph
candidate. -/
theorem concrete_l2_r2_completed_diagonal_formal_adjoint_containment :
    concreteL2R2CompletedDiagonalFormalAdjointContainment := by
  exact concrete_l2_r2_completed_diagonal_graph_subset_formal_adjoint_candidate

/-- Adjoint containment surface.

This upgrades symmetry to the formal adjoint-containment side of the
self-adjointness lane.  It still does not claim reverse containment, full adjoint
domain agreement, resolvent/deficiency control, essential self-adjointness,
self-adjointness, spectral theorem, PVM, or positive spectral weight. -/
structure ConcreteL2R2AdjointContainmentSurface where
  symmetricOperatorSurfaceReady : concreteAnalyticSpineL2R2SymmetricOperatorSurfaceReady
  formalAdjointContainment : concreteL2R2CompletedDiagonalFormalAdjointContainment
  boundaryNotReverseAdjointContainment : Prop
  boundaryNotAdjointDomainAgreementTheorem : Prop
  boundaryNotResolventOrDeficiencyTheorem : Prop
  boundaryNotEssentialSelfAdjointnessTheorem : Prop
  boundaryNotSelfAdjointnessTheorem : Prop
  boundaryNotSpectralTheorem : Prop
  boundaryNotPVM : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete adjoint-containment surface for the completed diagonal lane. -/
def concreteL2R2AdjointContainmentSurface :
    ConcreteL2R2AdjointContainmentSurface :=
  { symmetricOperatorSurfaceReady :=
      concrete_analytic_spine_l2_r2_symmetric_operator_surface_ready
    formalAdjointContainment :=
      concrete_l2_r2_completed_diagonal_formal_adjoint_containment
    boundaryNotReverseAdjointContainment := True
    boundaryNotAdjointDomainAgreementTheorem := True
    boundaryNotResolventOrDeficiencyTheorem := True
    boundaryNotEssentialSelfAdjointnessTheorem := True
    boundaryNotSelfAdjointnessTheorem := True
    boundaryNotSpectralTheorem := True
    boundaryNotPVM := True
    boundaryNotPositiveSpectralWeight := True }

/-- Public theorem-entry predicate for the adjoint-containment surface. -/
def concreteAnalyticSpineL2R2AdjointContainmentSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2SymmetricOperatorSurfaceReady ∧
  concreteL2R2CompletedDiagonalFormalAdjointContainment ∧
  True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True

/-- The adjoint-containment surface is ready. -/
theorem concrete_analytic_spine_l2_r2_adjoint_containment_surface_ready :
    concreteAnalyticSpineL2R2AdjointContainmentSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_symmetric_operator_surface_ready,
    concrete_l2_r2_completed_diagonal_formal_adjoint_containment,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
